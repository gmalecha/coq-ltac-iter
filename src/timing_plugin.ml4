(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

module Section = struct
  let current () = Unix.gettimeofday ();;

  module Timer = struct 

    type t =
	{
	  stack : float Stack.t ; 
	  mutable total : float;
	  mutable number : int; 
	  mutable mean : float;
	  mutable m2 : float
	}
	  
	  
    (** operations on timers *)
    let start (r : t) = 
      Stack.push (current ()) r.stack
	  	  
    let stop (r : t) = 
      try 
	let t = Stack.pop r.stack in 
	let x = current () -. t in 
	r.total <- r.total +. x; 
	r.number <- r.number + 1; 
	let delta = x -. r.mean in 
	r.mean <- r.mean +. (delta /. float r.number); 
	r.m2 <- r.m2 +. delta *. ( x -. r.mean)
      with 
	| Stack.Empty -> () 			(* warning *)
	 
    let zero () =
      {stack = Stack.create (); total = 0. ; number = 0; mean = 0.; m2 = 0.}
  end
    
  let state = Hashtbl.create 17;;

  (** operations on the mutable global state  *)	  

  type key = string 
  let print_key fmt k = Format.fprintf fmt "%10s" k
  (** [run n] starts the timer [n], and create it if needed *)
  let start (n: key) =
    let r = 
      try Hashtbl.find state n 
      with 
	| Not_found -> 
	  let r =  Timer.zero () in 
	  Hashtbl.add state n r;
	  r
    in
    Timer.start r

  (** [stop n] stop the timer [n] *)
  let stop (n : key) = 
    try 
      let r = Hashtbl.find state n in 
      Timer.stop r
    with 
      | Not_found -> ()
	
  (** [reset n] sets back a given timer to zero *)
  let reset (n : key) = 
    Hashtbl.replace state n (Timer.zero ())

  (** [clear] reset all timers *)
  let clear () =
    Hashtbl.clear state

  let print fmt () =
    let elements = Hashtbl.fold (fun key elt acc -> (key, elt) :: acc) state [] in
    let elements = List.sort (Pervasives.compare) elements in 
    List.iter
      (fun (key,timer) -> 
	if timer.Timer.number <> 0 
	then 
	  begin 
	    Format.fprintf fmt "%a:\t(total:%f, mean:%f, runs:%i, sigma2:%f)\n" 
	      print_key key 
	      timer.Timer.total
	      timer.Timer.mean
	      timer.Timer.number
	      (timer.Timer.m2 /. (float timer.Timer.number))	  
	  end;
	  )
      elements
end  
  
let _=Mltop.add_known_module "Timing_plugin"

let pp_print () =
  let buf = Buffer.create 4 in 
  let fmt = Format.formatter_of_buffer buf in 
  let _ = (Format.fprintf fmt "%a\n%!" Section.print ()) in 
  (Buffer.contents buf)

let _ = Pp.msgnl (Pp.str "Loading the Timing Profiler")

open Tacexpr
open Tacinterp

TACTIC EXTEND start_timer
  | ["start_timer" string(n)] -> 
    [
      fun gl -> 
	Section.start n; 
	Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND stop_timer
  | ["stop_timer" string(n)] -> 
    [fun gl -> 
      Section.stop n;
      Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND reset_timer
  | ["reset_timer" string(n)] -> 
    [fun gl -> Section.reset n; Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND print_current_time
  | ["print_current_time"] -> 
    [fun gl -> Pp.msgnl (Pp.str (Format.sprintf "Current time: %f\n%!" (Section.current()))); Tacticals.tclIDTAC gl]
END;;


TACTIC EXTEND time_tactic
  | ["time" string(n) tactic(t)] -> 
    [
      let tac =  Tacinterp.eval_tactic t in 
      fun gl -> 
	Section.start n;
	let res = tac gl in 
	Section.stop n; res
    ]
END;;

VERNAC COMMAND EXTEND PrintTimingProfile
 ["Print" "Timing" "Profile"] ->
   [ Pp.msgnl (Pp.str (pp_print ())) ]
END;;

VERNAC COMMAND EXTEND ClearTimingProfile
 ["Clear" "Timing" "Profile"] ->
   [ Section.clear () ]
END;;

