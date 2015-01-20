module WITH_DB =
struct

  let ltac_lcall tac args =
    Tacexpr.TacArg(Util.dummy_loc,Tacexpr.TacCall(Util.dummy_loc, Glob_term.ArgVar(Util.dummy_loc, Names.id_of_string tac),args))

  let ltac_letin (x, e1) e2 =
    Tacexpr.TacLetIn(false,[(Util.dummy_loc,Names.id_of_string x),e1],e2)

  let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) =
    Tacinterp.eval_tactic
      (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args))

  let to_ltac_val c = Tacexpr.TacDynamic(Util.dummy_loc,Pretyping.constr_in c)

  let the_tactic dbs tacK =
    let syms = ref [] in
    let _ =
      List.iter (fun l ->
		 let db = Auto.searchtable_map l in
		 Auto.Hint_db.iter (fun _ hintlist ->
				    syms := hintlist::!syms) db) dbs in
    List.fold_left
      (fun tac hints ->
       List.fold_left
	 (fun tac hint ->
	  match hint.Auto.code with
	    Auto.Give_exact lem
	  | Auto.Res_pf (lem,_)
	  | Auto.ERes_pf (lem,_) ->
	     let this_tac : Proof_type.tactic =
	       ltac_apply tacK [to_ltac_val lem] in
	     Tacticals.tclORELSE this_tac tac
	  | _ -> tac)
	 tac hints)
      Tacticals.tclIDTAC !syms

end

TACTIC EXTEND reset_timer
  | [ "foreach" "[" ne_preident_list(l) "]" "run" tactic(k) ]  ->
    [ fun gl -> WITH_DB.the_tactic l k gl ]
END;;
