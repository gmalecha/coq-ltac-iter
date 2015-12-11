(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "with_hint_db_plugin"

module WITH_DB =
struct

  let ltac_lcall tac args =
    Tacexpr.TacArg(Loc.dummy_loc,
                   Tacexpr.TacCall(Loc.dummy_loc,
                                   Misctypes.ArgVar(Loc.dummy_loc,
                                                    Names.id_of_string tac),
                                   args))

  let ltac_letin (x, e1) e2 =
    Tacexpr.TacLetIn(false,[(Loc.dummy_loc,Names.id_of_string x),e1],e2)

  let ltac_apply (f:Tacexpr.glob_tactic_expr)
      (args:Tacexpr.glob_tactic_arg list) =
    Tacinterp.eval_tactic
      (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args))

  let to_ltac_val c = Tacexpr.TacDynamic(Loc.dummy_loc,Pretyping.constr_in c)

  let add_runner combiner else_tac tacK h =
    match h with
      Hints.Give_exact ((lem, _, _), _)
    | Hints.Res_pf ((lem, _, _), _)
    | Hints.ERes_pf ((lem, _, _), _) ->
      let this_tac =
        ltac_apply tacK [to_ltac_val lem] in
      combiner this_tac else_tac
    | _ -> else_tac

  let the_tactic combiner dbs tacK =
    let syms = ref [] in
    let _ =
      List.iter (fun l ->
		 let db = Hints.searchtable_map l in
		 Hints.Hint_db.iter (fun _ _ hintlist ->
				    syms := hintlist::!syms) db) dbs in
    List.fold_left
      (fun tac hints ->
       List.fold_left
	 (fun tac hint ->
            Hints.run_hint hint.Hints.code (add_runner combiner tac tacK))
	 tac hints)
      (Proofview.tclUNIT ()) !syms

  let first_combiner a b =
    Proofview.tclORELSE a (fun _ -> b)
  let seq_combiner a b =
    Proofview.tclBIND a (fun _ -> b)
  let plus_combiner a b =
    Proofview.tclOR a (fun _ -> b)

end

TACTIC EXTEND first_of_hint_db
  | [ "first_of" "[" ne_preident_list(l) "]" "run" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.first_combiner l k ]
END;;

TACTIC EXTEND all_of_hint_db
  | [ "foreach" "[" ne_preident_list(l) "]" "run" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.seq_combiner l k ]
END;;

TACTIC EXTEND plus_of_hint_db
  | [ "plus_of" "[" ne_preident_list(l) "]" "run" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.plus_combiner l k ]
END;;
