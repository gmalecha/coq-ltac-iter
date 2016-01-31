(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Plugin_utils


DECLARE PLUGIN "ltac_iter_plugin"

module WITH_DB =
struct

  type collection =
    | Module of Constrexpr.constr_expr
    | HintDb of Hints.hint_db_name
    | Search of Term.constr list
    | Reverse of collection
    | Premise
    | Ctors of Constrexpr.constr_expr

  let rec pr_collection = function
      Module c -> assert false
    | HintDb db -> Pp.(str "db:" ++ str db)
    | Search ls -> assert false
    | Reverse c -> Pp.(str "rev" ++ pr_collection c)
    | Premise -> Pp.str "*|-"
    | Ctors typ -> Pp.(str "ctors:" ++ str "")

  let add_runner combiner else_tac tacK = function
    | Hints.Give_exact ((lem, _, _), _)
    | Hints.Res_pf ((lem, _, _), _)
    | Hints.ERes_pf ((lem, _, _), _) ->
      let this_tac =
        Use_ltac.ltac_apply tacK [Use_ltac.to_ltac_val lem] in
      combiner this_tac else_tac
    | _ -> else_tac

  let resolve_collection combiner tacK acc =
    let rec resolve_collection reverse = function
      | Reverse c -> resolve_collection (not reverse) c
      | HintDb db_name ->
        let db =
          let syms = ref [] in
          let db = Hints.searchtable_map db_name in
          Hints.Hint_db.iter (fun _ _ hl -> syms := hl :: !syms) db ;
          !syms
        in
        if reverse then
          Proofview.Goal.nf_enter begin fun gl ->
            List.fold_left (fun acc hints ->
                List.fold_left (fun acc hint ->
                    Hints.run_hint hint.Hints.code
                      (add_runner combiner acc tacK))
                  acc hints)
              acc db
          end
        else
          Proofview.Goal.nf_enter begin fun gl ->
            List.fold_right (fun hints acc ->
                List.fold_right (fun hint acc ->
                    Hints.run_hint hint.Hints.code
                      (add_runner combiner acc tacK))
                  hints acc)
              db acc
          end
      | Premise ->
        let call_on_id name =
          Use_ltac.ltac_apply tacK [Use_ltac.to_ltac_val (Term.mkVar name)] in
        if reverse then
          Proofview.Goal.nf_enter begin fun gl ->
            Context.fold_named_context_reverse
              (fun acc (name,_,_) -> combiner (call_on_id name) acc)
              ~init:acc
              (Proofview.Goal.hyps gl)
          end
        else
          Proofview.Goal.nf_enter begin fun gl ->
            Context.fold_named_context
              (fun (name,_,_) acc -> combiner (call_on_id name) acc)
              ~init:acc
              (Proofview.Goal.hyps gl)
          end
      | c ->
        Errors.anomaly ~label:"WithHintDb"
          Pp.(   str "Not Implemented: "
              ++ pr_collection c)
    in resolve_collection

  let the_tactic combiner dbs tacK =
    List.fold_right (fun db acc ->
        resolve_collection combiner tacK acc false db)
       dbs (Proofview.tclUNIT ())

  let first_combiner a b =
    Proofview.tclORELSE a (fun _ -> b)
  let seq_combiner a b =
    Proofview.tclBIND a (fun _ -> b)
  let plus_combiner a b =
    Proofview.tclOR a (fun _ -> b)

end

let pp_collection _ _ _ = WITH_DB.pr_collection

ARGUMENT EXTEND collection
TYPED AS collection
PRINTED BY pp_collection
  | [ "db:" preident(x) ] -> [ WITH_DB.HintDb x ]
  | [ "mod:" constr(m) ]  -> [ WITH_DB.Module m ]
  | [ "*|-" ] -> [ WITH_DB.Premise ]
  | [ "rev" collection(e) ] -> [ WITH_DB.Reverse e ]
  | [ "ctors:" constr(t) ] -> [ WITH_DB.Ctors t ]
  | [ "(" collection(e) ")" ] -> [ e ]
END;;

TACTIC EXTEND first_of_hint_db
  | [ "first_of" "[" ne_collection_list(l) "]" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.first_combiner l k ]
END;;

TACTIC EXTEND all_of_hint_db
  | [ "foreach" "[" ne_collection_list(l) "]" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.seq_combiner l k ]
END;;

TACTIC EXTEND plus_of_hint_db
  | [ "plus_of" "[" ne_collection_list(l) "]" tactic(k) ]  ->
    [ WITH_DB.the_tactic WITH_DB.plus_combiner l k ]
END;;
