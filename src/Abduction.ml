(** Abduction for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

let abd_typ cmp_v uni_v brs =
()
  
let abd_num cmp_v uni_v brs =
  ()

let abd cmp_v uni_v brs =
  (* Do not change the order and no. of branches afterwards. *)
  let brs_typ, brs_num, brs_so = Aux.split3
      (Aux.map_some (fun (prem, concl) ->
        let prems_opt =
          try Some (unify ~use_quants:false cmp_v uni_v prem)
          with Contradiction _ -> None in
        match prems_opt with
        | prem_typ, prem_num, prem_so ->
          if List.exists
            (function CFalse _ -> true | _ -> false) prem_so
          then None
          else                          (* can raise Contradiction *)
            let concl_typ, concl_num, concl_so =
              unify ~use_quants:false cmp_v uni_v concl in
            List.iter (function
            | CFalse loc ->
              raise (Contradiction ("assert false is possible", None, loc))
            | _ -> ()) concl_so;
            if not (satisfiable_num concl_num) then None
            else Some ((prem_typ, concl_typ), (prem_num, concl_num),
                       (prem_so, concl_so)))
         brs in
  let sols_typ = abd_typ cmp_v uni_v brs_typ in
  Aux.lconcat_map
    (fun (tvs, ans_typ, more_num) ->
      let brs_num = List.map2
        (fun (prem,concl) more -> prem, more @ concl)
        brs_num more_num in
      let sols_num = abd_num cmp_v uni_v brs_num in
      Aux.lmap
        (fun (nvs, ans_num) -> nvs @ tvs,
          Aux.map_append (fun (v,t,loc) -> Eqty (TVar v,t,loc))
            ans_typ ans_num)
        sols_typ)
    sols_typ
