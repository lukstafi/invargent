(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

exception Contradiction of string * (typ * typ) option * loc

type cnstrnt =
| And of cnstrnt list
| Or of atom list
| Impl of atom list * cnstrnt list
| All of var_name list * cnstrnt
| Ex of var_name list * cnstrnt

(* Global state for fresh variable guarantees: not re-entrant. *)
let fresh_var_id = ref 0
let fresh_chi_id = ref 0

let freshen_typ env ty =
  let rec aux env = function
    | TVar v ->
      (try env, TVar (List.assoc v env)
       with Not_found ->
         let v' = TVar (VId (var_sort v, !fresh_var_id)) in
         (v, v')::env, TVar v')
    | TCons (n, tys) ->
      let env, tys = Aux.fold_map aux env tys in
      env, TCons (n, tys)
    | Fun (t1, t2) ->
      let env, t1 = aux env t1 in
      let env, t2 = aux env t2 in
      env, Fun (t1, t2)
    | NCst _ as c -> c
    | Nadd tys ->
      let env, tys = Aux.fold_map aux env tys in
      env, Nadd tys

let constr_gen_pat p =
  ()

let envfrag_gen_pat p =
  ()

let constr_gen_expr e =
  ()

