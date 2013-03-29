(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
exception Contradiction of string * (Terms.typ * Terms.typ) option *
            Terms.loc
type cnstrnt =
| A of Terms.atom list
| And of cnstrnt list
| Or1 of Terms.atom list
| Impl of Terms.atom list * cnstrnt
| ImplOr2 of Terms.atom list list * cnstrnt
| All of Terms.VarSet.t * cnstrnt
| Ex of Terms.VarSet.t * cnstrnt

val cn_and : cnstrnt -> cnstrnt -> cnstrnt

val freshen_cns_scheme :
  Terms.var_name list * Terms.atom list * Terms.typ list * Terms.typ ->
  Terms.var_name list * Terms.atom list * Terms.typ list * Terms.typ
val freshen_val_scheme : typ_scheme -> typ_scheme
type sigma =
  (string,
   Terms.var_name list * Terms.atom list * Terms.typ list * Terms.typ)
    Hashtbl.t
val constr_gen_pat :
  sigma -> Terms.pat -> Terms.typ -> cnstrnt
type envfrag = Terms.VarSet.t * Terms.formula * (string * Terms.typ) list
val typ_to_sch : 'a * Terms.typ -> 'a * Terms.typ_scheme
val constr_gen_expr :
  (string * Terms.typ_scheme) list -> sigma ->
  (Terms.cns_name * (Terms.typ -> Terms.typ -> Terms.atom list) * Terms.loc)
  list ref -> Terms.expr -> Terms.typ -> cnstrnt
type solution =
  (Terms.subst * Terms.formula) *
    (int * (Terms.typ -> Terms.subst * Terms.atom list)) list *
    (int * (Terms.var_name -> Terms.var_name -> Terms.subst * Terms.formula))
    list
val infer_prog :
  (cnstrnt -> solution) -> Terms.struct_item list -> Terms.struct_item list
(*
type nicevars_env
val nicevars_empty : nicevars_env
val next_typ : nicevars_env -> int -> nicevars_env
val next_num : nicevars_env -> int -> nicevars_env
val nicevars_typ : nicevars_env -> Terms.typ -> Terms.typ
val nicevars_atom : nicevars_env -> Terms.atom -> Terms.atom
*)
val nicevars_cnstrnt : cnstrnt -> cnstrnt
val nicevars_struct_item : struct_item -> struct_item
val pr_cnstrnt : Format.formatter -> cnstrnt -> unit
