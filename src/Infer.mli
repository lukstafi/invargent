(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
exception Contradiction of string * (Terms.typ * Terms.typ) option *
            Terms.loc
type cnstrnt =
    A of Terms.atom list
  | And of cnstrnt list
  | Or1 of Terms.atom list
  | Impl of Terms.atom list * cnstrnt
  | ImplOr2 of (Terms.atom * Terms.atom) list * cnstrnt
  | All of Terms.VarSet.t * cnstrnt
  | Ex of Terms.VarSet.t * cnstrnt
val typ_to_sch : 'a * 'b -> 'a * ('c list * 'd list * 'b)
val constr_gen_expr :
  (string * Terms.typ_scheme) list ->
  (string, 
   Terms.var_name list * Terms.atom list * Terms.typ list * Terms.typ)
  Hashtbl.t -> Terms.expr -> Terms.typ -> cnstrnt
val nicevars_cnstrnt : cnstrnt -> cnstrnt
val pr_cnstrnt : Format.formatter -> cnstrnt -> unit
