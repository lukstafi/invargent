(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
type cnstrnt =
| A of Terms.atom list
| And of cnstrnt list
| Or1 of Terms.atom list
| Impl of Terms.atom list * cnstrnt
| ImplOr2 of Terms.atom list list * cnstrnt * cnstrnt
| All of Terms.VarSet.t * cnstrnt
| Ex of Terms.VarSet.t * cnstrnt

val cn_and : cnstrnt -> cnstrnt -> cnstrnt

(** {2 Constraint inference} *)

val freshen_cns_scheme :
  Terms.var_name list * Terms.atom list * Terms.typ list *
  Terms.cns_name * Terms.var_name list ->
  Terms.var_name list * Terms.atom list * Terms.typ list *
  Terms.cns_name * Terms.var_name list
val freshen_val_scheme : Terms.typ_scheme -> Terms.typ_scheme
val constr_gen_pat : Terms.pat -> Terms.typ -> cnstrnt
type envfrag = Terms.VarSet.t * Terms.formula * (string * Terms.typ) list
val typ_to_sch : 'a * Terms.typ -> 'a * Terms.typ_scheme
val constr_gen_expr :
  (string * Terms.typ_scheme) list ->
  Terms.expr -> Terms.typ -> cnstrnt
type solution =
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) *
    (Terms.var_name -> bool) * Terms.formula *
    (int * (Terms.var_name list * Terms.formula)) list
val infer_prog_mockup : Terms.struct_item list -> Terms.VarSet.t * cnstrnt
val infer_prog :
  (preserve:Terms.VarSet.t -> cnstrnt -> solution) ->
  Terms.struct_item list ->
  (string * Terms.typ_scheme) list * Terms.struct_item list

(** {2 Normalization} *)
type branch =
  Terms.formula * (Terms.subst * Terms.formula * Terms.formula)
val br_to_formulas : branch -> Terms.formula * Terms.formula
val fresh_typ_var : unit -> Terms.var_name
val fresh_num_var : unit -> Terms.var_name
val freshen_var : Terms.var_name -> Terms.var_name

val normalize : cnstrnt ->
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) *
    (Terms.var_name, bool) Hashtbl.t *
    branch list

(* Eliminate shared conclusions during {!simplify}. *)
val simplify :
  Terms.VarSet.t ->
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool)-> branch list -> branch list

(** {2 Postprocessing and printing} *)

val separate_subst :
  (Terms.var_name -> Terms.var_name -> Terms.var_scope) ->
  (Terms.var_name -> bool)-> Terms.formula ->
  Terms.subst * Terms.formula

(*
type nicevars_env
val nicevars_empty : nicevars_env
val next_typ : nicevars_env -> int -> nicevars_env
val next_num : nicevars_env -> int -> nicevars_env
val nicevars_typ : nicevars_env -> Terms.typ -> Terms.typ
val nicevars_atom : nicevars_env -> Terms.atom -> Terms.atom
*)
val nicevars_cnstrnt : cnstrnt -> cnstrnt
val nicevars_struct_item : Terms.struct_item -> Terms.struct_item
val pr_cnstrnt : Format.formatter -> cnstrnt -> unit
val pr_brs : Format.formatter -> branch list -> unit
val pr_rbrs : Format.formatter -> (Terms.formula * Terms.formula) list -> unit
val pr_rbrs3 :
  Format.formatter -> (bool * Terms.formula * Terms.formula) list -> unit
val pr_rbrs5 :
  Format.formatter ->
  (bool * 'a * 'b * Terms.formula * Terms.formula) list -> unit

val reset_state : unit -> unit
