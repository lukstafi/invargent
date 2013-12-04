(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

type cnstrnt =
| A of Terms.formula
| And of cnstrnt list
| Impl of Terms.formula * cnstrnt
| Or of cnstrnt list
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
  Terms.uexpr -> Terms.typ -> cnstrnt * Terms.iexpr
type solution =
  Terms.quant_ops * Terms.formula *
    (int * (Terms.var_name list * Terms.formula)) list
val infer_prog_mockup : Terms.struct_item list -> Terms.VarSet.t * cnstrnt
val infer_prog :
  (preserve:Terms.VarSet.t -> cnstrnt -> solution) ->
  Terms.struct_item list ->
  (string * Terms.typ_scheme) list * Terms.annot_item list

(** {2 Normalization} *)
val normalize_expr : Terms.uexpr -> Terms.uexpr
val normalize_program : Terms.program -> Terms.program

type branch = Terms.formula * Terms.formula
val fresh_typ_var : unit -> Terms.var_name
val fresh_num_var : unit -> Terms.var_name
val fresh_var : Terms.sort -> Terms.var_name
val freshen_var : Terms.var_name -> Terms.var_name

val prenexize : cnstrnt -> Terms.quant_ops * cnstrnt
(** Returns a map from existential type to the unary predicate variable
    in which it will appear as result type. *)
val normalize :
  Terms.quant_ops -> cnstrnt -> (int, int) Hashtbl.t * branch list

(* Eliminate shared conclusions during {!simplify}. *)
val simplify :
  Terms.VarSet.t ->
  Terms.quant_ops -> branch list -> branch list

(** {2 Postprocessing and printing} *)

val separate_subst :
  ?avoid:Terms.VarSet.t ->
  Terms.quant_ops -> Terms.formula ->
  Terms.subst * Terms.formula

val pr_cnstrnt : Format.formatter -> cnstrnt -> unit
val pr_brs : Format.formatter -> branch list -> unit
val pr_rbrs : Format.formatter -> (Terms.formula * Terms.formula) list -> unit
val pr_rbrs3 :
  Format.formatter -> (bool * Terms.formula * Terms.formula) list -> unit
val pr_rbrs4 :
  Format.formatter ->
  (bool * 'a * Terms.formula * Terms.formula) list -> unit
val pr_rbrs5 :
  Format.formatter ->
  (bool * 'a * 'b * Terms.formula * Terms.formula) list -> unit

val reset_state : unit -> unit
