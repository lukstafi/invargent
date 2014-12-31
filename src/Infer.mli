(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val annotating_fun : bool ref
val annotating_letin : bool ref
val inform_toplevel : bool ref
val time_toplevel : bool ref

(** Each disjunct stores a trigger to be called when other disjuncts
    are eliminated during normalization-simplification. *)
type cnstrnt =
| A of Terms.formula
| And of cnstrnt list
| Impl of Terms.formula * cnstrnt
| Or of Defs.var_name *
          (Defs.VarSet.t * cnstrnt * Terms.formula * (unit -> unit)) list *
          cnstrnt
| All of Defs.VarSet.t * cnstrnt
| Ex of Defs.VarSet.t * cnstrnt

val cn_and : cnstrnt -> cnstrnt -> cnstrnt

(** {2 Constraint inference} *)

val freshen_cns_scheme :
  Defs.var_name list * Terms.atom list * Terms.typ list *
  Terms.cns_name * Defs.var_name list ->
  Defs.var_name list * Terms.atom list * Terms.typ list *
  Terms.cns_name * Defs.var_name list
val freshen_val_scheme : Terms.typ_scheme -> Terms.typ_scheme
val constr_gen_pat : Terms.pat -> Terms.typ -> cnstrnt
type envfrag = Defs.VarSet.t * Terms.formula * (string * Terms.typ) list
val typ_to_sch : 'a * Terms.typ -> 'a * Terms.typ_scheme
(** Return a store cell where triggers will put which existentials are
    eliminated by which let-in patterns, and variables to preserve in
    the result (i.e. prevent from being dropped by simplification). *)
val constr_gen_expr :
  (string * Terms.typ_scheme) list ->
  Terms.uexpr -> Terms.typ ->
  (cnstrnt * Terms.iexpr) * (Terms.pat * int option) list ref *
    Defs.var_name list
type program = ((int * Defs.loc) list * Terms.struct_item) list
type solution =
  Defs.quant_ops * Terms.formula *
    (int * (Defs.var_name list * Terms.formula)) list
val infer_prog_mockup :
  program -> (int * Defs.loc) list * Defs.VarSet.t * cnstrnt
val infer_prog :
  (new_ex_types:(int * Defs.loc) list ->
   preserve:Defs.VarSet.t -> cnstrnt -> solution) ->
  program ->
  (string * Terms.typ_scheme) list * Terms.annot_item list

(** {2 Normalization} *)
val normalize_expr : Terms.uexpr -> (int * Defs.loc) list * Terms.uexpr
val normalize_program :
  Terms.struct_item list -> ((int * Defs.loc) list * Terms.struct_item) list

type branch = Terms.formula * Terms.formula

val prenexize : cnstrnt -> Defs.quant_ops * cnstrnt
(** Returns a map from existential type to the unary predicate variable
    in which it will appear as result type. *)
val normalize :
  Defs.quant_ops -> cnstrnt -> (int, int) Hashtbl.t * branch list

(** Contains information about phantom enumerations,
    i.e. alternatives to a datatype parameter's nullary concrete type
    excluded by an [assert false] pattern-matching branch.
    If the value for an is an empty list, the entry is not a phantom
    enumeration. *)
val phantom_enumeration : (Terms.cns_name, Terms.cns_name list) Hashtbl.t

(** Eliminate shared conclusions. Solve [RetType] constraints. *)
val simplify :
  Defs.VarSet.t ->
  Defs.quant_ops -> branch list -> branch list

(** {2 Postprocessing and printing} *)

val separate_subst :
  ?avoid:Defs.VarSet.t -> ?keep_uni:bool ->
  Defs.quant_ops -> Terms.formula ->
  Terms.subst * Terms.formula
val separate_sep_subst :
  ?avoid:Defs.VarSet.t -> ?keep_uni:bool ->
  Defs.quant_ops -> Terms.sep_formula ->
  Terms.subst * Terms.sep_formula

val pr_cnstrnt : Format.formatter -> cnstrnt -> unit
val pr_brs : Format.formatter -> branch list -> unit
val pr_rbrs : Format.formatter -> (Terms.formula * Terms.formula) list -> unit
val pr_rbrs3 :
  Format.formatter -> (bool * Terms.formula * Terms.formula) list -> unit
val pr_rbrs4 :
  Format.formatter ->
  (bool * 'a list * Terms.formula * Terms.formula) list -> unit
val pr_rbrs5 :
  Format.formatter ->
  (bool * (int * Terms.typ) list *
     (int * Terms.typ * Terms.typ * Terms.lc) list * Terms.atom list *
     Terms.atom list)
         list -> unit

val reset_state : unit -> unit
