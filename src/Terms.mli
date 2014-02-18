(** Data structures and printing for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
val show_extypes : bool ref

(** {2 Definitions} *)

val debug : bool ref

type cns_name =
| CNam of string
| Extype of int
val tuple : cns_name
val numtype : cns_name
val booltype : cns_name
val stringtype : cns_name

module CNames : (Set.S with type elt = cns_name)
val cnames_of_list : cns_name list -> CNames.t
val add_cnames : cns_name list -> CNames.t -> CNames.t

val init_types : CNames.t

type lc = Defs.loc

type pat =
    Zero
  | One of lc
  | PVar of string * lc
  | PAnd of pat * pat * lc
  | PCons of cns_name * pat list * lc

val pat_loc : pat -> lc

(** [string option] at [Letrec] and [Letin] are documentation
    comments. ['a] and ['b] parameters stand for annotations, e.g. type
    annotations in the last stage of inference. *)
type ('a, 'b) expr =
| Var of string * lc
| Num of int * lc
| NumAdd of ('a, 'b) expr * ('a, 'b) expr * lc
| String of string * lc
| Cons of cns_name * ('a, 'b) expr list * lc
| App of ('a, 'b) expr * ('a, 'b) expr * lc
| Lam of 'b * ('a, 'b) clause list * lc
| ExLam of int * ('a, 'b) clause list * lc
| Letrec of string option * 'a * string * ('a, 'b) expr * ('a, 'b) expr * lc
| Letin of string option * pat * ('a, 'b) expr * ('a, 'b) expr * lc
| AssertFalse of lc
| AssertLeq of ('a, 'b) expr * ('a, 'b) expr * ('a, 'b) expr * lc
| AssertEqty of ('a, 'b) expr * ('a, 'b) expr * ('a, 'b) expr * lc

and ('a, 'b) clause =
  pat * (('a, 'b) expr * ('a, 'b) expr) list * ('a, 'b) expr

val expr_loc : ('a, 'b) expr -> lc
val clause_loc : ('a, 'b) clause -> lc

type alien_subterm =
  | Num_term of NumDefs.term

type typ =
  | TVar of Defs.var_name
  | TCons of cns_name * typ list
  | Fun of typ * typ
  | Alien of alien_subterm

val num : NumDefs.term -> typ

type alien_atom =
  | Num_atom of NumDefs.atom

type atom =
  | Eqty of typ * typ * lc
  | CFalse of lc
  | PredVarU of int * typ * lc
  | PredVarB of int * typ * typ * lc
  | NotEx of typ * lc
  | A of alien_atom

val a_num : NumDefs.atom -> atom

type formula = atom list
type typ_scheme = Defs.var_name list * formula * typ
type answer = Defs.var_name list * formula

(** User input expression: no type annotations. *)
type uexpr = (unit, unit) expr

(** Post-constraint generation expression: number of predicate
    variable holding the invariant for each [let rec] expression;
    variables standing for the argument and return type of each
    [function] expression. *)
type iexpr = (int list, (Defs.var_name * Defs.var_name) list) expr

(** The annotation, besides providing the type scheme, tells whether
    nested type schemes have free variables in scope of the
    scheme. On [Lam] annotations, provides the argument and the
    return type separately. *)
type texpr = (typ_scheme * bool, (typ * typ) option) expr
val fuse_exprs : iexpr list -> iexpr
val tdelta : typ
val tdelta' : typ

val return_type : typ -> typ
val arg_types : typ -> typ list

val cns_str : cns_name -> string

val extype_id : int ref
val predvar_id : int ref

(** {3 Mapping and folding over types.} *)
type typ_map = {
  map_tvar : Defs.var_name -> typ;
  map_tcons : string -> typ list -> typ;
  map_exty : int -> typ list -> typ;
  map_fun : typ -> typ -> typ;
  map_alien : alien_subterm -> typ
}

type 'a typ_fold = {
  fold_tvar : Defs.var_name -> 'a;
  fold_tcons : string -> 'a list -> 'a;
  fold_exty : int -> 'a list -> 'a;
  fold_fun : 'a -> 'a -> 'a;
  fold_alien : alien_subterm -> 'a
}

val typ_id_map : typ_map

val typ_make_fold : ('a -> 'a -> 'a) -> 'a -> 'a typ_fold

val typ_map : typ_map -> typ -> typ

val typ_fold : 'a typ_fold -> typ -> 'a

(** {3 Zippers.} *)
type typ_dir =
| TCons_dir of cns_name * typ list * typ list
| Fun_left of typ
| Fun_right of typ
type typ_loc = {typ_sub : typ; typ_ctx : typ_dir list}

val typ_up : typ_loc -> typ_loc option
val typ_down : typ_loc -> typ_loc option
val typ_next : ?same_level:bool -> typ_loc -> typ_loc option
val typ_out : typ_loc -> typ

(** Set [extype_id] and [predvar_id] to [0]. *)
val reset_state : unit -> unit

(** [string option] stores the documentation comment appearing in
    front of a definition or declaration. *)
type struct_item =
| TypConstr of string option * cns_name * Defs.sort list * lc
| ValConstr of
    string option * cns_name * Defs.var_name list * formula * typ list
    * cns_name * Defs.var_name list * lc
| PrimVal of
    string option * string * typ_scheme * (string, string) Aux.choice * lc
| LetRecVal of
    string option * string * uexpr * typ_scheme option * uexpr list * lc
| LetVal of
    string option * pat * uexpr * typ_scheme option * uexpr list * lc

(** Represents both signature items and annotated structure items to
    be printed as OCaml source code. *)
type annot_item =
| ITypConstr of
    string option * cns_name * Defs.sort list * lc
| IValConstr of
    string option * cns_name * Defs.var_name list * formula * typ list
    * cns_name * typ list * lc
| IPrimVal of
    string option * string * typ_scheme * (string, string) Aux.choice * lc
| ILetRecVal of
    string option * string * texpr * typ_scheme *
      texpr list * (pat * int option) list * lc
| ILetVal of
    string option * pat * texpr * typ_scheme * (string * typ_scheme) list *
      texpr list * (pat * int option) list * lc

val typ_size : typ -> int
val atom_size : atom -> int
val fvs_typ : typ -> Defs.VarSet.t
val fvs_typs : typ list -> Defs.VarSet.t
val fvs_atom : atom -> Defs.VarSet.t
val fvs_formula : formula -> Defs.VarSet.t
val formula_loc : formula -> lc

(** {3 Formulas} *)

val atom_loc : atom -> lc

type subst = (Defs.var_name * (typ * lc)) list
type hvsubst = (Defs.var_name * Defs.var_name) list

type sep_formula = {
  cnj_typ : subst;
  cnj_num : NumDefs.formula;
  cnj_so : formula
}
(** We could define [sep_formula = (subst, NumDefs.formula formula)
    sep_sorts], but [sep_formula] is used frequently enough to earn
    a dedicated type. *)
type ('a, 'b, 'c) sep_sorts = {
  at_typ : 'a;
  at_num : 'b;
  at_so : 'c
}

val num_unbox : t2:typ -> Defs.loc -> typ -> NumDefs.term
val num_v_unbox : Defs.var_name -> Defs.loc -> typ -> NumDefs.term
val subst_atom : subst -> atom -> atom
val subst_formula : subst -> formula -> formula
val hvsubst_formula : hvsubst -> formula -> formula
val subst_fo_atom : subst -> atom -> atom
val subst_fo_formula : subst -> formula -> formula
val fvs_sb : subst -> Defs.VarSet.t
val eq_atom : atom -> atom -> bool
val subformula : formula -> formula -> bool
val formula_inter : formula -> formula -> formula
val formula_diff : formula -> formula -> formula

val replace_loc_atom : lc -> atom -> atom
val replace_loc : lc -> formula -> formula

(** Substitutions of variables [delta] and [delta']. *)
val sb_typ_unary : typ -> typ -> typ
val sb_typ_binary : typ -> typ -> typ -> typ
val sb_atom_unary : typ -> atom -> atom
val sb_atom_binary : typ -> typ -> atom -> atom
val sb_phi_unary : typ -> formula -> formula
val sb_phi_binary : typ -> typ -> formula -> formula

val enc_funtype : typ -> typ list -> typ
val typ_scheme_of_item :
  ?env:(string * typ_scheme) list -> struct_item -> typ_scheme

(** Turn [a -> b -> c -> d] into [[a; b; c; d]] etc. and a
    non-function type into a singleton list. *)
val collect_argtys : typ -> typ list
(** Patterns of consecutive single-branch [Lam] and the first
    non-single-branch-[Lam] expression. *)
val collect_lambdas : ('a, 'b) expr -> pat list * ('a, 'b) expr
(** Arguments and the resulting function in reverse order of
    application: turn [((a b) c) d] into [a; b; c; d] etc. *)
val collect_apps : ('a, 'b) expr -> ('a, 'b) expr list

(** Connected component(s) of the hypergraph spanned on variables,
    containing the given variables. [validate] should raise
    [Contradiction] when a result is incorrect. *)
val connected :
  ?validate:(formula -> unit) ->
  Defs.var_name list -> answer -> answer


(** {2 Substitutions and unification} *)

exception Contradiction of Defs.sort * string * (typ * typ) option * lc
exception NoAnswer of Defs.sort * string * (typ * typ) option * lc
exception Suspect of formula * lc
(** Change [Contradiction] to [NoAnswer] and vice-versa, identity on
    other exceptions. *)
val convert : exn -> exn

val subst_typ : subst -> typ -> typ
val hvsubst_typ : hvsubst -> typ -> typ
val subst_sb : sb:subst -> subst -> subst
val hvsubst_sb : hvsubst -> subst -> subst
val update_sb : more_sb:subst -> subst -> subst
(** [subst] must be a renaming of variables. *)
val revert_renaming : subst -> subst
(** Union/conjunction of sort-separated formulas, additionally
    perform an update of the term substitution. *)
val update_sep :
   ?typ_updated:bool -> more:sep_formula -> sep_formula -> sep_formula
(** Separate atoms into their sorts. Warning: ignores type sort atoms
    which are not solved form equations. *)
val sep_formulas : formula -> sep_formula
val unsep_formulas : sep_formula -> formula
val map_in_subst : (typ -> typ) -> subst -> subst
(** Substitute constants, and generally subterms identical to a term,
    with another term. [loc] is not used. *)
val c_subst_typ : (typ * (typ * lc)) list -> typ -> typ
val n_subst_typ : (cns_name * (typ list -> typ)) list -> typ -> typ
val typ_sort : typ -> Defs.sort
val atom_sort : atom -> Defs.sort

val var_not_left_of : Defs.quant_ops -> Defs.var_name -> typ -> bool

(** Register variable as [NotEx]. *)
val register_notex : Defs.var_name -> unit
(** [use_quants] whether to check for quantifier violations. [bvs] are
    variables that are parameters of invariants (or are candidates for
    such in the partial answer). [pms] are parameters to be ignored
    from quantifier violations, but should already be right-most in
    the quantifier. The first element of returned triple is the
    unifier, the second are numeric constraints including equations,
    the third one are predicate variables and [NotEx] atoms. The
    substitution is not applied to the third element atoms! *)
val unify :
  ?use_quants:bool -> ?bvs:Defs.VarSet.t -> ?pms:Defs.VarSet.t ->
  ?sb:subst -> Defs.quant_ops ->
  atom list -> sep_formula
val to_formula : subst -> formula
(** Find the atoms in the formula which are valid substitutions. *)
val subst_of_cnj : ?elim_uni:bool -> Defs.quant_ops -> formula -> subst
val combine_sbs :
  ?use_quants:bool -> ?bvs:Defs.VarSet.t -> ?pms:Defs.VarSet.t ->
  Defs.quant_ops ->
  ?more_phi:formula -> subst list -> sep_formula
val subst_solved :
  ?use_quants:bool -> ?bvs:Defs.VarSet.t -> ?pms:Defs.VarSet.t ->
  Defs.quant_ops ->
  subst -> cnj:subst -> sep_formula
val cleanup :
  Defs.quant_ops -> Defs.var_name list -> subst ->
  Defs.var_name list * subst

(** {2 Global tables} *)

type sigma =
  (cns_name, Defs.var_name list * formula * typ list *
               cns_name * Defs.var_name list)
    Hashtbl.t

val sigma : sigma
val all_ex_types : (int * lc) list ref

val fresh_typ_var : unit -> Defs.var_name
val fresh_num_var : unit -> Defs.var_name
val fresh_var : Defs.sort -> Defs.var_name
val freshen_var : Defs.var_name -> Defs.var_name

(** {2 Printing} *)

val pr_pat : Format.formatter -> pat -> unit

type ('a, 'b) pr_expr_annot =
  | LetRecNode of 'a
  | LamNode of 'b
  | MatchVal of 'b
  | MatchRes of 'b
  | LamOpen of 'b
  | MatchValOpen of 'b
  | MatchResOpen of 'b
  | LetInOpen of 'b
  | LetInNode of 'b

val pr_expr :
  ?export_num:(string * string * string * string) ->
  ?export_if:(string*string*string)
  -> ?export_bool:((bool * string) list) ->
  (Format.formatter -> ('a, 'b) pr_expr_annot -> unit) ->
  Format.formatter -> ('a, 'b) expr -> unit
val pr_uexpr : Format.formatter -> uexpr -> unit
val pr_iexpr : Format.formatter -> iexpr -> unit
val pr_atom : Format.formatter -> atom -> unit
val pr_formula : Format.formatter -> formula -> unit
val pr_ty : Format.formatter -> typ -> unit
val pr_alien_ty : Format.formatter -> alien_subterm -> unit
val pr_sort : Format.formatter -> Defs.sort -> unit
val pr_typscheme :
  Format.formatter -> typ_scheme -> unit
val pr_ans :
  Format.formatter -> answer -> unit
val pr_subst : Format.formatter -> subst -> unit
val pr_hvsubst : Format.formatter -> hvsubst -> unit
val pr_typ_dir : Format.formatter -> typ_dir -> unit
val pr_typ_loc : Format.formatter -> typ_loc -> unit
val pr_struct_item : Format.formatter -> struct_item -> unit
val pr_program : Format.formatter -> struct_item list -> unit
val pr_sig_item : Format.formatter -> annot_item -> unit
val pr_signature : Format.formatter -> annot_item list -> unit
val pr_exception : Format.formatter -> exn -> unit
val pr_to_str : (Format.formatter -> 'a -> unit) -> 'a -> string

val parser_more_items : struct_item list ref
val parser_unary_typs : (string, unit) Hashtbl.t
val parser_unary_vals : (cns_name, unit) Hashtbl.t
val parser_last_typ : int ref
val parser_last_num : int ref

(** {2 Nice variables} *)

val next_var : Defs.VarSet.t -> Defs.sort -> Defs.var_name
(** The [fvs] argument only lists additional variable names to
    consider "occupied" besides variables in the answer provided. *)
val nice_ans :
  ?sb:hvsubst -> ?fvs:Defs.VarSet.t -> answer -> hvsubst * answer
