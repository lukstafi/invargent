(** Data structures and printing for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
(** {2 Definitions} *)

val debug : bool ref

(** Source location for reporting parsing and inference problems. *)
type loc = {beg_pos : Lexing.position; end_pos : Lexing.position}
val dummy_loc : loc

exception Report_toplevel of string * loc option

val min_pos : Lexing.position -> Lexing.position -> Lexing.position
val max_pos : Lexing.position -> Lexing.position -> Lexing.position

(** The span containing the provided locations, or the optional [loc]
    if given. *)
val loc_union : ?loc:loc -> loc -> loc -> loc
(** The location with smaller span. *)
val loc_tighter : loc -> loc -> loc

type pat =
    Zero
  | One of loc
  | PVar of string * loc
  | PAnd of pat * pat * loc
  | PCons of string * pat list * loc

val pat_loc : pat -> loc

type expr =
| Var of string * loc
| Num of int * loc
| Cons of string * expr list * loc
| App of expr * expr * loc
| Lam of clause list * loc
| ExLam of int * clause list * loc
| Letrec of string * expr * expr * loc
| Letin of pat * expr * expr * loc
| AssertFalse of loc
| AssertLeq of expr * expr * expr * loc
| AssertEqty of expr * expr * expr * loc

and clause = pat * expr

val expr_loc : expr -> loc
val clause_loc : clause -> loc

type sort = Num_sort | Type_sort | Undefined_sort
(** Type variables (and constants) remember their sort. Sort
    inference is performed on user-supplied types and constraints. *)
type var_name =
| VNam of sort * string
| VId of sort * int
type cns_name =
| CNam of string
| Extype of int

type typ =
| TVar of var_name
| TCons of cns_name * typ list
| Fun of typ * typ
| NCst of int
| Nadd of typ list
type atom =
| Eqty of typ * typ * loc
| Leq of typ * typ * loc
| CFalse of loc
| PredVarU of int * typ
| PredVarB of int * typ * typ
type formula = atom list
type typ_scheme = var_name list * formula * typ

val delta : var_name
val delta' : var_name

val var_sort : var_name -> sort
val var_str : var_name -> string

val extype_id : int ref
val predvar_id : int ref

(** {3 Mapping and folding over types.} *)
type typ_map = {
  map_tvar : var_name -> typ;
  map_tcons : cns_name -> typ list -> typ;
  map_fun : typ -> typ -> typ;
  map_ncst : int -> typ;
  map_nadd : typ list -> typ
}

type 'a typ_fold = {
  fold_tvar : var_name -> 'a;
  fold_tcons : cns_name -> 'a list -> 'a;
  fold_fun : 'a -> 'a -> 'a;
  fold_ncst : int -> 'a;
  fold_nadd : 'a list -> 'a
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
| Nadd_dir of typ list * typ list
type typ_loc = {typ_sub : typ; typ_ctx : typ_dir list}

val typ_up : typ_loc -> typ_loc option
val typ_down : typ_loc -> typ_loc option
val typ_next : ?same_level:bool -> typ_loc -> typ_loc option
val typ_out : typ_loc -> typ

(** Set [extype_id] and [predvar_id] to [0]. *)
val reset_state : unit -> unit

type struct_item =
| TypConstr of cns_name * sort list * loc
| ValConstr of cns_name * var_name list * formula * typ list
  * cns_name * var_name list * loc
| PrimVal of string * typ_scheme * loc
| LetRecVal of string * expr * typ_scheme option * expr list * loc
| LetVal of pat * expr * typ_scheme option * expr list * loc
type program = struct_item list

module VarSet : (Set.S with type elt = var_name)
val fvs_typ : typ -> VarSet.t
val fvs_atom : atom -> VarSet.t
val fvs_formula : formula -> VarSet.t
val vars_of_list : var_name list -> VarSet.t

(** {3 Formulas} *)

val atom_loc : atom -> loc

type subst = (var_name * (typ * loc)) list

val subst_atom : subst -> atom -> atom
val subst_formula : subst -> formula -> formula
val subst_fo_atom : subst -> atom -> atom
val subst_fo_formula : subst -> formula -> formula
val fvs_sb : subst -> VarSet.t

val enc_funtype : typ -> typ list -> typ
val ty_add : typ -> typ -> typ
val typ_scheme_of_item :
  ?env:(string * typ_scheme) list -> struct_item -> typ_scheme
val current_file_name : string ref

(** Turn [a -> b -> c -> d] into [[a; b; c; d]] etc. and a
    non-function type into a singleton list. *)
val collect_argtys : typ -> typ list
(** Patterns of consecutive single-branch [Lam] and the first
    non-single-branch-[Lam] expression. *)
val collect_lambdas : expr -> pat list * expr
(** Arguments and the resulting function in reverse order of
    application: turn [((a b) c) d] into [a; b; c; d] etc. *)
val collect_apps : expr -> expr list

(** {2 Substitutions and unification} *)

type var_scope =
| Upstream | Same_quant | Downstream | Not_in_scope

val str_of_cmp : var_scope -> string

exception Contradiction of string * (typ * typ) option * loc
exception Suspect of var_name list * formula

val subst_typ : subst -> typ -> typ
val update_sb : more_sb:subst -> subst -> subst
val typ_sort_typ : typ -> bool
val num_sort_typ : typ -> bool
val unify : use_quants:bool -> ?params:VarSet.t ->
  ?sb:subst ->
  (var_name -> var_name -> var_scope) -> (var_name -> bool) ->
  atom list -> subst * atom list * atom list
val to_formula : subst -> atom list
val combine_sbs : use_quants:bool -> ?params:VarSet.t ->
  (var_name -> var_name -> var_scope) -> (var_name -> bool) ->
  ?more_phi:atom list -> subst list -> subst * atom list
val subst_solved : use_quants:bool -> ?params:VarSet.t ->
  (var_name -> var_name -> var_scope) -> (var_name -> bool) ->
  subst -> cnj:subst -> subst * atom list

(** {2 Sort inference} *)

val infer_sorts_item : struct_item -> struct_item list
val infer_sorts : program -> program

(** {2 Printing} *)

val sort_str : sort -> string
val pr_loc_short : Format.formatter -> loc -> unit
val pr_loc_long : Format.formatter -> loc -> unit
val pr_loc_emb : Format.formatter -> loc -> unit
val pr_loc : Format.formatter -> loc -> unit
val pr_sep_list :
  string ->
  ?pr_hd:(Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_pre_sep_list :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_line_list :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_pat : bool -> Format.formatter -> pat -> unit
val pr_tyvar : Format.formatter -> var_name -> unit
val pr_expr : bool -> Format.formatter -> expr -> unit
val pr_clause : Format.formatter -> clause -> unit
val pr_atom : Format.formatter -> atom -> unit
val pr_formula : Format.formatter -> formula -> unit
val pr_ty : bool -> Format.formatter -> typ -> unit
val pr_sort : Format.formatter -> sort -> unit
val pr_typscheme :
  Format.formatter -> typ_scheme -> unit
val pr_ans :
  Format.formatter -> var_name list * formula -> unit
val pr_subst : Format.formatter -> subst -> unit
val pr_typ_dir : Format.formatter -> typ_dir -> unit
val pr_typ_loc : Format.formatter -> typ_loc -> unit
val pr_struct_item : Format.formatter -> struct_item -> unit
val pr_program : Format.formatter -> struct_item list -> unit
val pr_exception : Format.formatter -> exn -> unit
val pr_to_str : (Format.formatter -> 'a -> unit) -> 'a -> string

val parser_more_items : struct_item list ref
val parser_unary_typs : (string, unit) Hashtbl.t
val parser_unary_vals : (string, unit) Hashtbl.t
val parser_last_typ : int ref
val parser_last_num : int ref
