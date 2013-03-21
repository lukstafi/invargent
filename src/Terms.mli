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
    Var of string * loc
  | Num of int * loc
  | Cons of string * expr list * loc
  | App of expr * expr * loc
  | Lam of clause list * loc
  | ExLam of int * clause list * loc
  | Letrec of string * expr * expr * loc
  | Letin of pat * expr * expr * loc
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
| PredVar of int * typ
type formula = atom list
type typ_scheme = var_name list * formula * typ

val var_sort : var_name -> sort
val var_str : var_name -> string

val extype_id : int ref
val predvar_id : int ref

(** Set [extype_id] and [predvar_id] to [0]. *)
val reset_processing : unit -> unit

type struct_item =
| TypConstr of cns_name * sort list * loc
| ValConstr of cns_name * var_name list * formula * typ list * typ * loc
| PrimVal of string * typ_scheme * loc
| LetRecVal of string * expr * loc
| LetVal of string * expr * loc
type program = struct_item list

module VarSet : (Set.S with type elt = var_name)
val fvs_typ : typ -> VarSet.t
val fvs_atom : atom -> VarSet.t
val fvs_formula : formula -> VarSet.t
val vars_of_list : var_name list -> VarSet.t

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
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_more_sep_list :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_pre_sep_list :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_line_list :
  string ->
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pr_more_line_list :
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
val pr_struct_item : Format.formatter -> struct_item -> unit
val pr_program : Format.formatter -> struct_item list -> unit
