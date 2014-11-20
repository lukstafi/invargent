(** Definitions indispensable in every sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
(** If [nodeadcode=true], fail on implication branches with
    contradictory premises, which are not negation branches. "False
    positives" are possible in complex programs using [min] or [max]
    atoms, especially if [force_nodeadcode=true]. False negatives are
    possible only if [force_nodeadcode=false]. Default [true]. *)
val nodeadcode : bool ref
(** If [force_nodeadcode=false], let through some cases indicative of
    dead code when a possible alternative explanation is that the
    contradiction is due to a combination of min, max predicates. The
    min, max predicates are treated as disjunctions, and are expanded
    to DNF in premises. Default [false]. *)
val force_nodeadcode : bool ref
val deadcode_flag : bool ref

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
(** The locations have nonempty intersection. *)
val interloc : loc -> loc -> bool

type sort = Num_sort | Type_sort | Order_sort
val sort_str : sort -> string

(** Type variables (and constants) remember their sort. Sort
    inference is performed on user-supplied types and constraints. *)
type var_name =
| VNam of sort * string
| VId of sort * int

val delta : var_name
val delta' : var_name

val var_sort : var_name -> sort
val var_str : var_name -> string

module VarSet : (Set.S with type elt = var_name)
val vars_of_list : var_name list -> VarSet.t
val add_vars : var_name list -> VarSet.t -> VarSet.t
val no_vs : VarSet.t
val vars_of_map : ('a -> VarSet.t) -> 'a list -> VarSet.t

module VarMap : (Map.S with type key = var_name)
val varmap_of_list : (var_name * 'a) list -> 'a VarMap.t
val add_to_varmap : (var_name * 'a) list -> 'a VarMap.t -> 'a VarMap.t
val empty_vmap : 'a VarMap.t
val concat_varmap : (var_name -> 'a -> 'b list) -> 'a VarMap.t -> 'b list

(** {2 Quantification} *)

type var_scope =
| Left_of | Same_params | Same_quant | Right_of

val var_scope_str : var_scope -> string

type quant_ops = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  same_as : var_name -> var_name -> unit;
  upward_of : var_name -> var_name -> bool;
}
val empty_q : quant_ops

val crosses_xparams :
  cmp_v : (var_name -> var_name -> var_scope) ->
  bvs:VarSet.t -> VarSet.t -> bool


(** {2 Printing} *)
val current_file_name : string ref

val pr_loc_pos_only : Format.formatter -> loc -> unit
val pr_loc_short : Format.formatter -> loc -> unit
val pr_loc_long : Format.formatter -> loc -> unit
val pr_loc_emb : Format.formatter -> loc -> unit
val pr_loc : Format.formatter -> loc -> unit
val pr_tyvar : Format.formatter -> var_name -> unit
val pr_vars : Format.formatter -> VarSet.t -> unit
