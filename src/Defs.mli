(** Definitions indispensable in every sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)


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

type sort = Num_sort | Type_sort
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

(** {2 Quantification} *)

type var_scope =
| Left_of | Same_quant | Right_of

val var_scope_str : var_scope -> string

type quant_ops = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  same_as : var_name -> var_name -> unit;
}
val empty_q : quant_ops

(** {2 Printing} *)
val current_file_name : string ref

val pr_loc_pos_only : Format.formatter -> loc -> unit
val pr_loc_short : Format.formatter -> loc -> unit
val pr_loc_long : Format.formatter -> loc -> unit
val pr_loc_emb : Format.formatter -> loc -> unit
val pr_loc : Format.formatter -> loc -> unit
val pr_tyvar : Format.formatter -> var_name -> unit
val pr_vars : Format.formatter -> VarSet.t -> unit