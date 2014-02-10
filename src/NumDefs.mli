(** Definitions for the numeric sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val sort : Defs.sort

type term =
  | Cst of int * int                  (** [Cst (i,j)] = $(i/j)$ *)
  | Lin of int * int * Defs.var_name  (** [Lin [i,j,n]] = $(i/j)*n$ *)
  | Add of term list

val add : term -> term -> term
val diff : term -> term -> term

type atom =
  | Eq of term * term * Defs.loc
  | Leq of term * term * Defs.loc
  | Opti of term * term * Defs.loc
  | Subopti of term * term * Defs.loc
type formula = atom list

val fvs_term : term -> Defs.VarSet.t
val fvs_atom : atom -> Defs.VarSet.t
val fvs_formula : formula -> Defs.VarSet.t
val formula_inter : formula -> formula -> formula
val subformula : formula -> formula -> bool
val atom_loc : atom -> Defs.loc
val replace_loc_atom : Defs.loc -> atom -> atom
val replace_loc : Defs.loc -> formula -> formula
val eq_atom : atom -> atom -> bool
val subst_term :
  (Defs.var_name -> Defs.loc -> 'a -> term) ->
  (Defs.var_name * ('a * Defs.loc)) list ->
  term -> term
val subst_atom :
  (Defs.var_name -> Defs.loc -> 'a -> term) ->
  (Defs.var_name * ('a * Defs.loc)) list ->
  atom -> atom
val nsubst_atom :
  (Defs.var_name * term) list -> atom -> atom
val hvsubst_term :
  (Defs.var_name * Defs.var_name) list -> term -> term
val hvsubst_atom :
  (Defs.var_name * Defs.var_name) list -> atom -> atom
val term_size : term -> int
val atom_size : atom -> int
val formula_size : formula -> int
val iter_terms : (term -> unit) -> atom -> unit
val scale_term : int -> int -> term -> term
val iter_term_vars : (Defs.var_name -> unit) -> term -> unit
val denom : term -> int
val flatten :
  term -> (int * int * Defs.var_name) list * (int * int)
val direct_opti :
  term -> term -> (Defs.var_name * bool * term * term) option
val taut_atom_or_undir_opti : atom -> bool

val pr_term : Format.formatter -> term -> unit
val pr_atom : Format.formatter -> atom -> unit
val pr_formula : Format.formatter -> formula -> unit
val pr_num_subst :
  Format.formatter -> (Defs.var_name * (term * Defs.loc)) list -> unit
val pr_nsubst :
  Format.formatter -> (Defs.var_name * term) list -> unit

val term_no_parens : term -> bool
