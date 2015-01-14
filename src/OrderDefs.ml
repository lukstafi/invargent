(** Definitions for the order sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Aux
open Defs

let sort = Order_sort

type term =
  | Zero
  | Top
  | OVar of var_name
  | Succ of term

let rec fvs_term = function
  | Zero | Top -> VarSet.empty
  | OVar v -> VarSet.singleton v
  | Succ o -> fvs_term o

type atom =
  | Eq of term * term * Defs.loc
  | Leq of term * term * Defs.loc
  | EqMin of term * term * term * Defs.loc
  | MinLeq of term * term * term * Defs.loc
  | EqMax of term * term * term * Defs.loc
  | LeqMax of term * term * term * Defs.loc
type formula = atom list

let fvs_atom = function
  | Eq (t1, t2, _)
  | Leq (t1, t2, _) ->
    VarSet.union (fvs_term t1) (fvs_term t2)
  | EqMin (t1, t2, t3, _)
  | MinLeq (t1, t2, t3, _)
  | EqMax (t1, t2, t3, _)
  | LeqMax (t1, t2, t3, _) ->
    VarSet.union (fvs_term t1) (VarSet.union (fvs_term t2) (fvs_term t3))

let prim_constr_var = function
  | EqMin (OVar v, _, _, _)
  | MinLeq (_, OVar v, _, _)
  | EqMax (OVar v, _, _, _)
  | LeqMax (OVar v, _, _, _) -> Some v
  | _ -> None

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

let atom_loc = function
  | Eq (_, _, lc) | Leq (_, _, lc)
  | EqMin (_, _, _, lc) | MinLeq (_, _, _, lc)
  | EqMax (_, _, _, lc) | LeqMax (_, _, _, lc) -> lc

let replace_loc_atom loc = function
  | Eq (t1, t2, _) -> Eq (t1, t2, loc)
  | Leq (t1, t2, _) -> Leq (t1, t2, loc)
  | EqMin (t1, t2, t3, _) -> EqMin (t1, t2, t3, loc)
  | MinLeq (t1, t2, t3, _) -> MinLeq (t1, t2, t3, loc)
  | EqMax (t1, t2, t3, _) -> EqMax (t1, t2, t3, loc)
  | LeqMax (t1, t2, t3, _) -> LeqMax (t1, t2, t3, loc)

let replace_loc loc = List.map (replace_loc_atom loc)

let eq_atom a1 a2 =
  match a1, a2 with
  | Leq (t1, t2, _), Leq (t3, t4, _) -> t1=t3 && t2=t4
  | MinLeq (t1, t2, t3, _), MinLeq (t4, t5, t6, _)
  | LeqMax (t1, t2, t3, _), LeqMax (t4, t5, t6, _)
  | EqMin (t1, t2, t3, _), EqMin (t4, t5, t6, _)
  | EqMax (t1, t2, t3, _), EqMax (t4, t5, t6, _) -> t1=t4 && t2=t5 && t3=t6
  | Eq (t1, t2, _), Eq (t3, t4, _) -> t1=t3 && t2=t4 || t1=t4 && t2=t3
  | _ -> false

let formula_inter cnj1 cnj2 =
    List.filter (fun a -> List.exists (eq_atom a) cnj2) cnj1

let subformula phi1 phi2 =
  List.for_all (fun a1 -> List.exists (eq_atom a1) phi2) phi1

let rec iter_term_vars f = function
  | Zero | Top -> ()
  | OVar v -> f v
  | Succ o -> iter_term_vars f o


let subst_term unbox sb t =
  let rec aux = function
    | (Zero | Top) as i -> i
    | OVar v as t ->
      (try
         let t, lc = List.assoc v sb in
         unbox v lc t
       with Not_found -> t)
    | Succ o -> Succ (aux o) in
  aux t

let osubst_term sb t =
  let rec aux = function
    | (Zero | Top) as i -> i
    | OVar v as t ->
      (try fst (List.assoc v sb)
       with Not_found -> t)
    | Succ o -> Succ (aux o) in
  aux t

let hvsubst_term sb t =
  let rec aux = function
    | (Zero | Top) as i -> i
    | OVar v as t ->
      (try OVar (List.assoc v sb)
       with Not_found -> t)
    | Succ o -> Succ (aux o) in
  aux t

let rec term_size = function
  | Zero | Top | OVar _ -> 1
  | Succ o -> 1 + term_size o

let subst_atom unbox sb = function
  | Eq (t1, t2, loc) ->
    Eq (subst_term unbox sb t1, subst_term unbox sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (subst_term unbox sb t1, subst_term unbox sb t2, loc)
  | EqMin (t1, t2, t3, loc) ->
    EqMin (subst_term unbox sb t1, subst_term unbox sb t2,
           subst_term unbox sb t3, loc)
  | MinLeq (t1, t2, t3, loc) ->
    MinLeq (subst_term unbox sb t1, subst_term unbox sb t2,
            subst_term unbox sb t3, loc)
  | EqMax (t1, t2, t3, loc) ->
    EqMax (subst_term unbox sb t1, subst_term unbox sb t2,
           subst_term unbox sb t3, loc)
  | LeqMax (t1, t2, t3, loc) ->
    LeqMax (subst_term unbox sb t1, subst_term unbox sb t2,
            subst_term unbox sb t3, loc)

let osubst_atom sb = function
  | Eq (t1, t2, loc) ->
    Eq (osubst_term sb t1, osubst_term sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (osubst_term sb t1, osubst_term sb t2, loc)
  | EqMin (t1, t2, t3, loc) ->
    EqMin (osubst_term sb t1, osubst_term sb t2, osubst_term sb t3, loc)
  | MinLeq (t1, t2, t3, loc) ->
    MinLeq (osubst_term sb t1, osubst_term sb t2, osubst_term sb t3, loc)
  | EqMax (t1, t2, t3, loc) ->
    EqMax (osubst_term sb t1, osubst_term sb t2, osubst_term sb t3, loc)
  | LeqMax (t1, t2, t3, loc) ->
    LeqMax (osubst_term sb t1, osubst_term sb t2, osubst_term sb t3, loc)

let hvsubst_atom sb = function
  | Eq (t1, t2, loc) ->
    Eq (hvsubst_term sb t1, hvsubst_term sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (hvsubst_term sb t1, hvsubst_term sb t2, loc)
  | EqMin (t1, t2, t3, loc) ->
    EqMin (hvsubst_term sb t1, hvsubst_term sb t2, hvsubst_term sb t3, loc)
  | MinLeq (t1, t2, t3, loc) ->
    MinLeq (hvsubst_term sb t1, hvsubst_term sb t2, hvsubst_term sb t3, loc)
  | EqMax (t1, t2, t3, loc) ->
    EqMax (hvsubst_term sb t1, hvsubst_term sb t2, hvsubst_term sb t3, loc)
  | LeqMax (t1, t2, t3, loc) ->
    LeqMax (hvsubst_term sb t1, hvsubst_term sb t2, hvsubst_term sb t3, loc)

let atom_size = function
  | Eq (t1, t2, loc)
  | Leq (t1, t2, loc) -> term_size t1 + term_size t2 + 1
  | EqMin (t1, t2, t3, _)
  | MinLeq (t1, t2, t3, _)
  | EqMax (t1, t2, t3, _)
  | LeqMax (t1, t2, t3, _) ->
    term_size t1 + term_size t2 + term_size t3 + 1  

let formula_size = List.fold_left
    (fun s a -> s + atom_size a) 0

let iter_terms f = function
  | Eq (t1, t2, _)
  | Leq (t1, t2, _) -> f t1; f t2
  | EqMin (t1, t2, t3, _)
  | MinLeq (t1, t2, t3, _)
  | EqMax (t1, t2, t3, _)
  | LeqMax (t1, t2, t3, _) -> f t1; f t2; f t3

open Format

let rec pr_term ppf = function
  | Zero -> fprintf ppf "zero"
  | Top -> fprintf ppf "top"
  | OVar v -> fprintf ppf "%s" (var_str v)
  | Succ o -> fprintf ppf "succ %a" pr_term o

let rec term_no_parens = function
  | Zero | Top | OVar _ -> true
  | Succ o -> false

let rec taut_atom = function
  | Eq (Succ t1, Succ t2, lc) -> taut_atom (Eq (t1, t2, lc))
  | Leq (Succ t1, Succ t2, lc) -> taut_atom (Leq (t1, t2, lc))
  | EqMin (Succ t1, Succ t2, Succ t3, lc) ->
    taut_atom (EqMin (t1, t2, t3, lc))
  | EqMax (Succ t1, Succ t2, Succ t3, lc) ->
    taut_atom (EqMax (t1, t2, t3, lc))
  | MinLeq (Succ t1, Succ t2, Succ t3, lc) ->
    taut_atom (MinLeq (t1, t2, t3, lc))
  | LeqMax (Succ t1, Succ t2, Succ t3, lc) ->
    taut_atom (LeqMax (t1, t2, t3, lc))
  | Leq (t1, Succ t2, lc) -> taut_atom (Leq (t1, t2, lc))
  | MinLeq (t1, t2, Succ t3, lc) ->
    taut_atom (MinLeq (t1, t2, t3, lc))
  | LeqMax (t1, Succ t2, t3, lc) ->
    taut_atom (LeqMax (t1, t2, t3, lc))
  | LeqMax (t1, t2, Succ t3, lc) ->
    taut_atom (LeqMax (t1, t2, t3, lc))
  | Leq (Zero, _, _) -> true
  | Leq (_, Top, _) -> true
  | MinLeq (Zero, _, _, _) -> true
  | MinLeq (_, Zero, _, _) -> true
  | MinLeq (_, _, Top, _) -> true
  | LeqMax (Zero, _, _, _) -> true
  | LeqMax (_, Top, _, _) -> true
  | LeqMax (_, _, Top, _) -> true
  | Eq (t1, t2, _)
  | Leq (t1, t2, _) -> t1 = t2
  | EqMax (t1, t2, t3, _)
  | EqMin (t1, t2, t3, _) -> t1 = t2 && t2 = t3
  | MinLeq (t1, t2, t3, _) -> t1 = t3 || t2 = t3
  | LeqMax (t1, t2, t3, _) -> t1 = t2 || t1 = t3

let pr_atom ppf = function
  | Eq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_term t1 pr_term t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_term t1 pr_term t2
  | EqMin (t1, t2, t3, _) ->
    fprintf ppf "@[<2>%a@ =@ min @[(%a,@ %a)@]@]"
      pr_term t1 pr_term t2 pr_term t3
  | MinLeq (t1, t2, t3, _) ->
    fprintf ppf "@[<2>@[min (%a,@ %a)@]@ ≤@ %a@]"
      pr_term t1 pr_term t2 pr_term t3
  | EqMax (t1, t2, t3, _) ->
    fprintf ppf "@[<2>%a@ =@ max @[(%a,@ %a)@]@]"
      pr_term t1 pr_term t2 pr_term t3
  | LeqMax (t1, t2, t3, _) ->
    fprintf ppf "@[<2>%a@ ≤@ @[max (%a,@ %a)@]@]"
      pr_term t1 pr_term t2 pr_term t3

let pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms
  
let pr_num_subst ppf sb =
  pr_sep_list ";" (fun ppf (v,(t,_)) ->
    fprintf ppf "%s:=%a" (var_str v) pr_term t) ppf sb
  
let pr_nsubst ppf sb =
  pr_sep_list ";" (fun ppf (v,t) ->
    fprintf ppf "%s:=%a" (var_str v) pr_term t) ppf sb
