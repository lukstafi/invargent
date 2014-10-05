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
    VarSet.union (fvs_term t1) (fvs_term t2) (fvs_term t3)

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
  | MinLeq (t1, t2, _) -> MinLeq (t1, t2, t3, loc)
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
  | Cst _ -> ()
  | Lin (_, _, v) -> f v
  | Add cmb -> List.iter (iter_term_vars f) cmb


let subst_term unbox sb t =
  let rec aux = function
    | Cst _ as i -> i
    | Lin (j, k, v) as t ->
      (try
         let t, lc = List.assoc v sb in
         scale_term j k (unbox v lc t)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let nsubst_term sb t =
  let rec aux = function
    | Cst _ as i -> i
    | Lin (j, k, v) as t ->
      (try
         scale_term j k (List.assoc v sb)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let hvsubst_term sb t =
  let rec aux = function
    | Cst _ as i -> i
    | Lin (j, k, v) as t ->
      (try Lin (j, k, List.assoc v sb)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let rec term_size = function
  | Cst _
  | Lin _ -> 1
  | Add cmb -> List.fold_left (fun acc t -> acc+term_size t) 1 cmb

let add t1 t2 =
  match t1, t2 with
  | Lin (j,m,v1), Lin (k,n,v2) when v1=v2 -> Lin (j*n + k*m, m*n, v1)
  | Add ds, Add es -> Add (ds @ es)
  | Add es, t | t, Add es -> Add (t::es)
  | _ -> Add [t1; t2]

let diff t1 t2 = add t1 (scale_term (-1) 1 t2)

let subst_atom unbox sb = function
  | Eq (t1, t2, loc) ->
    Eq (subst_term unbox sb t1, subst_term unbox sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (subst_term unbox sb t1, subst_term unbox sb t2, loc)
  | Opti (t1, t2, loc) ->
    Opti (subst_term unbox sb t1, subst_term unbox sb t2, loc)
  | Subopti (t1, t2, loc) ->
    Subopti (subst_term unbox sb t1, subst_term unbox sb t2, loc)

let nsubst_atom sb = function
  | Eq (t1, t2, loc) ->
    Eq (nsubst_term sb t1, nsubst_term sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (nsubst_term sb t1, nsubst_term sb t2, loc)
  | Opti (t1, t2, loc) ->
    Opti (nsubst_term sb t1, nsubst_term sb t2, loc)
  | Subopti (t1, t2, loc) ->
    Subopti (nsubst_term sb t1, nsubst_term sb t2, loc)

let hvsubst_atom sb = function
  | Eq (t1, t2, loc) ->
    Eq (hvsubst_term sb t1, hvsubst_term sb t2, loc)
  | Leq (t1, t2, loc) ->
    Leq (hvsubst_term sb t1, hvsubst_term sb t2, loc)
  | Opti (t1, t2, loc) ->
    Opti (hvsubst_term sb t1, hvsubst_term sb t2, loc)
  | Subopti (t1, t2, loc) ->
    Subopti (hvsubst_term sb t1, hvsubst_term sb t2, loc)

let atom_size = function
  | Eq (t1, t2, loc)
  | Leq (t1, t2, loc)
  | Opti (t1, t2, loc)
  | Subopti (t1, t2, loc) ->
    term_size t1 + term_size t2 + 1  

let formula_size = List.fold_left
    (fun s a -> s + atom_size a) 0

let iter_terms f = function
  | Eq (t1, t2, loc)
  | Leq (t1, t2, loc)
  | Opti (t1, t2, loc)
  | Subopti (t1, t2, loc) -> f t1; f t2

let rec denom = function
  | Cst (_, d) -> d
  | Lin (_, d, _) -> d
  | Add cmb ->
    List.fold_left lcm 1 (List.map denom cmb)

open Format

let rec pr_term ppf = function
  | Zero -> fprintf ppf "zero"
  | Top -> fprintf ppf "top"
  | OVar v -> fprintf ppf "%s" (var_str v)
  | Succ o -> fprintf ppf "succ %a" pr_term o

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
