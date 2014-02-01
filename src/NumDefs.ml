(** Definitions for the numeric sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Aux
open Defs

let sort = Num_sort

type term =
  | Cst of int * int                  (** [Cst (i,j)] = $(i/j)$ *)
  | Lin of int * int * var_name       (** [Lin [i,j,n]] = $(i/j)*n$ *)
  | Add of term list

let rec fvs_term = function
  | Cst _ -> VarSet.empty
  | Lin (_, _, v) -> VarSet.singleton v
  | Add cmb -> vars_of_map fvs_term cmb

type atom =
  | Eq of term * term * Defs.loc
  | Leq of term * term * Defs.loc
  | Opti of term * term * Defs.loc
  | Subopti of term * term * Defs.loc
type formula = atom list

let fvs_atom = function
  | Eq (t1, t2, _)
  | Leq (t1, t2, _)
  | Opti (t1, t2, _)
  | Subopti (t1, t2, _) -> VarSet.union (fvs_term t1) (fvs_term t2)

let fvs_formula phi =
  List.fold_left VarSet.union VarSet.empty (List.map fvs_atom phi)

let atom_loc = function
  | Eq (_, _, lc) | Leq (_, _, lc) | Opti (_, _, lc)
  | Subopti (_, _, lc) -> lc

let replace_loc_atom loc = function
  | Eq (t1, t2, _) -> Eq (t1, t2, loc)
  | Leq (t1, t2, _) -> Leq (t1, t2, loc)
  | Opti (t1, t2, _) -> Opti (t1, t2, loc)
  | Subopti (t1, t2, _) -> Subopti (t1, t2, loc)

let replace_loc loc = List.map (replace_loc_atom loc)

let eq_atom a1 a2 =
  match a1, a2 with
  | Leq (t1, t2, _), Leq (t3, t4, _) -> t1=t3 && t2=t4
  | Eq (t1, t2, _), Eq (t3, t4, _)
  | Opti (t1, t2, _), Opti (t3, t4, _) -> t1=t3 && t2=t4 || t1=t4 && t2=t3
  | Subopti (t1, t2, _), Subopti (t3, t4, _) ->
    t1=t3 && t2=t4 || t1=t4 && t2=t3
  | _ -> false

let formula_inter cnj1 cnj2 =
    List.filter (fun a -> List.exists (eq_atom a) cnj2) cnj1

let scale_term j k t =
  let rec aux = function
    | Cst (m, n) -> Cst (m*j, n*k)
    | Lin (m, n, v) -> Lin (m*j, n*k, v)
    | Add cmb -> Add (List.map aux cmb) in
  if j=1 && k=1 then t else aux t

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
  | Cst (m, 1) -> fprintf ppf "%d" m
  | Cst (m, n) -> fprintf ppf "(%d/%d)" m n
  | Lin (1, 1, v) -> fprintf ppf "%s" (var_str v)
  | Lin (-1, 1, v) -> fprintf ppf "-%s" (var_str v)
  | Lin (m, 1, v) -> fprintf ppf "%d %s" m (var_str v)
  | Lin (m, n, v) -> fprintf ppf "(%d/%d) %s" m n (var_str v)
  | Add cmb -> fprintf ppf "%a" (pr_sep_list " +" pr_term) cmb

(* Simplified, i.e. non-normalizing, detection of directed opti atoms. *)
let direct_opti t1 t2 =
  let rec flat (vars, (j,k as cst) as acc) = function
    | Add sum -> List.fold_left flat acc sum
    | Cst (j2,k2) -> vars, (j2*k+j*k2, k*k2)
    | Lin (j,k,v) -> (j,k,v)::vars, cst in
  let unpack (j,k,v) = Lin (j,k,v) in
  let uncst (j,k) = if j=0 then [] else [Cst (j,k)] in
  let negate = List.map (fun (j,k,v) -> ~-j,k,v) in
  let negcst (j,k) = ~-j,k in
  try
    let ts1, cst1 = flat ([], (0,1)) t1
    and ts2, cst2 = flat ([], (0,1)) t2 in
    let (j,k,v as i) = List.find (fun e -> List.mem e ts2) ts1 in
    let vs1, ts1 = List.partition ((=) i) ts1
    and vs2, ts2 = List.partition ((=) i) ts2 in
    let ts1 = List.tl vs1 @ ts1 and ts2 = List.tl vs2 @ ts2 in
    let s = j*k>0 in
    let ts1, ts2, cst1, cst2 =
      if not s then ts1, ts2, cst1, cst2
      else negate ts1, negate ts2, negcst cst1, negcst cst2 in
    Some (v, s, Add (map_append unpack ts1 (uncst cst1)),
          Add (map_append unpack ts2 (uncst cst2)))
  with Not_found -> None

let taut_atom_or_undir_opti = function
  | Eq (t1, t2, _) -> t1 = t2
  | Leq (t1, t2, _) -> t1 = t2
  | Subopti (t1, t2, _)
  | Opti (t1, t2, _) ->
    match direct_opti t1 t2 with
    | None -> true
    | Some (v, s, Add [], _) -> true
    | Some (v, s, _, Add []) -> true
    | Some (v, s, Lin (1, 1, v2), _) when v = v2 -> true
    | Some (v, s, _, Lin (1, 1, v2)) when v = v2 -> true
    | _ -> false

let pr_atom ppf = function
  | Eq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_term t1 pr_term t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_term t1 pr_term t2
  | Opti (t1, t2, _) ->
    (match direct_opti t1 t2 with
    | None ->
      fprintf ppf "@[<2>min|max@ (%a,@ %a)@]" pr_term t1 pr_term t2
    | Some (v, true, t1, t2) ->
      fprintf ppf "@[<2>%s=min@ (%a,@ %a)@]"(var_str v)
        pr_term t1 pr_term t2
    | Some (v, false, t1, t2) ->
      fprintf ppf "@[<2>%s=max@ (%a,@ %a)@]"(var_str v)
        pr_term t1 pr_term t2)
  | Subopti (t1, t2, _) ->
    match direct_opti t1 t2 with
    | None ->
      fprintf ppf "@[<2>min||max@ (%a,@ %a)@]" pr_term t1 pr_term t2
    | Some (v, true, t1, t2) ->
      fprintf ppf "@[<2>%s≤max@ (%a,@ %a)@]"(var_str v)
        pr_term t1 pr_term t2
    | Some (v, false, t1, t2) ->
      fprintf ppf "@[<2>min@ (%a,@ %a)≤%s@]"
        pr_term t1 pr_term t2 (var_str v)

let pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms
  
let pr_num_subst ppf sb =
  pr_sep_list ";" (fun ppf (v,(t,_)) ->
    fprintf ppf "%s:=%a" (var_str v) pr_term t) ppf sb

let term_no_parens = function
  | Lin (1, 1, _) | Cst _ -> true
  | _ -> false
