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

let rec has_var_term v = function
  | Cst _ -> false
  | Lin (_, _, v2) -> v = v2
  | Add cmb -> List.fold_left
                 (fun acc t -> acc || has_var_term v t) false cmb

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

let subformula phi1 phi2 =
  List.for_all (fun a1 -> List.exists (eq_atom a1) phi2) phi1

(* Small fractions keep their source spelling. Larger operations use exact
   rationals before converting the reduced result to source coefficients. *)
let small_component =
  let limit = 1 lsl ((Sys.word_size-3)/2) in
  fun n -> -limit <= n && n <= limit

let source_fraction q =
  let r = Num.ratio_of_num q in
  Big_int.int_of_big_int (Ratio.numerator_ratio r),
  Big_int.int_of_big_int (Ratio.denominator_ratio r)

let rational j k = Num.(div_num (num_of_int j) (num_of_int k))

let add_fraction j k m n =
  if small_component j && small_component k && small_component m && small_component n
  then j*n + m*k, k*n
  else source_fraction (Num.add_num (rational j k) (rational m n))

let scale_term j k t =
  let times m n =
    if small_component j && small_component k && small_component m && small_component n
    then m*j, n*k
    else source_fraction (Num.mult_num (rational j k) (rational m n)) in
  let scale make m n =
    (* The opposite of min_int needs one more unit than max_int. Its sum
       representation is available even inside a min/max argument. *)
    if j= -1 && k=1 && m=min_int then Add [make max_int n;make 1 n]
    else let a,b = times m n in make a b in
  let rec aux = function
    | Cst (m,n) -> scale (fun a b -> Cst (a,b)) m n
    | Lin (m,n,v) -> scale (fun a b -> Lin (a,b,v)) m n
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
         let t, lc = VarMap.find v sb in
         scale_term j k (unbox v lc t)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let nsubst_term sb t =
  let rec aux = function
    | Cst _ as i -> i
    | Lin (j, k, v) as t ->
      (try
         scale_term j k (VarMap.find v sb)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let hvsubst_term sb t =
  let rec aux = function
    | Cst _ as i -> i
    | Lin (j, k, v) as t ->
      (try Lin (j, k, VarMap.find v sb)
       with Not_found -> t)
    | Add cmb -> Add (List.map aux cmb) in
  aux t

let rec term_size = function
  | Cst _
  | Lin _ -> 1
  | Add cmb -> List.fold_left (fun acc t -> acc+term_size t) 1 cmb

let add t1 t2 =
  match t1, t2 with
  | Lin (j,m,v1), Lin (k,n,v2) when v1=v2 ->
    (try let a,b = add_fraction j m k n in Lin (a,b,v1)
     with Failure msg when msg="int_of_big_int" -> Add [t1;t2])
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
    List.fold_left (fun a t ->
        let b = denom t in
        if small_component a && small_component b then lcm a b
        else Big_int.(int_of_big_int (lcm_big_int (big_int_of_int a) (big_int_of_int b)))) 1 cmb

open Format

let rec pr_term ppf = function
  | Cst (m, 1) -> fprintf ppf "%d" m
  | Cst (m, n) -> fprintf ppf "(%d/%d)" m n
  | Lin (1, 1, v) -> fprintf ppf "%s" (var_str v)
  | Lin (-1, 1, v) -> fprintf ppf "-%s" (var_str v)
  | Lin (m, 1, v) -> fprintf ppf "%d %s" m (var_str v)
  | Lin (m, n, v) -> fprintf ppf "(%d/%d) %s" m n (var_str v)
  | Add [] -> fprintf ppf "0"
  | Add cmb -> fprintf ppf "%a" (pr_sep_list " +" pr_term) cmb

let flatten t =
  let rec flat (vars, (j,k as cst) as acc) = function
    | Add sum -> List.fold_left flat acc sum
    | Cst (j2,k2) -> vars, add_fraction j k j2 k2
    | Lin (j,k,v) -> (j,k,v)::vars, cst in
  flat ([], (0,1)) t

let equal_to_cst =
  let rec flatten = function
    | Add [t] -> flatten t
    | t -> t in
 function
  | Eq (t1, t2, _) ->
    (match flatten t1, flatten t2 with
     | Lin _, Cst _
     | Cst _, Lin _ -> true
     | _ -> false)
  | _ -> false

(* Simplified, i.e. non-normalizing, detection of directed opti atoms. *)
let factor_opti t1 t2 =
  let unpack (j,k,v) = Lin (j,k,v) in
  let uncst (j,k) = if j=0 then [] else [Cst (j,k)] in
  let negate j = if j=min_int then raise Not_found else -j in
  let negterms = List.map (fun (j,k,v) -> negate j,k,v) in
  let negcst (j,k) = negate j,k in
  try
    let ts1, cst1 = flatten t1
    and ts2, cst2 = flatten t2 in
    let (j,k,v as i) = List.find (fun (j,k,_ as term) ->
        j <> 0 && k <> 0 && j <> min_int && k <> min_int && List.mem term ts2) ts1 in
    let vs1, ts1 = List.partition ((=) i) ts1
    and vs2, ts2 = List.partition ((=) i) ts2 in
    let ts1 = List.tl vs1 @ ts1 and ts2 = List.tl vs2 @ ts2 in
    let s = (j > 0) = (k > 0) in
    let ts1, ts2, cst1, cst2 =
      if not s then ts1, ts2, cst1, cst2
      else negterms ts1, negterms ts2, negcst cst1, negcst cst2 in
    Some ((abs j, abs k, v), s, Add (map_append unpack ts1 (uncst cst1)),
          Add (map_append unpack ts2 (uncst cst2)))
  with Not_found -> None
     | Failure msg when msg="int_of_big_int" -> None

let direct_opti t1 t2 =
  match factor_opti t1 t2 with
  | None -> None
  | Some ((j,k,v), sign, left, right) ->
      let g = gcd j k in
      let divide = scale_term (k/g) (j/g) in
      (try Some (v, sign, divide left, divide right)
       with Failure msg when msg="int_of_big_int" -> None)

let prim_constr_var = function
  | Opti (t1, t2, _)
  | Subopti (t1, t2, _) ->
    (match direct_opti t1 t2 with
     | Some (v, _, _, _) -> Some v
     | None -> None)
  | _ -> None

let taut_atom_or_undir_opti = function
  | Eq (t1, t2, _) -> t1 = t2
  | Leq (t1, t2, _) -> t1 = t2
  | Subopti (t1, t2, _)
  | Opti (t1, t2, _) -> direct_opti t1 t2 = None

let pr_atom ppf = function
  | Eq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ =@ %a@]" pr_term t1 pr_term t2
  | Leq (t1, t2, _) ->
    fprintf ppf "@[<2>%a@ ≤@ %a@]" pr_term t1 pr_term t2
  | Opti (t1, t2, _) ->
    (match factor_opti t1 t2 with
    | None ->
      fprintf ppf "@[<2>min|max@ (%a,@ %a)@]" pr_term t1 pr_term t2
    | Some ((j,k,v), true, t1, t2) ->
      fprintf ppf "@[<2>%a=min@ (%a,@ %a)@]" pr_term (Lin (j,k,v))
        pr_term t1 pr_term t2
    | Some ((j,k,v), false, t1, t2) ->
      fprintf ppf "@[<2>%a=max@ (%a,@ %a)@]" pr_term (Lin (j,k,v))
        pr_term t1 pr_term t2)
  | Subopti (t1, t2, _) ->
    match factor_opti t1 t2 with
    | None ->
      fprintf ppf "@[<2>min||max@ (%a,@ %a)@]" pr_term t1 pr_term t2
    | Some ((j,k,v), true, t1, t2) ->
      fprintf ppf "@[<2>%a≤max@ (%a,@ %a)@]" pr_term (Lin (j,k,v))
        pr_term t1 pr_term t2
    | Some ((j,k,v), false, t1, t2) ->
      fprintf ppf "@[<2>min@ (%a,@ %a)≤%a@]"
        pr_term t1 pr_term t2 pr_term (Lin (j,k,v))

let pr_formula ppf atoms =
  pr_sep_list " ∧" pr_atom ppf atoms
  
let pr_num_subst ppf sb =
  pr_sep_list ";" (fun ppf (v,(t,_)) ->
    fprintf ppf "%s:=%a" (var_str v) pr_term t) ppf
    (varmap_to_assoc sb)
  
let pr_nsubst ppf sb =
  pr_sep_list ";" (fun ppf (v,t) ->
    fprintf ppf "%s:=%a" (var_str v) pr_term t) ppf
    (varmap_to_assoc sb)

let term_no_parens = function
  | Lin (1, 1, _) | Cst _ -> true
  | _ -> false
