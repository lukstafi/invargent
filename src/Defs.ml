(** Definitions indispensable in every sort for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let nodeadcode = ref true
let force_nodeadcode = ref false
let deadcode_flag = ref false
let guess_from_postcond = ref true

open Lexing
open Aux

type loc = {beg_pos : position; end_pos : position}
let dummy_loc =
  {beg_pos = dummy_pos; end_pos = dummy_pos}

exception Report_toplevel of string * loc option

let min_pos p1 p2 =
  if p1.pos_cnum <> -1 && p1.pos_cnum < p2.pos_cnum then p1 else p2
let max_pos p1 p2 =
  if p2.pos_cnum < p1.pos_cnum then p1 else p2
let loc_union ?loc loc1 loc2 =
  match loc with
    | Some loc -> loc
    | None ->
      if loc1 = dummy_loc then loc2
      else if loc2 = dummy_loc then loc1
      else
	{beg_pos = min_pos loc1.beg_pos loc2.beg_pos;
	 end_pos = max_pos loc1.end_pos loc2.end_pos}
let loc_tighter loc1 loc2 =
  if loc1.end_pos.pos_cnum - loc1.beg_pos.pos_cnum <
    loc2.end_pos.pos_cnum - loc2.beg_pos.pos_cnum &&
    loc1.beg_pos.pos_cnum <> -1
  then loc1 else loc2
let interloc loc1 loc2 =
  not (loc1.end_pos.pos_cnum < loc2.beg_pos.pos_cnum ||
         loc1.beg_pos.pos_cnum > loc2.end_pos.pos_cnum)

type sort = Num_sort | Type_sort | Order_sort

let sort_str = function
  | Num_sort -> "num"
  | Type_sort -> "type"
  | Order_sort -> "order"


(** Type variables (and constants) remember their sort. Sort
    inference is performed on user-supplied types and constraints. *)
type var_name =
| VNam of sort * string
| VId of sort * int

let delta = VId (Type_sort, -1)
let delta' = VId (Type_sort, -2)

let var_sort = function VNam (s,_) -> s | VId (s,_) -> s
let var_str = function
  | VNam (_,v) -> v
  | VId _ as d when d = delta -> "δ"
  | VId _ as d when d = delta' -> "δ'"
  | VId (s,i) -> Char.escaped (sort_str s).[0]^string_of_int i

module VarSet =
    Set.Make (struct type t = var_name let compare = Pervasives.compare end)
let vars_of_list l =
  List.fold_right VarSet.add l VarSet.empty
let add_vars l vs =
  List.fold_right VarSet.add l vs
let no_vs = VarSet.empty
let vars_of_map f l =
  List.fold_left (fun acc x -> VarSet.union acc (f x)) VarSet.empty l
let var_subset vs1 vs2 =
  VarSet.for_all (fun v -> VarSet.mem v vs2) vs1

module VarMap =
  Map.Make (struct type t = var_name let compare = Pervasives.compare end)
let varmap_of_assoc l =
  List.fold_right (uncurry VarMap.add) l VarMap.empty
let varmap_to_assoc l =
  VarMap.fold (fun v e acc -> (v, e)::acc) l []
let add_to_varmap l vs =
  List.fold_right (uncurry VarMap.add) l vs
let add_map_to_varmap f l vs =
  List.fold_right (uncurry VarMap.add % f) l vs
let empty_vmap = VarMap.empty
let concat_varmap f vmap =
  VarMap.fold
    (fun v x acc -> List.rev_append (f v x) acc) vmap []
let varmap_merge sb1 sb2 =
  VarMap.merge
    (fun _ -> function Some _ as sv1 -> fun _ -> sv1
                     | None -> fun sv2 -> sv2)
    sb1 sb2
let varmap_concat sbs =
  List.fold_left varmap_merge VarMap.empty sbs
let varmap_domain sb =
  VarMap.fold (fun v _ vs -> VarSet.add v vs) sb VarSet.empty
let varmap_codom sb =
  VarMap.fold (fun _ e acc -> e::acc) sb []

(** {2 Quantification} *)

type var_scope =
| Left_of | Same_params | Same_quant | Right_of

type quant_ops = {
  cmp_v : var_name -> var_name -> var_scope;
  uni_v : var_name -> bool;
  same_as : var_name -> var_name -> unit;
  upward_of : var_name -> var_name -> bool;
}

let empty_q = {
  cmp_v = (fun _ _ -> Same_quant);
  uni_v = (fun _ -> false);
  same_as = (fun _ _ -> ());
  upward_of = (fun _ _ -> false);
}
  

let var_scope_str = function
| Left_of -> "left_of"
| Same_quant -> "same_quant"
| Same_params -> "same_params"
| Right_of -> "right_of"


exception Omit
(* Linearization of quantifiers is a problem here because we want "<>
   Incomparable" (before prenexization) rather than "<> Same_quant". *)
let crosses_xparams ~cmp_v ~bvs cvs =
  try
    let pvs = List.filter
        (fun v -> VarSet.mem v bvs) (VarSet.elements cvs) in
    triangle_iter
      (* Same_params is OK. *)
      (fun v1 v2 -> if cmp_v v1 v2 = Same_quant then raise Omit)
      pvs;
    false
  with Omit -> true


(** {2 Printing} *)
let current_file_name = ref ""

open Format

let pr_loc_pos_only ppf loc =
  fprintf ppf "@[<1>:%d@,-%d:@]"
    loc.beg_pos.pos_cnum loc.end_pos.pos_cnum

let pr_loc_short ppf loc =
  let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
  fprintf ppf "@[<1>%s:%d:%d@,-%d:I:@]"
  !current_file_name loc.beg_pos.pos_lnum clbeg
  (clbeg+(loc.end_pos.pos_cnum - loc.beg_pos.pos_cnum))

let pr_loc_long ppf loc =
  if loc = dummy_loc then fprintf ppf "@[<0>{no@ loc}@]" else
    let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
    fprintf ppf "@[<2>File@ \"%s\",@ line@ %d,@ characters@ %d-%d:@]"
      !current_file_name loc.beg_pos.pos_lnum clbeg
      (clbeg+(loc.end_pos.pos_cnum - loc.beg_pos.pos_cnum))

let pr_loc_emb ppf loc =
  let clbeg = loc.beg_pos.pos_cnum - loc.beg_pos.pos_bol in
  let clend = loc.end_pos.pos_cnum - loc.end_pos.pos_bol in
  fprintf ppf "@[<1>{%d:%d@,-%d:%d}@]"
    loc.beg_pos.pos_lnum clbeg loc.end_pos.pos_lnum clend

let pr_loc ppf loc = pr_loc_long ppf loc

let pr_tyvar ppf v = pp_print_string ppf (var_str v)

let pr_vars ppf vs =
  pr_sep_list "," pr_tyvar ppf (VarSet.elements vs)
