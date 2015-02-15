(** General purpose auxiliary functions for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let flip f a b = f b a
let uncurry f (a, b) = f a b

let (%) f g x = f (g x)
let (%>) f g x = g (f x)
let (|>) x f = f x

let rec gcd a b =
  if b > a then gcd b a
  else if b = 0 then a
  else gcd b (a mod b)

let lcm a b = (a * b) / gcd a b

let lcm_big_int a b =
  Big_int.(div_big_int (mult_big_int a b) (gcd_big_int a b))

module Ints = Set.Make
  (struct type t = int let compare x y = x - y end)
let add_ints nvs vs =
  List.fold_left (fun vs nv -> Ints.add nv vs) vs nvs
let ints_of_list nvs =
  add_ints nvs Ints.empty

module Strings =
    Set.Make (struct type t = string let compare = Pervasives.compare end)
let strings_of_list l =
  List.fold_right Strings.add l Strings.empty
let add_strings l vs =
  List.fold_right Strings.add l vs

let order_key l = List.sort (fun (a,_) (b,_) -> compare a b) l

let unique_sorted ?(cmp = Pervasives.compare) l =
  let rec idemp acc = function
    | e1::(e2::_ as tl) when cmp e1 e2 = 0 -> idemp acc tl
    | e::tl -> idemp (e::acc) tl
    | [] -> acc in
  idemp [] (List.sort (fun x y -> - (cmp x y)) l)

let is_unique l =
  let rec idemp = function
    | e1::(e2::_) when e1 = e2 -> false
    | e::tl -> idemp tl
    | [] -> true in
  idemp (List.sort Pervasives.compare l)

let fold_map f acc l =
  let rec aux acc res =
    function
    | [] -> acc, List.rev res
    | hd::tl ->
      let acc, hd = f acc hd in aux acc (hd::res) tl in
  aux acc [] l

let rev_fold_map2 f acc l1 l2 =
  let rec aux acc res =
    function
    | [], [] -> acc, res
    | hd1::tl1, hd2::tl2 ->
      let acc, hd = f acc hd1 hd2 in aux acc (hd::res) (tl1, tl2)
    | _ -> assert false in
  aux acc [] (l1, l2)

let one_out l =
  let rec aux acc lhs = function
    | [] -> List.rev acc
    | a::rhs -> aux ((a, List.rev_append lhs rhs)::acc) (a::lhs) rhs in
  aux [] [] l

let rec list_make_n e n =
  if n <= 0 then [] else e :: list_make_n e (n-1)

let concat_map f l =
  let rec cmap_f accu = function
    | [] -> accu
    | a::l -> cmap_f (List.rev_append (f a) accu) l
  in
  List.rev (cmap_f [] l)

let concat_map2 f l1 l2 =
  let rec cmap_f accu = function
    | [], [] -> accu
    | a1::l1, a2::l2 -> cmap_f (List.rev_append (f a1 a2) accu) (l1, l2)
    | _ -> invalid_arg "concat_map2" in
  List.rev (cmap_f [] (l1, l2))

let rec concat_fold f a = function
  | [] -> [a]
  | x::xs -> 
    concat_map (fun a' -> concat_fold f a' xs) (f x a)

let map_some f l =
  let rec maps_f accu = function
    | [] -> accu
    | a::l -> maps_f (match f a with None -> accu
	| Some r -> r::accu) l
  in
  List.rev (maps_f [] l)

let mapi_some f l =
  let rec maps_f accu i = function
    | [] -> accu
    | a::l -> maps_f (match f i a with None -> accu
	| Some r -> r::accu) (i+1) l
  in
  List.rev (maps_f [] 0 l)

let map_some_append f l postfix =
  let rec maps_f = function
    | [] -> postfix
    | a::l ->
      match f a with
      | None -> maps_f l
      | Some r -> r::maps_f l in
  maps_f l

let map_some2 f l1 l2 =
  let rec maps_f accu = function
    | ([], []) -> accu
    | a1::l1, a2::l2 -> maps_f (match f a1 a2 with None -> accu
	| Some r -> r::accu) (l1, l2)
    | _, _ -> invalid_arg "Aux.map_some2"
  in
  List.rev (maps_f [] (l1, l2))

let split_map f l =
  let rec map_f xs ys = function
    | [] -> List.rev xs, List.rev ys
    | a::l ->
      let x, y = f a in
      map_f (x::xs) (y::ys) l in
  map_f [] [] l

let list_some = function
  | Some a -> [a]
  | None -> []

let list_some_list = function
  | Some a -> a
  | None -> []

let unsome = function None -> raise Not_found | Some e -> e

let array_mapi_some f a =
  let r = Array.mapi f a in
  let rl = ref (Array.length r) in
  for i=0 to Array.length a - 1 do
    if r.(i) = None then decr rl
  done;
  if !rl = 0 then [||]
  else
    let pos = ref 0 in
    while r.(!pos) = None do incr pos done;
    let res = Array.create !rl (unsome r.(!pos)) in
    incr pos;
    for i=1 to !rl -1 do
      while r.(!pos) = None do incr pos done;
      res.(i) <- unsome r.(!pos); incr pos
    done;
    res

let find_map f l =
  let rec aux = function
    | [] -> None
    | a::l ->
      match f a with None -> aux l
	| Some _ as ans -> ans in
  aux l

let find_some f l =
  let rec aux = function
    | [] -> raise Not_found
    | a::l ->
      match f a with None -> aux l
	| Some ans -> ans in
  aux l

let map_upto postfix f l =
  let rec aux = function
    | [] -> []
    | l when l == postfix -> l
    | a::l -> f a :: aux l in
  aux l

let map_append f l postfix =
  let rec aux = function
    | [] -> postfix
    | a::l -> f a :: aux l in
  aux l

let split3 l =
  let rec aux l1 l2 l3 = function
    | [] -> List.rev l1, List.rev l2, List.rev l3
    | (e1,e2,e3)::tl -> aux (e1::l1) (e2::l2) (e3::l3) tl in
  aux [] [] [] l

let flat2 l =
  List.fold_left (fun acc (x,y) -> x::y::acc) [] l

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thr3 (_,_,c) = c

let map_fst f (a, b) = f a, b
let map_snd f (a, b) = a, f b

let product l =
  List.fold_left (fun prod set -> concat_map
    (fun el -> List.rev (List.rev_map (fun tup ->  el::tup) prod))
    set) [[]] (List.rev l) 

let product_iter f l =
  let rec aux tup = function
    | [] -> f (List.rev tup)
    | hd::tl -> List.iter (fun e -> aux (e::tup) tl) hd in
  aux [] l

let triangle l =
  let rec aux acc = function
    | [] -> acc
    | e::l -> aux (List.map (fun d -> e,d) l @ acc) l in
  aux [] l

let triangle_iter f l =
  let rec aux = function
    | [] -> ()
    | e::l -> List.iter (f e) l; aux l in
  aux l

let transpose_lists lls =
  let rec aux acc = function
    | [] -> List.map List.rev acc
    | hd::tl ->
        aux (List.map2 (fun e col -> e::col) hd acc) tl in
  match lls with
    | [] -> []
    | hd::tl ->
        aux (List.map (fun e->[e]) hd) tl

let minimal ~less l =
  let rec aux acc = function
    | [] -> acc
    | e::l ->
      if List.exists (flip less e) l || List.exists (flip less e) acc
      then aux acc l
      else aux (e::acc) l in
  aux [] l

let maximum ~leq l =
  let rec aux acc = function
    | [] -> acc
    | e::l -> if leq e acc then aux acc l else aux e l in
  aux (List.hd l) (List.tl l)

let sorted_diff xs ys =
  let rec aux acc = function
    | [], _ -> acc
    | xs, [] -> List.rev_append xs acc
    | (x::xs' as xs), (y::ys' as ys) ->
      let c = Pervasives.compare x y in
      if c = 0 then aux acc (xs', ys')
      else if c < 0 then aux (x::acc) (xs', ys)
      else aux acc (xs, ys') in
  List.rev (aux [] (xs, ys))

let sorted_put cmp e l =
  let rec aux acc = function
    | [] -> List.rev (e::acc)
    | hd::tl as l ->
      let c = cmp e hd in
      if c < 0 then List.rev_append (e::acc) l
      else if c = 0 then List.rev_append acc l
      else aux (e::acc) tl in
  aux [] l

let merge cmp l1 l2 =
  let rec aux acc = function
    | [], l | l, [] -> List.rev_append acc l
    | e1::tl1, (e2::_ as l2) when cmp e1 e2 <= 0 ->
      aux (e1::acc) (tl1, l2)
    | l1, e2::tl2 ->
      aux (e2::acc) (l1, tl2) in
  aux [] (l1, l2)

let inter_merge (type a) (type b) (type c)
    (cmp : a -> b -> int) (f : a -> b -> c)
    (l1 : a list) (l2 : b list) : c list =
  let rec aux acc = function
    | [], l -> List.rev acc
    | l, [] -> List.rev acc
    | e1::tl1 as l1, (e2::tl2 as l2) ->
      let c = cmp e1 e2 in
      if c = 0 then aux (f e1 e2::acc) (tl1, tl2)
      else if c < 0 then aux acc (tl1, l2)
      else aux acc (l1, tl2) in
  aux [] (l1, l2)

let union_merge (type a)
    (cmp : a -> a -> int) (f : a -> a -> a)
    (l1 : a list) (l2 : a list) : a list =
  let rec aux acc = function
    | [], l -> List.rev_append acc l
    | l, [] -> List.rev_append acc l
    | e1::tl1 as l1, (e2::tl2 as l2) ->
      let c = cmp e1 e2 in
      if c = 0 then aux (f e1 e2::acc) (tl1, tl2)
      else if c < 0 then aux (e1::acc) (tl1, l2)
      else aux (e2::acc) (l1, tl2) in
  aux [] (l1, l2)

let union_merge_f (type a) (type b) (type c)
    (cmp : a -> b -> int) (f : a -> b -> c) (g : a  -> c) (h : b -> c)
    (l1 : a list) (l2 : b list) : c list =
  let rec aux acc = function
    | [], l -> List.rev_append (List.map h l) acc
    | l, [] -> List.rev_append (List.map g l) acc
    | e1::tl1 as l1, (e2::tl2 as l2) ->
      let c = cmp e1 e2 in
      if c = 0 then aux (f e1 e2::acc) (tl1, tl2)
      else if c < 0 then aux (g e1::acc) (tl1, l2)
      else aux (h e2::acc) (l1, tl2) in
  aux [] (l1, l2)

let list_inter a b = List.filter (fun e -> List.mem e b) a
let list_interq a b = List.filter (fun e -> List.memq e b) a
let list_diff a b = List.filter (fun e -> not (List.mem e b)) a
let list_remove a b = List.filter (fun e -> e <> a) b

let replace_assocs ~repl l = List.map
  (fun (k,_ as kv) -> try k, List.assoc k repl with Not_found -> kv)
  l

let rec update_assoc k0 v0 f = function
  | [] -> [k0, f v0]
  | (k,v)::l when k=k0 -> (k, f v)::l
  | kv::l -> kv::update_assoc k0 v0 f l
  

let bind_opt t f =
  match t with
  | None -> None
  | Some t -> f t

let map_opt t f =
  match t with
  | None -> None
  | Some t -> Some (f t)

let default v0 f v =
  match v with None -> v0 | Some v -> f v

let map_reduce ~cmp_k ?cmp ?mapf redf red0 l =
  let cmp = match cmp with
    | Some cmp -> cmp
    | None -> fun (x,_) (y,_) -> cmp_k x y in
  let l = match mapf with None -> l | Some f -> List.map f l in
  match List.sort cmp l with
      | [] -> []
      | (k0, v0)::tl ->
        let k0, vs, l =
          List.fold_left (fun (k0, vs, l) (kn, vn) ->
	    if cmp_k k0 kn = 0 then k0, vn::vs, l
            else kn, [vn], (k0,vs)::l)
	    (k0, [v0], []) tl in
        List.rev_map (fun (k,vs) -> k, List.fold_left redf red0 vs)
          ((k0,vs)::l)

let map_reduce_def ?mapf redf red0 l =
  map_reduce ~cmp_k:compare
    ?mapf redf red0 l

let collect ?(cmp_k=fun x y -> compare x y) ?cmp l =
  let cmp = match cmp with Some f -> f
                         | None -> fun (x,_) (y,_) -> cmp_k x y in
  match List.sort cmp l with
    | [] -> []
    | (k0, v0)::tl ->
	let k0, vs, l = List.fold_left (fun (k0, vs, l) (kn, vn) ->
	  if cmp_k k0 kn = 0 then k0, vn::vs, l
          else kn, [vn], (k0,List.rev vs)::l)
	  (k0, [v0], []) tl in
	List.rev ((k0,List.rev vs)::l)

(** {2 Choice, aka. either type}  *)

type ('a,'b) choice = Left of 'a | Right of 'b

let is_right = function
  | Right _ -> true | Left _ -> false

let partition_choice l =
  let rec split laux raux = function
    | [] -> List.rev laux, List.rev raux
    | Left e::tl -> split (e::laux) raux tl
    | Right e::tl -> split laux (e::raux) tl in
  split [] [] l

let partition_map f l =
  let rec split laux raux = function
    | [] -> List.rev laux, List.rev raux
    | hd::tl ->
        match f hd with
          | Left e -> split (e::laux) raux tl
          | Right e -> split laux (e::raux) tl in
  split [] [] l

let map_choice f g = function
  | Left e -> Left (f e)
  | Right e -> Right (g e)

let partition_map_some f l =
  let rec split laux raux = function
    | [] -> List.rev laux, List.rev raux
    | hd::tl ->
        match f hd with
          | None -> split laux raux tl
          | Some (Left e) -> split (e::laux) raux tl
          | Some (Right e) -> split laux (e::raux) tl in
  split [] [] l


let assoc_all x l =
  let rec aux acc = function
    | [] -> acc
    | (a,b)::l ->
      if a = x then aux (b::acc) l else aux acc l in
  aux [] l

let pop_assoc x l =
  let rec aux acc = function
    | [] -> raise Not_found
    | (a, b as pair) :: l ->
      if compare a x = 0 then b, List.rev_append acc l
      else aux (pair :: acc) l in
  aux [] l

let hashtbl_to_assoc h =
  Hashtbl.fold (fun k v acc -> (k, v)::acc) h []

let rec list_take n = function
  | a::l when n > 0 -> a :: list_take (n-1) l
  | _ -> []

(** {2 Lazy lists} *)
type 'a lazy_list = 'a lazy_list_ Lazy.t
and 'a lazy_list_ = LazNil | LazCons of 'a * 'a lazy_list
let rec laztake n = function
 | lazy (LazCons (a, l)) when n > 0 ->
   a::(laztake (n-1) l)
 | _ -> []
let rec append_aux l1 l2 =
  match l1 with lazy LazNil -> Lazy.force l2
  | lazy (LazCons (hd, tl)) ->
    LazCons (hd, lazy (append_aux tl l2))
let lazappend l1 l2 = lazy (append_aux l1 l2)
let rec concat_map_aux f = function
  | lazy LazNil -> LazNil
  | lazy (LazCons (a, l)) ->
    append_aux (f a) (lazy (concat_map_aux f l))
let lazconcat_map f l = lazy (concat_map_aux f l)
let rec map_aux f = function
  | lazy LazNil -> LazNil
  | lazy (LazCons (a, l)) ->
    LazCons (f a, lazy (map_aux f l))
let lazmap f l = lazy (map_aux f l)
let rec filter_aux f = function
  | lazy LazNil -> LazNil
  | lazy (LazCons (a, l)) ->
    if f a then LazCons (f a, lazy (map_aux f l))
    else map_aux f l
let lazfilter f l = lazy (filter_aux f l)
let rec map_some_aux f = function
  | lazy LazNil -> LazNil
  | lazy (LazCons (a, l)) ->
    match f a with
    | Some b -> LazCons (b, lazy (map_some_aux f l))
    | None -> map_some_aux f l
let lazmap_some f l = lazy (map_some_aux f l)
let rec laziter f = function
  | lazy LazNil -> ()
  | lazy (LazCons (a, l)) ->
    let () = f a in
    laziter f l
let rec of_list_aux = function
  | [] -> LazNil
  | a::l -> LazCons (a, lazy (of_list_aux l))
let laz_of_list l = lazy (of_list_aux l)
let laznil = lazy LazNil
let laz_single a = lazy (LazCons (a, lazy LazNil))
(*
let pr_lazy_list_aux f ppf = function
  | lazy LazNil -> 
*)

(** {2 Printing} *)

open Format

let pr_sep_list sep ?pr_hd pr_tl ppf l =
  let pr_hd = match pr_hd with
    | None -> pr_tl | Some pr_a -> pr_a in
  let rec aux = function
    | [] -> ()
    | [hd] -> pr_hd ppf hd
    | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_hd hd sep more_aux tl
  and more_aux ppf = function
    | [] -> ()
    | [hd] -> pr_tl ppf hd
    | hd::tl ->
      fprintf ppf "%a%s@ %a" pr_tl hd sep more_aux tl in
  aux l

let rec pr_pre_sep_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@ %s%a" pr_a hd sep (pr_pre_sep_list sep pr_a) tl

let rec pr_line_list sep pr_a ppf = function
  | [] -> ()
  | [hd] -> pr_a ppf hd
  | hd::tl ->
      fprintf ppf "%a@\n%s%a" pr_a hd sep (pr_line_list sep pr_a) tl

let pr_some pr_a ppf = function
  | None -> fprintf ppf "%s" "none"
  | Some a -> pr_a ppf a

let pr_ints ppf ints =
  pr_sep_list "," (fun ppf -> fprintf ppf "%d") ppf (Ints.elements ints)
