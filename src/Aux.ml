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

module Ints = Set.Make
  (struct type t = int let compare x y = x - y end)
let add_ints nvs vs =
  List.fold_left (fun vs nv -> Ints.add nv vs) vs nvs
let ints_of_list nvs =
  add_ints nvs Ints.empty

let order_key l = List.sort (fun (a,_) (b,_) -> compare a b) l

let unique_sorted ?(cmp = Pervasives.compare) l =
  let rec idemp acc = function
    | e1::(e2::_ as tl) when cmp e1 e2 = 0 -> idemp acc tl
    | e::tl -> idemp (e::acc) tl
    | [] -> acc in
  idemp [] (List.sort (fun x y -> - (cmp x y)) l)

let fold_map f acc l =
  let rec aux acc res =
    function
    | [] -> acc, List.rev res
    | hd::tl ->
      let acc, hd = f acc hd in aux acc (hd::res) tl in
  aux acc [] l

let rec list_make_n e n =
  if n <= 0 then [] else e :: list_make_n e (n-1)

let concat_map f l =
  let rec cmap_f accu = function
    | [] -> accu
    | a::l -> cmap_f (List.rev_append (f a) accu) l
  in
  List.rev (cmap_f [] l)

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

let map_some2 f l1 l2 =
  let rec maps_f accu = function
    | ([], []) -> accu
    | a1::l1, a2::l2 -> maps_f (match f a1 a2 with None -> accu
	| Some r -> r::accu) (l1, l2)
    | _, _ -> invalid_arg "Aux.map_some2"
  in
  List.rev (maps_f [] (l1, l2))

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

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thr3 (_,_,c) = c

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
      if List.exists (flip less e) acc then aux acc l
      else aux (e::List.filter (fun f -> not (less e f)) acc) l in
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

let list_inter a b = List.filter (fun e -> List.mem e b) a
let list_diff a b = List.filter (fun e -> not (List.mem e b)) a

(* Second argument should be sorted. *)
let replace_assocs ~repl l =
  let cmp  (i,_) (j,_) = compare i j in
  let rec idemp acc = function
    | e1::(e2::_ as tl) when cmp e1 e2 = 0 -> idemp acc tl
    | e::tl -> idemp (e::acc) tl
    | [] -> acc in
  idemp [] (List.rev (merge cmp (List.sort cmp repl) l))

let bind_opt t f =
  match t with
  | None -> None
  | Some t -> f t

let map_opt t f =
  match t with
  | None -> None
  | Some t -> Some (f t)

let unsome = function None -> invalid_arg "Aux.unsome" | Some e -> e

let map_reduce ?mapf redf red0 l =
  let l = match mapf with None -> l | Some f -> List.map f l in
  match List.sort (fun x y -> compare (fst x) (fst y)) l with
      | [] -> []
      | (k0, v0)::tl ->
        let k0, vs, l =
          List.fold_left (fun (k0, vs, l) (kn, vn) ->
	    if k0 = kn then k0, vn::vs, l
            else kn, [vn], (k0,vs)::l)
	    (k0, [v0], []) tl in
        List.rev_map (fun (k,vs) -> k, List.fold_left redf red0 vs)
          ((k0,vs)::l)

let collect l =
  match List.sort (fun x y -> compare (fst x) (fst y)) l with
    | [] -> []
    | (k0, v0)::tl ->
	let k0, vs, l = List.fold_left (fun (k0, vs, l) (kn, vn) ->
	  if k0 = kn then k0, vn::vs, l
          else kn, [vn], (k0,List.rev vs)::l)
	  (k0, [v0], []) tl in
	List.rev ((k0,List.rev vs)::l)

(** {2 Choice, aka. either type}  *)

type ('a,'b) choice = Left of 'a | Right of 'b

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
