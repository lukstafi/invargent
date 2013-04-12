(** General purpose auxiliary functions for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
let flip f a b = f b a

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

let product l =
  List.fold_left (fun prod set -> concat_map
    (fun el -> List.rev (List.rev_map (fun tup ->  el::tup) prod))
    set) [[]] (List.rev l) 

let bind_opt t f =
  match t with
  | None -> None
  | Some t -> f t

let unsome = function None -> invalid_arg "Aux.unsome" | Some e -> e

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

(** {2 Lazy lists} *)
(*
type 'a lazy_list = 'a lazy_list_ Lazy.t
and 'a lazy_list_ = LNil | LCons of 'a * 'a lazy_list

let lsingl a = lazy (LCons (a, lazy LNil))
let rec ltake n = function
 | lazy (LazCons (a, l)) when n > 0 ->
   a::(laztake (n-1) l)
 | _ -> []
let rec append_aux l1 l2 =
  match l1 with lazy LazNil -> Lazy.force l2
  | lazy (LazCons (hd, tl)) ->
    LazCons (hd, lazy (append_aux tl l2))
let lappend l1 l2 = lazy (append_aux l1 l2)
let rec concat_map_aux f = function
  | lazy LazNil -> LazNil
  | lazy (LazCons (a, l)) ->
    append_aux (f a) (lazy (concat_map_aux f l))
let lconcat_map f l = lazy (concat_map_aux f l)

let rec lfoldM f a = function
  | [] -> lsingl a
  | x::xs -> lconcat_map (fun a' -> foldM f a' xs) (f a x)
*)
