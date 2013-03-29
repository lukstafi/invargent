(** General purpose auxiliary functions for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

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

(** {2 Lazy lists} *)

type 'a lazy_list = 'a lazy_list_ Lazy.t
and 'a lazy_list_ = LNil | LCons of 'a * 'a lazy_list

