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
