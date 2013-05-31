(** Solving second-order i.e. formula variables for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)
open Terms

type chi_subst = (int * formula) list

let sb_typ_unary arg =
  typ_map {typ_id_map with map_delta = fun _ -> arg}  

let sb_typ_binary arg1 arg2 =
  typ_map {typ_id_map with map_delta = fun b -> if b then arg1 else arg2}  

let sb_atom_unary arg = function
  | Eqty (t1, t2, lc) ->
    Eqty (subst_typ_unary arg t1, subst_typ_unary arg t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (subst_typ_unary arg t1, subst_typ_unary arg t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_atom_binary arg1 arg2 = function
  | Eqty (t1, t2, lc) ->
    Eqty (subst_typ_binary arg1 arg2 t1, subst_typ_binary arg1 arg2 t2, lc)
  | Leq (t1, t2, lc) ->
    Leq (subst_typ_binary arg1 arg2 t1, subst_typ_binary arg1 arg2 t2, lc)
  | CFalse _ as a -> a
  | PredVarU (_, t) -> assert false
  | PredVarB (_, t1, t2) -> assert false

let sb_phi_unary arg = List.map (sb_atom_unary arg)

let sb_phi_binary arg1 arg2 = List.map (sb_atom_binary arg1 arg2)

let sb_atom_pred psb = function
  | PredVarU (i, t) as a ->
    (try
       let phi = List.find i psb in
       sb_phi_unary t phi
     with Not_found -> a)  
  | PredVarB (_, t1, t2) -> assert false
    (try
       let phi = List.find i psb in
       sb_phi_binary t1 t2 phi
     with Not_found -> a)

let rec split cmp_v uni_v avs ans bvss =
  ()

let operator cmp_v uni_v brs sol =
  ()
