(** Inferring and normalizing formulas for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

(** Shortcut for deriving [false]. *)
exception Contradiction of string * (Terms.typ * Terms.typ) option * Terms.loc

type cnstrnt =
| And of cnstrnt list
| Or of atom list
| Impl of atom list * cnstrnt list
| All of var_name list * cnstrnt
| Ex of var_name list * cnstrnt

