(** Reading and generating OCaml code/interface for InvarGenT.

    Released under the GNU General Public Licence (version 2 or
    higher), NO WARRANTY of correctness etc. (C) Lukasz Stafiniak 2013
    @author Lukasz Stafiniak lukstafi (AT) gmail.com
    @since Mar 2013
*)

val pr_ml :
  funtys:bool -> lettys:bool ->
  Format.formatter -> Terms.annot_item list -> unit
