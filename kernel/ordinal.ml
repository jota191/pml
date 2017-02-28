open Ast
open Pos
open Compare

type positives = ordi list

let is_pos : positives -> ordi -> bool =
  fun pos o ->
    let o = Norm.whnf o in
    match o.elt with
    | Vari(_) -> assert false (* Should not happen. *)
    | Conv    -> true
    | Succ(_) -> true
    | _       -> List.exists (eq_expr ~strict:true o) pos

let rec oadd : ordi -> int -> ordi =
  fun o n -> if n <= 0 then o else oadd (Pos.none (Succ(o))) (n-1)

let rec leq_i_ordi : positives -> ordi -> int -> ordi -> bool =
  fun pos o1 i o2 ->
    let o1 = Norm.whnf o1 in
    let o2 = Norm.whnf o2 in
    match (o1.elt, o2.elt) with
    | (Vari(_) , _       ) -> assert false (* Should not happen. *)
    | (_       , Vari(_) ) -> assert false (* Should not happen. *)
    | (_       , _       ) when eq_expr ~strict:true (oadd o1 i) o2 -> true
    | (_       , Succ(o2)) -> leq_i_ordi pos o1 (i-1) o2
    | (Succ(o1), _       ) -> leq_i_ordi pos o1 (i+1) o2
    (* TODO unification and higher-order *)
    | (OWit(o1,_,_), _   ) when (Norm.whnf o1).elt <> OMax ->
        let i = if is_pos pos o1 then i-1 else i in
        leq_i_ordi pos o1 i o2
    | (_       , _       ) -> false

let leq_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 0 o2

let less_ordi : positives -> ordi -> ordi -> bool =
  fun pos o1 o2 -> leq_i_ordi pos o1 1 o2
