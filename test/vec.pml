include test.nat
include test.list

val rec length : ∀a:ο, list<a> ⇒ nat =
  fun l {
    case l {
      Nil    → zero
      Cns[c] → succ (length c.tl)
    }
  }

type vec<a:ο,s:ι> = ∃l:ι, l∈(list<a> | length l ≡ s)

val vnil : ∀a:ο, vec<a,zero> = nil

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
  fun y ls {
    let test : nat = length ls;
    Cns[{hd = y; tl = ls}]
  }

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,S[s]> =
  fun y ls { Cns[{hd = y; tl = ls}] }
