include lib.nat
include lib.nat_proofs

val u0   : nat = zero
val u1   : nat = succ u0
val u2   : nat = succ u1
val u3   : nat = succ u2
val u4   : nat = succ u3
val u5   : nat = succ u4
val u6   : nat = succ u5
val u7   : nat = succ u6
val u8   : nat = succ u7
val u9   : nat = succ u8
val u10  : nat = succ u9
val u11  : nat = succ u10
val u91  : nat = succ (mul u10 u9)
val u100 : nat = mul u10 u10
val u101 : nat = succ u100

def mccarthy91 : τ =
  fix mccarthy91 {
    fun n {
      if gt n u100 {
        minus n u10
      } else {
        mccarthy91 (mccarthy91 (add n u11))
      }
    }
  }

val lemma91 : ∀n∈nat, leq n u101 ≡ true ⇒ mccarthy91 n ≡ u91 =
  fun n h {
    {-1-}
  }

val mccarthy91_total : ∀n∈nat, ∃v:ι, v∈nat | mccarthy91 n ≡ v =
  fun n {
    if leq n u101 { // n ≤ 101
      use lemma91 n {};
      u91
    } else { // n > 101
      if gt n u100 { // n > 101 && n > 100
        deduce mccarthy91 n ≡ minus n u10;
        use minus n u10;
        minus n u10
      } else { // n > 101 && n ≤ 100
        deduce leq n u101 ≡ false;
        show compare n u101 ≡ Gr using
          case compare n u101 { Ls → ✂ | Eq → ✂ | Gr → {} };
        deduce gt n u100 ≡ false;
        case compare n u100 {
          | Ls → deduce compare n u100 ≡ Ls;
                 deduce compare n S[u100] ≡ Gr;
                 show compare n S[u100] ≡ Ls using succ_ls n u100 {};
                 ✂
          | Eq → ✂
          | Gr → ✂
        }
      }
    }
  }

val mccarthy91_fun : nat ⇒ nat = mccarthy91_total
