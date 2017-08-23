include lib.either
include lib.nat
include lib.nat_proofs

type min<n,f> = ∀p ∈ nat, leq (f n) (f p) ≡ true

def total<f,a:ο> = ∀x∈a, ∃w:ι, f x ≡ w

type bot = ∀x:ο,x

type snat<o> = μo nat [ Z ; S of nat ]

val rec leq_size : ∀o, ∀m∈snat<o+1>, ∀n∈nat, either<leq m n ≡ true, n∈snat<o>> =
  fun m n {
    case m {
      Z → case n {
          Z    → InL
          S[n] → InL
        }
      S[m] →
        case n {
          Z  → InR[Z]
          S[n] →
            case m {  // case for n because leq use compare
              Z     → case n { Z → InL | S[_] → InL}
              S[m'] →
                case leq_size S[m'] n {
                  InL    → InL
                  InR[p] → InR[S[p]]
                  }
              }
          }
      }
  }

val rec fn : ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∀n∈nat, ∀q∈(nat | q ≡ f n),
    (∀n∈ nat, min<n,f> ⇒ bot) ⇒ bot =
  fun f ft n q k {
    let o such that q : snat<o+1> in
    k (n:nat) (fun p {
        use {ft p};
        use {leq_total q (f p)};
        case leq_size (q:snat<o+1>) (f p) {
          InL     → {}
          InR[fp] → fn f ft p fp k
        }} : min<n,f>)
  }

type prod<a,b> = {fst : a ; snd : b }

val minimum_principle : ∀f∈(nat ⇒ nat), total<f,nat> ⇒ ∃n:ι, (prod<n∈nat, min<n,f>>) =
  fun f ft {
    save s {
      let k : ∀n∈ nat, min<n,f> ⇒ bot =
        fun n mi {
          restore s ({ fst = n; snd=mi }:prod<n∈nat, min<n,f>>)
        }
      in
      use { ft Z };
      fn f ft Z (f Z) k
    }
  }
