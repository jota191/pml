include lib.nat
include lib.list
include contrib.functor

type vec⟨n,a⟩ = {l∈list⟨a⟩ | length l ≡ n}

val rec vec_map : ∀a b :ο, ∀ n:ι, (a ⇒ b) ⇒ vec⟨n, a⟩ ⇒ vec⟨n, b⟩ =
  fun f v {
    case v {
      []      → []
      hd::tl  → let n = length tl; f hd::vec_map f tl
      }
  }

val rec vec_fid : ∀a:ο, ∀n:ι, ∀v∈vec⟨n,a⟩, vec_map id v ≡ v =
  fun l {
    case l{
      [] → qed
      hd::tl → use vec_fid tl
    }    
  }

val rec vec_fap : ∀a b c, ∀ n:ι, ∀g ∈ (b ⇒ c), ∀f ∈ (a ⇒ b), ∀v ∈ vec⟨n,a⟩,
                    vec_map (g ∘ f) v ≡ (vec_map g ∘ vec_map f) v =
  fun g f l {
    case l {
       [] → qed
     | hd :: tl →
            eqns vec_map (g ∘ f) l
               ≡ vec_map (g ∘ f) (hd :: tl)
               ≡ ((g ∘ f) hd) :: vec_map (g ∘ f) tl;
            eqns (vec_map g ∘ vec_map f) l
               ≡ vec_map g (vec_map f l)
               ≡ vec_map g (vec_map f (hd :: tl))
               ≡ vec_map g (f hd :: vec_map f tl)
               ≡ g (f hd) :: vec_map g (vec_map f tl);
            eqns (g ∘ f) hd ≡ g (f hd);
            let n = length tl;                  
            show vec_map g (vec_map f tl) ≡ vec_map (g ∘ f) tl
               using vec_fap g f tl;
            qed
    }
  }

/// ??
//val vec_functor : ∀n:ι, functor⟨vec⟨n,⟩