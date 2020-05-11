include contrib.functor
include lib.list


val rec list_fid : ∀a:ο, ∀l ∈ list⟨a⟩, map id l ≡ l =
  fun l {
    case l {
      []       → qed
      hd :: tl → use list_fid tl
    }
  }


val rec list_fap : ∀a b c, ∀g ∈ (b ⇒ c), ∀f ∈ (a ⇒ b), ∀l ∈ list⟨a⟩,
                  map (g ∘ f) l ≡ (map g ∘ map f) l =
  fun g f l {
    case l {
       [] → qed
     | hd :: tl → eqns map (g ∘ f) l
                     ≡ map (g ∘ f) (hd :: tl)
                     ≡ ((g ∘ f) hd) :: map (g ∘ f) tl;
                  eqns ((map g) ∘ (map f)) l
                     ≡ map g (map f l)
                     ≡ map g (map f (hd :: tl))
                     ≡ map g (f hd :: map f tl)
                     ≡ g (f hd) :: map g (map f tl);
                  eqns (g ∘ f) hd ≡ g (f hd);
                  show map g (map f tl) ≡ map (g ∘ f) tl
                    using list_fap g f tl;
                  qed
    }
  }

val list_functor : functor⟨list⟩ =
  { fmap = map
  ; fid  = list_fid
  ; fap  = list_fap
  }