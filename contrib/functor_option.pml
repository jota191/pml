include contrib.functor
include lib.option


val option_fmap : ∀a b:ο, (a ⇒ b) ⇒ option⟨a⟩ ⇒ option⟨b⟩ =
  fun f o
  {
    case o
      {
        None    → None
      | Some[v] → Some[f v]
      }
  }


val option_fid : ∀a:ο, ∀x ∈ option⟨a⟩, option_fmap id x ≡ x =
  fun x
  {
    case x
      {
           None → qed
         | Some[v] → eqns option_fmap id x
                     ≡ option_fmap id (Some[v])
                     ≡ (Some[id v])
                     ≡ Some[v]; qed
      }
  }

val option_fap : ∀a b c, ∀g ∈ (b ⇒ c), ∀f ∈ (a ⇒ b), ∀x ∈ option⟨a⟩,
   option_fmap (comp g f) x ≡ comp (option_fmap g) (option_fmap f) x =
  fun g f x
  {
    case x
      {
        None    → qed
      | Some[v] → eqns option_fmap (comp g f) x
                  ≡ option_fmap (comp g f) (Some[v])
                  ≡ (Some[(comp g f v)])
                  ≡ (Some[(g (f v))]);
                  eqns comp (option_fmap g) (option_fmap f) x
                  ≡ comp (option_fmap g) (option_fmap f) (Some[v])
                  ≡ (option_fmap g) ((option_fmap f) (Some[v]))
                  ≡ (option_fmap g) (Some[f v])
                  ≡ (Some[g (f v)]); qed
      }
  }

val option_functor : functor⟨option⟩ =
  { fmap = option_fmap
  ; fid  = option_fid
  ; fap  = option_fap
  }