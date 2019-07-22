

val id : ∀a, a ⇒ a = fun x {x}
val comp : ∀ a b c, (b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c
  = fun g f {
     fun x { g (f x)}
  }

infix (∘) = comp priority 9 left associative
//in a strict language probably left associativity is ok

type functor⟨f :ο → ο⟩ = ∃fmap,
   { fmap : fmap ∈ (∀a b : ο, (a ⇒ b) ⇒ f⟨a⟩ ⇒ f⟨b⟩)
   ; fid  : ∀ a:ο, ∀x∈ f⟨a⟩, fmap id x ≡ x
   ; fap  : ∀ a b c, ∀ g∈(b ⇒ c), ∀ h∈(a ⇒ b), ∀x∈ f⟨a⟩,
           fmap (comp g h) x ≡ comp (fmap g) (fmap h) x
   }
