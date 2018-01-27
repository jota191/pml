// Type of streams.
type corec stream⟨a⟩ = {} ⇒ {hd : a; tl : stream}

// Head of a stream.
val head : ∀a, stream⟨a⟩ ⇒ a =
  fun s { (s {}).hd }

// Tail of a stream.
val tail : ∀a, stream⟨a⟩ ⇒ stream⟨a⟩ =
  fun s { (s {}).tl }

// Identity function.
val rec id : ∀a, stream⟨a⟩ ⇒ stream⟨a⟩ =
  fun s _ {
    let c = s {};
    {hd = c.hd ; tl = id c.tl}
  }

// Map function.
val rec map : ∀a b, (a ⇒ b) ⇒ stream⟨a⟩ ⇒ stream⟨b⟩ =
  fun f s _ {
    let {hd ; tl} = s {};
    {hd = f hd ; tl = map f tl}
  }

include lib.nat
include lib.list

// Compute the list of the first n elements of a stream.
val rec nth : ∀a, nat ⇒ stream⟨a⟩ ⇒ a =
  fun n s {
    case n {
           | Zero → (s {}).hd
           | S[k] → nth k (s {}).tl
    }
  }

// Compute the list of the first n elements of a stream.
val rec takes : ∀a, nat ⇒ stream⟨a⟩ ⇒ list⟨a⟩ =
  fun n s {
    case n {
           | Zero → Nil
           | S[k] → let c = s {};
                    let tl = takes k c.tl;
                    Cons[{hd = c.hd; tl = tl}]
    }
  }

// Stream of zeroes.
val rec zeroes : stream⟨nat⟩ =
  fun _ { {hd = Zero; tl = zeroes} }

// Stream of the natural numbers starting at n.
val rec naturals_from : nat ⇒ stream⟨nat⟩ =
  fun n _ { {hd = n; tl = naturals_from S[n]} }

// Stream of the natural numbers.
val naturals : stream⟨nat⟩ = naturals_from Zero
