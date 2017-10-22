include lib.option
include lib.nat

type rec list<a> = [Nil ; Cons of {hd : a ; tl : list}]

val nil : ∀a, list<a> = []
val cons : ∀a, a ⇒ list<a> ⇒ list<a> =
  fun hd tl { hd::tl }

val head : ∀a, list<a> ⇒ option<a> =
  fun l {
    case l {
      []       → none
      hd :: tl → some hd
    }
  }

val tail : ∀a, list<a> ⇒ option<list<a>> =
  fun l {
    case l {
      []       → none
      hd :: tl → some tl
    }
  }

val rec length : ∀a, list<a> ⇒ nat =
  fun l {
    case l {
      []       → zero
      hd :: tl → succ (length tl)
    }
  }

val rec map : ∀a b, (a ⇒ b) ⇒ list<a> ⇒ list<b> =
  fun fn l {
    case l {
      []       → []
      hd :: tl → fn hd :: map fn tl
    }
  }

val rec fold_left : ∀a b, (a ⇒ b ⇒ a) ⇒ a ⇒ list<b> ⇒ a =
  fun fn acc l {
    case l {
      []       → acc
      hd :: tl → fold_left fn (fn acc hd) tl
    }
  }

val sum : list<nat> ⇒ nat = fold_left add zero

val rec app : ∀b, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      []       → l2
      hd :: tl → cons hd (app tl l2)
    }
  }

val rec rev_app : ∀b, list<b> ⇒ list<b> ⇒ list<b> =
  fun l1 l2 {
    case l1 {
      []       → l2
      hd :: tl → rev_app tl (hd :: l2) // FIXME: loop if app instead of rev_app
                                       // in the proof of rev_total (l2 = [])
    }
  }

val rev : ∀b, list<b> ⇒ list<b> = fun l { rev_app l [] }