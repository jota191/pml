include lib.list

type order<a:ο> = ∃cmp:ι, {
  cmp : cmp ∈ (a ⇒ a ⇒ bool);
  tmp : ∀x y∈a, ∃v:ι, v ≡ cmp x y;
  tra : ∀x y z∈a, (cmp x y ≡ tru ⇒ cmp y z ≡ tru ⇒ cmp x y ≡ tru);
  tot : ∀x y∈a, or (cmp x y) (cmp y x) ≡ tru
}

val rec sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, bool = fun o l →
  case l of
  | Nil[_]   → tru
  | Cons[c1] →
    let hd = c1.hd in let tl = c1.tl in
    (case tl of
     | Nil[_]   → tru
     | Cons[c2] →
       let hd2 = c2.hd in
       land<(o.cmp) hd hd2, sorted o tl>)

val rec sorted_total : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, ∃v:ι, v ≡ sorted o l =
  fun o l →
  case l of
  | Nil[_]   → {}
  | Cons[c1] →
    let hd = c1.hd in let tl = c1.tl in
    (case tl of
    | Nil[_]   → {}
    | Cons[c2] →
       let hd2 = c2.hd in let tl2 = c2.tl in
       let ind : (∃v:ι, v ≡ sorted o tl) = sorted_total o tl in
       let lem = o.tmp hd hd2 in
       if o.cmp hd hd2 then
         (let lem : o.cmp hd hd2 ≡ tru = {} in
          let lem : sorted o l ≡ sorted o tl = {} in {})
       else
         (let lem : o.cmp hd hd2 ≡ fls = {} in
          let lem : sorted o l ≡ fls = {} in {}))


val rec insert : ∀a:ο, order<a> ⇒ a ⇒ list<a> ⇒ list<a> = fun o x l →
   case l of
   | Nil[_]   → Cons[{hd = x; tl = Nil}]
   | Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                if o.cmp x hd then Cons[{hd = x ; tl = l}]
                else
                  (let tl = insert o x tl in
                   Cons[{hd = hd ; tl = tl}])

val rec insert_total :  ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>,
     ∃v:ι, insert o x l ≡ v =
  fun o x l →
    case l of
    | Nil[_]   → {}
    | Cons[c1] → let hd = c1.hd in let tl = c1.tl in
                 let lem = o.tmp x hd in
                 if o.cmp x hd then {}
                 else (let lem = insert_total o x tl in {})

val rec isort : ∀a:ο, order<a> ⇒ list<a> ⇒ list<a> = fun o l →
   case l of
   | Nil[_]  → Nil
   | Cons[c] → insert o c.hd (isort o c.tl)

val rec isort_total :  ∀a:ο, ∀o∈order<a>, ∀l∈list<a>, ∃v:ι, isort o l ≡ v =
  fun o l →
    case l of
    | Nil[_]  → {}
    | Cons[c] → let lem = isort_total o c.tl in
                let lem = insert_total o c.hd (isort o c.tl) in {}

type slist<a:ο,ord:τ> = ∃l:ι, l∈(list<a> | sorted ord l ≡ tru)

val rec tail_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈list<a>,
    sorted o Cons[{hd = x ; tl = l}] ≡ tru ⇒
    sorted o l ≡ tru =
  fun o x l hyp →
    case l of
    | Nil[_]  → {}
    | Cons[c] → let lem : (∃v:ι, o.cmp x c.hd ≡ v) = o.tmp x c.hd in
                let lem : (∃v:ι, sorted o l ≡ v) = sorted_total o l in
                if o.cmp x c.hd then {} else ✂

val rec insert_sorted : ∀a:ο, ∀o∈order<a>, ∀x∈a, ∀l∈slist<a,o>,
    sorted o (insert o x l) ≡ tru =
  fun o x l →
    let cmp = o.cmp in
    case l of
    | Nil[_]   → {}
    | Cons[c1] →
      let hd = c1.hd in let tl = c1.tl in
      let lem = insert_total o x tl in
      let lem = o.tmp x hd in
      if cmp x hd then (let lem = tail_sorted o hd tl {} in {})
      else
        (let lem : (∃v:ι, v ≡ cmp x hd) = o.tmp x hd in
         let lem : (∃v:ι, v ≡ cmp hd x) = o.tmp hd x in
         let lem : cmp hd x ≡ tru = o.tot x hd in
         (case tl of
          | Nil[] → {}
          | Cons[c2] →
            let hd2 = c2.hd in let tl2 = c2.tl in
            let lem = insert_total o x tl2 in
            let lem : (∃v:ι, v ≡ cmp hd hd2) = o.tmp hd hd2 in
            let lem : (∃v:ι, v ≡ cmp x hd2) = o.tmp x hd2 in
            if cmp hd hd2 then 
              (let lem = insert_sorted o x tl in
               if cmp x hd2 then {} else
               (let lem : (∃v:ι, v ≡ cmp hd2 x) = o.tmp hd2 x in
                let lem : (cmp hd2 x) ≡ tru = o.tot x hd2 in {})
              )
            else ✂))

val rec isort_sorted : ∀a:ο, ∀o∈order<a>, ∀l∈list<a>,
    sorted o (isort o l) ≡ tru =
  fun o l →
    case l of
    | Nil[_]  → {}
    | Cons[c] → let lem = isort_total o c.tl in
                let lem = sorted_total o (isort o c.tl) in
                let ind = isort_sorted o c.tl in
                let lem = insert_total o c.hd (isort o c.tl) in
                let tls = isort o c.tl in
                let lem = insert_sorted o c.hd tls in {}
