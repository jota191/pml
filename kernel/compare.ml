(** Expression comparing and unification. *)

open Bindlib
open Sorts
open Pos
open Ast
open Output

(* Log functions registration. *)
let log_equ = Log.register 'c' (Some "cmp") "comparing informations"
let log_equ = Log.(log_equ.p)

let log_uni = Log.register 'u' (Some "uni") "unification informations"
let log_uni = Log.(log_uni.p)

(* Setting a unification variable. *)
let uvar_set : type a. a uvar -> a ex loc -> unit = fun u e ->
  log_uni "?%i ← %a" u.uvar_key Print.ex e;
  assert(!(u.uvar_val) = None);
  u.uvar_val := Some e

(* Unification variable equality test. *)
let uvar_eq : type a. a uvar -> a uvar -> bool =
  fun u v -> u.uvar_key == v.uvar_key

type uvar_fun = { f : 'a. 'a sort -> 'a uvar -> unit }

let rec uvar_iter : type a. uvar_fun -> a ex loc -> unit = fun f e ->
  let uvar_iter_eq f (t,_,u) = uvar_iter f t; uvar_iter f u in
  match (Norm.whnf e).elt with
  | Vari(_)     -> ()
  | HFun(_,_,b) -> uvar_iter f (bndr_subst b Dumm)
  | HApp(_,a,b) -> uvar_iter f a; uvar_iter f b
  | HDef(_)     -> () (* NOTE no unification variable in definition. *)
  | Func(a,b)   -> uvar_iter f a; uvar_iter f b
  | Prod(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | DSum(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | Univ(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Exis(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | FixM(o,b)   -> uvar_iter f o; uvar_iter f (bndr_subst b Dumm)
  | FixN(o,b)   -> uvar_iter f o; uvar_iter f (bndr_subst b Dumm)
  | Memb(t,a)   -> uvar_iter f t; uvar_iter f a
  | Rest(a,eq)  -> uvar_iter f a; uvar_iter_eq f eq
  (* NOTE type annotation ignored. *)
  | LAbs(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Cons(_,v)   -> uvar_iter f v
  | Reco(m)     -> M.iter (fun _ (_,a) -> uvar_iter f a) m
  | Scis        -> ()
  | VDef(_)     -> () (* NOTE no unification variable in definition. *)
  | Valu(v)     -> uvar_iter f v
  | Appl(t,u)   -> uvar_iter f t; uvar_iter f u
  (* NOTE type annotation ignored. *)
  | MAbs(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | Name(s,t)   -> uvar_iter f s; uvar_iter f t
  | Proj(v,_)   -> uvar_iter f v
  | Case(v,m)   -> let fn _ (_,b) = uvar_iter f (bndr_subst b Dumm) in
                   uvar_iter f v; M.iter fn m
  | FixY(t,v)   -> uvar_iter f t; uvar_iter f v
  | Epsi        -> ()
  | Push(v,s)   -> uvar_iter f v; uvar_iter f s
  | Fram(t,s)   -> uvar_iter f t; uvar_iter f s
  | Conv        -> ()
  | Succ(o)     -> uvar_iter f o
  (* NOTE type annotations ignored. *)
  | VTyp(v,_)   -> uvar_iter f v
  | TTyp(t,_)   -> uvar_iter f t
  | VLam(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | TLam(_,b)   -> uvar_iter f (bndr_subst b Dumm)
  | ITag(_)     -> ()
  | Dumm        -> ()
  | VWit(b,a,c) -> uvar_iter f (bndr_subst b Dumm);
                   uvar_iter f a; uvar_iter f c
  | SWit(b,a)   -> uvar_iter f (bndr_subst b Dumm); uvar_iter f a
  | UWit(_,t,b) -> uvar_iter f t; uvar_iter f (bndr_subst b Dumm)
  | EWit(_,t,b) -> uvar_iter f t; uvar_iter f (bndr_subst b Dumm)
  | UVar(s,u)   -> f.f s u

type s_elt = U : 'a sort * 'a uvar -> s_elt

let uvars : type a. a ex loc -> s_elt list = fun e ->
  let uvars = ref [] in
  let f s u =
    let p (U(_,v)) = v.uvar_key == u.uvar_key in
    if not (List.exists p !uvars) then uvars := (U(s,u)) :: !uvars
  in
  uvar_iter {f} e; !uvars

let uvar_occurs : type a b. a uvar -> b ex loc -> bool = fun u e ->
  let f _ v = if v.uvar_key == u.uvar_key then raise Exit in
  try uvar_iter {f} e; false with Exit -> true

(* Comparison function with unification variable instantiation. *)
let eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
  log_equ "trying to show %a = %a" Print.ex e1 Print.ex e2;
  let c = ref (-1) in
  let new_itag : type a. unit -> a ex = fun () -> incr c; ITag(!c) in
  let rec eq_expr : type a. a ex loc -> a ex loc -> bool = fun e1 e2 ->
    let e1 = Norm.whnf e1 in
    let e2 = Norm.whnf e2 in
    (* log_equ "comparing %a and %a" Print.ex e1 Print.ex e2; *)
    match (e1.elt, e2.elt) with
    | (Vari(x1)      , Vari(x2)      ) ->
        Bindlib.eq_vars x1 x2
    | (HFun(_,_,b1)  , HFun(_,_,b2)  ) ->
        let t = new_itag () in
        eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (HApp(s1,f1,a1), HApp(s2,f2,a2)) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> eq_expr f1 f2 && eq_expr a1 a2
          | NEq -> false
        end
    | (HDef(_,d)     , _             ) -> eq_expr d.expr_def e2
    | (_             , HDef(_,d)     ) -> eq_expr e1 d.expr_def
    | (Func(a1,b1)   , Func(a2,b2)   ) -> eq_expr a1 a2 && eq_expr b1 b2
    | (DSum(m1)      , DSum(m2)      ) ->
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Prod(m1)      , Prod(m2)      ) ->
        M.equal (fun (_,a1) (_,a2) -> eq_expr a1 a2) m1 m2
    | (Univ(s1,b1)   , Univ(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
          | NEq -> false
        end
    | (Exis(s1,b1)   , Exis(s2,b2)   ) ->
        begin
          match eq_sort s1 s2 with
          | Eq  -> let t = new_itag () in
                   eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
          | NEq -> false
        end
    | (FixM(o1,b1)   , FixM(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (FixN(o1,b1)   , FixN(o2,b2)   ) ->
        let t = new_itag () in
        eq_expr o1 o2 && eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Memb(t1,a1)   , Memb(t2,a2)   ) -> eq_expr t1 t2 && eq_expr a1 a2
    | (Rest(a1,eq1)  , Rest(a2,eq2)  ) ->
        let (t1,b1,u1) = eq1 and (t2,b2,u2) = eq2 in
        b1 = b2 && eq_expr a1 a2 && eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (LAbs(_,b1)    , LAbs(_,b2)    ) ->
        let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Cons(c1,v1)   , Cons(c2,v2)   ) -> c1.elt = c2.elt && eq_expr v1 v2
    | (Reco(m1)      , Reco(m2)      ) ->
        M.equal (fun (_,v1) (_,v2) -> eq_expr v1 v2) m1 m2
    | (Scis          , Scis          ) -> true
    | (VDef(d1)      , VDef(d2)      ) -> d1 == d2 (* FIXME ? *)
    | (Valu(v1)      , Valu(v2)      ) -> eq_expr v1 v2
    | (Appl(t1,u1)   , Appl(t2,u2)   ) -> eq_expr t1 t2 && eq_expr u1 u2
    (* NOTE type annotation ignored. *)
    | (MAbs(_,b1)    , MAbs(_,b2)    ) ->
        let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
    | (Name(s1,t1)   , Name(s2,t2)   ) -> eq_expr s1 s2 && eq_expr t1 t2
    | (Proj(v1,l1)   , Proj(v2,l2)   ) -> l1.elt = l2.elt && eq_expr v1 v2
    | (Case(v1,m1)   , Case(v2,m2)   ) ->
        let cmp (_,b1) (_,b2) =
          let t = new_itag () in eq_expr (bndr_subst b1 t) (bndr_subst b2 t)
        in
        eq_expr v1 v2 && M.equal cmp m1 m2
    | (FixY(t1,v1)   , FixY(t2,v2)   ) -> eq_expr t1 t2 && eq_expr v1 v2
    | (Epsi          , Epsi          ) -> true
    | (Push(v1,s1)   , Push(v2,s2)   ) -> eq_expr v1 v2 && eq_expr s1 s2
    | (Fram(t1,s1)   , Fram(t2,s2)   ) -> eq_expr t1 t2 && eq_expr s1 s2
    | (Conv          , Conv          ) -> true
    | (Succ(o1)      , Succ(o2)      ) -> eq_expr o1 o2
    (* NOTE type annotations ignored. *)
    | (VTyp(v1,_)    , _             ) -> eq_expr v1 e2
    | (_             , VTyp(v2,_)    ) -> eq_expr e1 v2
    | (TTyp(t1,_)    , _             ) -> eq_expr t1 e2
    | (_             , TTyp(t2,_)    ) -> eq_expr e1 t2
    | (VLam(_,b1)    , _             ) -> eq_expr (bndr_subst b1 Dumm) e2
    | (_             , VLam(_,b2)    ) -> eq_expr e1 (bndr_subst b2 Dumm)
    | (TLam(_,b1)    , _             ) -> eq_expr (bndr_subst b1 Dumm) e2
    | (_             , TLam(_,b2)    ) -> eq_expr e1 (bndr_subst b2 Dumm)
    | (ITag(i1)      , ITag(i2)      ) -> i1 = i2
    (* NOTE should not be compare dummy expressions. *)
    | (Dumm          , Dumm          ) -> false
    | (VWit(f1,a1,b1), VWit(f2,a2,b2)) ->
        let t = new_itag () in
        eq_expr (bndr_subst f1 t) (bndr_subst f2 t) && eq_expr a1 a2 && eq_expr b1 b2
    | (SWit(f1,a1)   , SWit(f2,a2)   ) ->
        let t = new_itag () in
        eq_expr (bndr_subst f1 t) (bndr_subst f2 t) && eq_expr a1 a2
    | (UWit(s1,t1,b1), UWit(s2,t2,b2)) ->
        let t = new_itag () in
        eq_expr (bndr_subst b1 t) (bndr_subst b2 t) && eq_expr t1 t2
    | (EWit(s1,t1,b1), EWit(s2,t2,b2)) ->
        let t = new_itag () in
        eq_expr (bndr_subst b1 t) (bndr_subst b2 t) && eq_expr t1 t2
    | (UVar(_,u1)    , UVar(_,u2)    ) ->
        if u1.uvar_key <> u2.uvar_key then uvar_set u1 e2;
        true
    (* FIXME experimental. *)
    | (UVar(_,u1)    , Func({elt = Memb(t,a)}, b)) when uvar_occurs u1 t ->
        eq_expr e1 (Pos.none (Func(a,b)))
    | (UVar(_,u1)    , _             ) ->
        if uvar_occurs u1 e2 then false else (uvar_set u1 e2; true)
    | (_             , UVar(_,u2)    ) ->
        if uvar_occurs u2 e1 then false else (uvar_set u2 e1; true)
    | _                                -> false
  in
  let res = eq_expr e1 e2 in
  log_equ "we have %a %s %a"
    Print.ex e1 (if res then "=" else "≠") Print.ex e2;
  res