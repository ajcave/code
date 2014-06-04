
type ident = AbsSyntax.ident
type idx = Top | Pop of idx

and moduleT =
   Mod of ident * decl list

and decl =
   Def of ident * exp * exp

and exp =
   Pi of exp * abstr
 | Sigma of exp * abstr
 | Nat
 | Set
 | Unit
 | Tt
 | Lam of abstr
 | App of exp * exp
 | Var of idx
 | Const of ident
 | Zero
 | Suc of exp
 | Plus of exp * exp
 | NatRec of exp * abstr * exp * (ident * ident * exp)
 | Subst of subst * exp
and abstr = ident * exp

and nat = NZero | NSuc of nat
and subst =
  | Shift of nat
  | Dot of subst * exp

type signature = decl list

let idsub = Shift NZero
let shift1 = Shift (NSuc NZero)
let rec shiftvar n i = match n with
  | NZero -> i
  | NSuc n -> Pop (shiftvar n i)
let rec substvar s i = match (s,i) with
  | Shift n, i -> Var (shiftvar n i)
  | Dot (s,e), Top -> e
  | Dot (s,e), Pop i -> substvar s i
let rec nplus k n = match k with
  | NZero -> n
  | NSuc k -> nplus k n
let rec shiftComp s1 n = match (s1,n) with
  | s1, NZero -> s1
  | Shift k, n -> Shift (nplus k n)
  | Dot (s1,e), NSuc n -> shiftComp s1 n
let rec comp s1 = function
  | Shift n -> shiftComp s1 n
  | Dot (s2,e) -> Dot (comp s1 s2, subst s1 e)

and ext1 s = Dot (comp shift1 s, Var Top)
and sub1 e = Dot (idsub, e)
and subst1 e b = Subst (sub1 e, b)
and subst s b = Subst (s, b)
and do_shift1 e = subst shift1 e

and abstr_subst s (x,e) = (x, subst (ext1 s) e)
let abstr_subst1 e1 (x,e) = (x, subst1 e1 e)

(* Push a substitution under one constructor *)
let rec whsubst s = function
  | Pi (t, a) -> Pi (subst s t, abstr_subst s a)
  | Sigma (t, a) -> Sigma (subst s t, abstr_subst s a)
  | Nat -> Nat
  | Unit -> Unit
  | Set -> Set
  | Zero -> Zero
  | Tt -> Tt
  | Suc e -> Suc (subst s e)
  | Lam a -> Lam (abstr_subst s a)
  | App (e1,e2) -> App (subst s e1, subst s e2)
  | Var x -> substvar s x
  | Const c -> Const c
  | Plus (e1,e2) -> Plus (subst s e1, subst s e2)
  | Subst (s1, e) -> whsubst (comp s s1) e
  | NatRec (en,aC,ez,(x,ih,eS)) ->
    NatRec (subst s en, abstr_subst s aC, subst s ez, (x,ih, subst (ext1 (ext1 s)) eS))

