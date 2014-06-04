
type ident = AbsSyntax.ident
type idx = Top | Pop of idx
and moduleT =
   Mod of ident * decl list

and decl =
   Def of ident * exp * exp

and exp =
   Pi of ident * exp * exp
 | Sigma of ident * exp * exp
 | Nat
 | Set
 | Unit
 | Lam of ident * exp
 | App of exp * exp
 | Var of idx
 | Zero
 | Suc of exp
 | Plus of exp * exp
 | NatRec of exp * exp * ident * exp
