module Abs = AbsSyntax
module Int = IntSyntax

exception UnboundVar of Abs.ident

let rec index = function
  | Abs.Mod (n, ds) -> Int.Mod (n, List.map index_decl ds)

and index_decl = function
  | Abs.Def (n, tp, body) -> Int.Def (n, index_exp [] tp, index_exp [] body)

and index_var vars x = 
  let rec index_var' n = function
    | [] -> raise (UnboundVar x)
    | (y::vars) -> if x = y then n else index_var' (Int.Pop n) vars
  in index_var' Int.Top vars

and index_exp vars = function
  | Abs.Pi (x, a, b) -> Int.Pi (index_exp vars a, (x, index_exp (x::vars) b))
  | Abs.Sigma (x, a, b) -> Int.Sigma (index_exp vars a, (x, index_exp (x::vars) b))
  | Abs.Nat -> Int.Nat
  | Abs.Set -> Int.Set
  | Abs.Unit -> Int.Unit
  | Abs.Tt -> Int.Tt
  | Abs.Lam a -> Int.Lam (index_abstr vars a)
  | Abs.App (t1, t2) -> Int.App (index_exp vars t1, index_exp vars t2)
  | Abs.Var x -> Int.Var (index_var vars x)
  | Abs.Zero -> Int.Zero
  | Abs.Suc t -> Int.Suc (index_exp vars t)
  | Abs.Plus (t1, t2) -> Int.Plus (index_exp vars t1, index_exp vars t2)
  | Abs.NatRec (tn, aC, tz, x, ih, eS) -> Int.NatRec (index_exp vars tn, index_abstr vars aC, index_exp vars tz, (x, ih, index_exp (ih::x::vars) eS))
and index_abstr vars = function 
  | Abs.Abstr (x,t) -> (x, index_exp (x::vars) t)
