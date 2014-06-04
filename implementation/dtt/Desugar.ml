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
  | Abs.Pi (x, a, b) -> Int.Pi (x, index_exp vars a, index_exp (x::vars) b)
  | Abs.Sigma (x, a, b) -> Int.Sigma (x, index_exp vars a, index_exp (x::vars) b)
  | Abs.Nat -> Int.Nat
  | Abs.Set -> Int.Set
  | Abs.Unit -> Int.Unit
  | Abs.Lam (x, t) -> Int.Lam (x, index_exp (x::vars) t)
  | Abs.App (t1, t2) -> Int.App (index_exp vars t1, index_exp vars t2)
  | Abs.Var x -> Int.Var (index_var vars x)
  | Abs.Zero -> Int.Zero
  | Abs.Suc t -> Int.Suc (index_exp vars t)
  | Abs.Plus (t1, t2) -> Int.Plus (index_exp vars t1, index_exp vars t2)
  | Abs.NatRec (t1, t2, x, t3) -> Int.NatRec (index_exp vars t1, index_exp vars t2, x, index_exp (x::vars) t3)

