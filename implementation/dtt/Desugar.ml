module Abs = AbsSyntax
module Int = IntSyntax

exception UnboundVar of Abs.ident

let rec index = function
  | Abs.Mod (n, ds) -> Int.Mod (n, index_decls [] ds)

and index_decls sigma = function
  | [] -> []
  | d::ds -> (index_decl sigma d)::(index_decls (d::sigma) ds)

and index_decl sigma = function
  | Abs.Def (n, tp, body) -> Int.Def (n, index_exp (sigma, []) tp, index_exp (sigma, []) body)

and index_var (sigma,vars) x =
  let rec check_sig = function
    | [] -> raise (UnboundVar x)
    | (Abs.Def (c, tp, body))::ds -> if x = c then Int.Const c else check_sig ds
  and index_var' n = function
    | [] -> check_sig sigma
    | (y::vars) -> if x = y then Int.Var n else index_var' (Int.Pop n) vars
  in index_var' Int.Top vars

and index_exp vars = function
  | Abs.Pi (x, a, b) -> Int.Pi (index_exp vars a, (x, index_exp (cons_var x vars) b))
  | Abs.Arr (a, b) -> Int.Pi (index_exp vars a, (dummy, index_exp (cons_var dummy vars) b))
  | Abs.Sigma (x, a, b) -> Int.Sigma (index_exp vars a, (x, index_exp (cons_var x vars) b))
  | Abs.Nat -> Int.Nat
  | Abs.Set -> Int.Set
  | Abs.Unit -> Int.Unit
  | Abs.Tt -> Int.Tt
  | Abs.Lam a -> Int.Lam (index_abstr vars a)
  | Abs.App (t1, t2) -> Int.App (index_exp vars t1, index_exp vars t2)
  | Abs.Var x -> index_var vars x
  | Abs.Zero -> Int.Zero
  | Abs.Suc t -> Int.Suc (index_exp vars t)
  | Abs.Plus (t1, t2) -> Int.Plus (index_exp vars t1, index_exp vars t2)
  | Abs.NatRec (tn, aC, tz, x, ih, eS) -> Int.NatRec (index_exp vars tn, index_abstr vars aC, index_exp vars tz, (x, ih, index_exp (cons_var ih (cons_var x vars)) eS))
and index_abstr vars = function 
  | Abs.Abstr (x,t) -> (x, index_exp (cons_var x vars) t)
and cons_var x (sigma,vars) = sigma, x::vars
and dummy = Abs.Ident "_"
