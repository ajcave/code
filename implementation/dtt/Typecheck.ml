open AbsSyntax

type signature = SigEmp | SigComma of signature*(ident*exp*exp)
type ctx = Emp | Comma of ctx * (exp * exp)

let rec chk ctxs e tp = true

let rec chkDecl ctxs (Def (name,tp,body)) = chk ctxs tp Set && chk ctxs body tp

let rec chkDeclList (sigma,gamma) defs = match defs with
  | [] -> true
  | ((Def (n,t,b)) as d::ds) ->
    (chkDecl (sigma,gamma) d)
    && (chkDeclList (SigComma (sigma,(n,t,b)), gamma) ds)

let chkMod (Mod (name,defs)) = chkDeclList (SigEmp,Emp) defs


