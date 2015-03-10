module E = AbsSyntax

type value = 
    Fun of value * value
  | Clo of (ident * E.Exp) * env
  | Sigma of value * value
  | Type
  | Constr of E.ident * spine
  | DefApp of E.ident * spine
  | Neu of E.ident * spine
and env =
  | Id
  | Empty
  | Dot of env * (value * E.ident)
and spine =
  | Emp
  | Snoc of spine * value   

let rec lookup = function
  | 

exception NotImplemented
let rec vapp sigma = function
  | (Clo ((x,t),rho), v) -> eval' sigma t (rho, (v,x))
  | (Neu (x,s), v) -> Neu (x, Snoc (s,v))
  | (DefApp (f,s), v) -> defapp sigma (lookup (sigma, f)) (Snoc (s,v))
  | (Constr (c,s), v) -> Constr (c, Snoc (s,v))
and defapp sigma (Def (_name,_tp,body)) sp = raise NotImplemented
and eval' sigma t rho = match t with
  | E.Pi (x,a,b) -> Fun (eval' sigma a rho, Clo ((x,b), rho))
  | E.Arr (a,b) -> Fun (eval' sigma a rho, Clo (("_",b),rho))
  | E.Sigma (x,a,b) -> Sigma (eval' sigma a rho, Clo ((x,b), rho))
  | E.Type -> Type
  | E.Lam abstr -> Clo (abstr, rho)
  | E.App (t1,t2) -> vapp sigma (eval' sigma t1 rho, eval' sigma t2 rho)
  | E.Id x -> 

let eval sigma t = eval' sigma t Id
