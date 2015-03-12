module E = AbsSyntax

type value =
  | Fun of tpvalue * value
  | Clo of ((E.ident * E.exp) * env)
  | Sigma of tpvalue * value
  | Type
  | ConApp of E.ident * spine
  | DefApp of E.ident * spine
  | Neu of E.ident * spine
and env =
    Id
  | Empty
  | Dot of env * (value * E.ident)
and spine =
    Emp
  | Snoc of spine * value

and tpvalue = value

type idsort = DefI | ConI | VarI

type decl =
    Def of tpvalue * E.branch list
  | Constr of tpvalue

exception Free
let rec lookuptp sigma c = match sigma with
  | [] -> raise Free
  | (y,d)::sigma' when c = y -> d
  | (_,_)::sigma' -> lookuptp sigma' c

let rec lookupenv (rho, x) = match rho with
  | Empty -> raise Free
  | Dot (rho, (v,y)) when x = y -> v
  | Dot (rho,   _  ) -> lookupenv (rho, x)
  | Id -> Neu (x, Emp)

let disambiguate sigma x rho =
  try
    begin match lookuptp sigma x with
    | Def (_,_) -> DefApp (x,Emp)
    | Constr _  -> ConApp (x,Emp)
    end
  with Free -> lookupenv (rho, x)

let rec append sp = function
  | [] -> sp
  | (v::vs) -> append (Snoc (sp, v)) vs

exception NotImplemented
exception Violation
let rec reduce sigma = function
  | (v, []) -> v
  | (Clo ((x,t),rho), v::vs) -> reduce sigma (eval' sigma t (Dot (rho, (v,x))), vs)
  | (Neu (x,sp), vs) -> Neu (x, append sp vs)
  | (DefApp (f,s), v) -> raise NotImplemented (* defapp sigma f (Snoc (s,v)) *)
  | (ConApp (c,sp), vs) -> ConApp (c, append sp vs)
(* and defapp sigma (_name, Def (_tp,body)) sp = raise NotImplemented *)
and eval' sigma t rho = match t with
  | E.Pi (x,a,b) -> Fun (eval' sigma a rho, Clo ((x,b), rho))
  | E.Arr (a,b) -> Fun (eval' sigma a rho, Clo ((E.Ident "_",b),rho))
  | E.Type -> Type
  | E.Lam (ident,t) -> Clo ((ident,t), rho)
  | E.App (ident,spine) -> reduce sigma (disambiguate sigma ident rho, evalspine sigma spine rho)
  | E.Id ident -> disambiguate sigma ident rho
and evalspine sigma s rho = match s with
  | [] -> []
  | t::ts -> (eval' sigma t rho)::(evalspine sigma ts rho)

let vapp sigma (f,v) = reduce sigma (f, v::[])

let eval sigma t = eval' sigma t Id
