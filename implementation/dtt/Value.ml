module E = AbsSyntax

type value =
  | Fun of tpvalue * value
  | Clo of ((E.ident * E.exp) * env)
  | Type
  | ConApp of E.ident * spine
  | DefApp of E.ident * spine
  | Neu of E.ident * spine
and env =
    Empty
  | Dot of env * (value * E.ident)
and spine =
    Emp
  | Snoc of spine * value

and tpvalue = value

type idsort = DefI | ConI | VarI

type decl =
    Def of tpvalue * E.branch list
  | Constr of tpvalue

let gensym =
  let i = ref 0 in
  fun () -> i := !i + 1; E.Ident ("_x" ^ string_of_int !i)

exception Free
let rec lookuptp sigma c = match sigma with
  | [] -> raise Free
  | (y,d)::sigma' when c = y -> d
  | (_,_)::sigma' -> lookuptp sigma' c

let rec lookupenv (rho, x) = match rho with
  | Empty -> raise Free
  | Dot (rho, (v,y)) when x = y -> v
  | Dot (rho,   _  ) -> lookupenv (rho, x)

let disambiguate sigma x rho =
  try
    begin match lookuptp sigma x with
    | Def (_,_) -> DefApp (x,Emp)
    | Constr _  -> ConApp (x,Emp)
    end
  with Free -> lookupenv (rho, x)

let isConstr sigma x = try lookuptp sigma x; true with Free -> false
let isVar sigma x = not (isConstr sigma x)

let rec append sp = function
  | [] -> sp
  | (v::vs) -> append (Snoc (sp, v)) vs

exception NotImplemented
exception Violation
exception MatchFailed

type 'a option = None | Some of 'a

let rec appendEnv rho1 = function
  | Empty -> rho1
  | Dot (rho2, vx) -> Dot (appendEnv rho1 rho2, vx)

let rec rev acc = function
  | Emp -> acc
  | Snoc (sp, v) -> rev (v::acc) sp

let rec computeMatch sigma = function
  | E.App (c1, ps) , ConApp (c2 , vs) when c1 = c2 -> computeMatches sigma (ps, (rev [] vs))
  | E.Id c1 , ConApp (c2, Emp) when isConstr sigma c1 && c1 = c2 -> Empty
  | E.Id x , v when isVar sigma x -> Dot (Empty, (v, x))
  | _ , _ -> raise MatchFailed

and computeMatches sigma = function
  | [] , [] -> Empty
  | p::ps , v::vs -> appendEnv (computeMatch sigma (p, v)) (computeMatches sigma (ps, vs))

let rec reduce sigma = function
  | (v, []) -> v
  | (Clo ((x,t),rho), v::vs) -> reduce sigma (eval' sigma t (Dot (rho, (v,x))), vs)
  | (Neu (x,sp), vs) -> Neu (x, append sp vs)
  | (DefApp (f,sp), vs) -> defapp sigma f (append sp vs)
  | (ConApp (c,sp), vs) -> ConApp (c, append sp vs)
and defapp sigma f sp =
  let Def (_,body) = lookuptp sigma f in
  let args = rev [] sp in
  let rec applyBranch = function
    | [] -> DefApp (f, sp) (* Still stuck *)
    | (E.Br (pats, body))::brs ->
      try eval' sigma body (computeMatches sigma (pats, args))
      with MatchFailed -> applyBranch brs
  in applyBranch body
and eval' sigma t rho = match t with
  | E.Pi (x,a,b) -> Fun (eval' sigma a rho, Clo ((x,b), rho))
  | E.Arr (a,b) -> Fun (eval' sigma a rho, Clo ((gensym (),b),rho))
  | E.Type -> Type
  | E.Lam (ident,t) -> Clo ((ident,t), rho)
  | E.App (ident,spine) -> reduce sigma (disambiguate sigma ident rho, evalspine sigma spine rho)
  | E.Id ident -> disambiguate sigma ident rho
and evalspine sigma s rho = match s with
  | [] -> []
  | t::ts -> (eval' sigma t rho)::(evalspine sigma ts rho)

let vapp sigma (f,v) = reduce sigma (f, v::[])

let rec vappSp sigma f = function
  | Emp -> f
  | Snoc (sp, v) -> vapp sigma (vappSp sigma f sp, v)

