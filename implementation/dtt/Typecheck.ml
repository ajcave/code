open IntSyntax
module Norm = Whnf

type signature = SigEmp | SigComma of signature*(ident*exp*exp)
type ctx = Emp | Comma of ctx * exp

type type_error = CheckSet | CheckPi | InferMismatch of exp * exp
		  | NotInferrable

exception IllTyped of type_error
exception Violation of string

let rec equal sigma e1 e2 =
  let rec equal e1 e2 =
  let e1 = Norm.whnf sigma e1 in
  let e2 = Norm.whnf sigma e2 in
  match (e1,e2) with
    | (Pi (t1,a1), Pi (t2,a2)) | (Sigma (t1,a1), Sigma (t2,a2))
      -> equal t1 t2 && equal_abstr a1 a2
    | (Nat,Nat) | (Set,Set) | (Unit,Unit) | (Zero,Zero) -> true
    | (Lam a1, Lam a2) -> equal_abstr a1 a2
    | (Suc e1, Suc e2) -> equal e1 e2
    | (App (ea1,ea2), App (eb1, eb2)) | Plus (ea1, ea2), Plus (eb1, eb2) ->
      equal ea1 eb1 && equal ea2 eb2
    | NatRec (en,aC,ez,(x,ih,eS)), NatRec (en',aC',ez',(x',ih',eS')) ->
      equal en en' && equal_abstr aC aC' && equal ez ez' && equal eS eS'
    | Var x, Var y -> x = y
    | (Pi _ | Sigma _ | Nat | Set | Unit | Lam _ | App _ | Var _ | Zero | Suc _ | Plus _ | NatRec _), _ -> false
    | Subst _ , _  -> raise (Violation "Subst should not appear in weak head normal terms")
  and equal_abstr a1 a2 = match (a1,a2) with
    | (x,e1), (y,e2) -> equal e1 e2
  in equal e1 e2

let rec chk_pi sigma e =
  match Norm.whnf sigma e with
    | Pi (t, (x,b)) -> (t,b)
    | Sigma _ | Nat | Set | Unit | Lam _ | Zero
    | App _ | Var _ | Suc _ | Plus _ | NatRec _ -> raise (IllTyped CheckPi)
    | Subst _ -> raise (Violation "Subst should not appear in weak head normal terms")

let rec lookup_ty gamma x = match (gamma,x) with
  | Emp, x -> raise (Violation "variable out of bounds")
  | Comma (gamma, a), Top -> a
  | Comma (gamma, a), (Pop x) -> lookup_ty gamma x

let rec chk ((sigma,gamma) as ctxs) e tp = match e with
  | Lam (x, e1) ->
    let (a,b) = chk_pi sigma tp in
    chk (sigma, Comma (gamma, a)) e1 b
  | Subst (s, e) -> chk ctxs (whsubst s e) tp
  | e ->
    let a = infer ctxs e in
    if equal sigma a tp then ()
    else raise (IllTyped (InferMismatch (a,tp)))
and infer ((sigma,gamma) as ctxs) e = match e with
  | Set | Nat | Unit -> Set
  | Zero -> Nat
  | Suc t -> chk ctxs t Nat; Nat
  | Pi (a,(x,b)) | Sigma (a,(x,b)) -> chk ctxs a Set; chk (sigma, Comma (gamma, a)) b Set; Set
  | Var x -> lookup_ty gamma x
  | App (e1,e2) ->
    let (a,b) = chk_pi sigma (infer ctxs e1) in
    chk ctxs e2 a; subst1 e2 b
  | NatRec (en, (x,eC), ez, (y,ih,eS)) ->
    chk ctxs en Nat;
    chk (sigma, Comma (gamma, Nat)) eC Set;
    chk ctxs ez (subst1 Zero eC);
    chk (sigma, Comma (Comma (gamma, Nat), eC)) eS (subst shift1 eC);
    subst1 en eC
  | Plus (e1, e2) -> chk ctxs e1 Nat; chk ctxs e2 Nat; Nat
  | Subst (s, e) -> infer ctxs (whsubst s e) (* This case is slightly weird *)
  | Lam _ -> raise (IllTyped NotInferrable)

let rec chkDecl ctxs (Def (name,tp,body)) = chk ctxs tp Set; chk ctxs body tp

let rec chkDeclList (sigma,gamma) defs = match defs with
  | [] -> true
  | ((Def (n,t,b)) as d::ds) ->
    chkDecl (sigma,gamma) d;
    chkDeclList (SigComma (sigma,(n,t,b)), gamma) ds

let chkMod (Mod (name,defs)) = chkDeclList (SigEmp,Emp) defs



