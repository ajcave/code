open AbsSyntax
module V = Value

type ctx = Emp | Comma of ctx * exp

type type_error = CheckSet | CheckPi | InferMismatch of exp * exp
		  | NotInferrable

exception IllTyped of type_error

(* let rec equal sigma e1 e2 = *)
(*   let rec equal e1 e2 = *)
(*   let e1 = Norm.whnf sigma e1 in *)
(*   let e2 = Norm.whnf sigma e2 in *)
(*   match (e1,e2) with *)
(*     | Const c1, Const c2 -> c1 = c2 *)
(*     | (Pi (t1,a1), Pi (t2,a2)) | (Sigma (t1,a1), Sigma (t2,a2)) *)
(*       -> equal t1 t2 && equal_abstr a1 a2 *)
(*     | Type,Type -> true *)
(*     | (Lam a1, Lam a2) -> equal_abstr a1 a2 *)
(*     | (App (ea1,ea2), App (eb1, eb2)) -> *)
(*       equal ea1 eb1 && equal ea2 eb2 *)
(*     | Var x, Var y -> x = y *)
(*     | (Pi _ | Sigma _ | Type | Lam _ | App _ *)
(*         | Var _ | Const _), _ -> false *)
(*     | Subst _ , _  -> raise (Violation "Subst should not appear in weak head normal terms") *)
(*   and equal_abstr (x,e1) (y,e2) = equal e1 e2 *)
(*   in equal e1 e2 *)

(* let rec chk_pi sigma e = *)
(*   match Norm.whnf sigma e with *)
(*     | Pi (t, (x,b)) -> (t,b) *)
(*     | Sigma _ | Type | Lam _ | Const _ *)
(*     | App _ | Var _ -> raise (IllTyped CheckPi) *)
(*     | Subst _ -> raise (Violation "Subst should not appear in weak head normal terms") *)

(* let rec lookup_ty gamma x = match (gamma,x) with *)
(*   | Emp, x -> raise (Violation "variable out of bounds") *)
(*   | Comma (gamma, a), Top -> a *)
(*   | Comma (gamma, a), (Pop x) -> lookup_ty gamma x *)

(* let rec lookup_const sigma c = match sigma with *)
(*   | [] -> raise (Violation "undefined constant") *)
(*   | (k,a,_)::ds -> if k = c then a else lookup_const ds c *)

(* let rec chk ((sigma,gamma) as ctxs) e tp = match e with *)
(*   | Lam (x, e1) -> *)
(*     let (a,b) = chk_pi sigma tp in *)
(*     chk (sigma, Comma (gamma, a)) e1 b *)
(*   | Subst (s, e) -> chk ctxs (whsubst s e) tp *)
(*   | e -> *)
(*     let a = infer ctxs e in *)
(*     if equal sigma a tp then () *)
(*     else raise (IllTyped (InferMismatch (a,tp))) *)
(* and infer ((sigma,gamma) as ctxs) e = match e with *)
(*   | Type -> Type *)
(*   | Pi (a,(x,b)) | Sigma (a,(x,b)) -> chk ctxs a Type; chk (sigma, Comma (gamma, a)) b Type; Type *)
(*   | Var x -> lookup_ty gamma x *)
(*   | Const c -> lookup_const sigma c *)
(*   | App (e1,e2) -> *)
(*     let (a,b) = chk_pi sigma (infer ctxs e1) in *)
(*     chk ctxs e2 a; subst1 e2 b *)
(*   | Subst (s, e) -> infer ctxs (whsubst s e) (\* This case is slightly weird *\) *)
(*   | Lam _ -> raise (IllTyped NotInferrable) *)

let equal vtp vtp' = [] (* TODO *)

let chk (sigma,gamma) e vtp = () (* TODO *)

let rec chkPat sigma = function
  | (App (ident,ps), tp) ->
    try
	let V.Constr vtp = V.lookuptp sigma ident in 
	let (gamma1, vtp') = chkPats sigma (ps, vtp) in
	let eqns = equal vtp vtp' in
	  (gamma1@eqns)
    with V.LookupFailure -> (* Interpret it as a variable binding *)
      let [] = ps in
      [(ident,tp)]

and chkPats sigma = function
  | ([],vtp) -> ([],vtp)
  | (p::ps, V.Fun (a,f)) ->
    let gamma1 = chkPat sigma (p,a) in
    let p' = V.eval sigma p in
    let (gamma2,vtp') = chkPats sigma (ps, V.vapp sigma (f, p')) in
    (gamma1@gamma2, vtp')
  | (p::ps, _) -> raise (IllTyped CheckPi)

let chkBranch sigma (Br (ps,e)) vtp =
  let (gamma,vtp') = chkPats sigma (ps,vtp) in
  chk (sigma,gamma) e vtp'  

let rec chkDecl sigma = function
  | (Def (name,tp,body)) ->
     chk (sigma,[]) tp Type;
     let vtp = V.eval sigma tp in
     List.iter (fun br -> chkBranch sigma br vtp) body;
     [(name,(V.Def (vtp,body)))]
  | (Data (name, constructors)) ->
     (name,V.Constr V.Type)::(List.map (fun (Con (cname, ctp)) ->
       chk (sigma,[]) ctp Type;
       (cname,(V.Constr (V.eval sigma ctp)))) constructors)

let rec chkDeclList sigma defs = match defs with
  | [] -> ()
  | (d::ds) ->
    let vd = chkDecl sigma d in
    chkDeclList (vd@sigma) ds

let chkMod (Prog defs) = chkDeclList [] defs



