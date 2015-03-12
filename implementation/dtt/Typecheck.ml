open AbsSyntax
module V = Value

exception IllTyped

let equal vtp vtp' = [] (* TODO *)

let solvable gamma eqns = () (* TODO *)

let rec chk sigma gamma =
  let rec chk' = function
  | (Lam (x, e), V.Fun (a, f)) -> chk sigma ((x, a)::gamma) (e, V.vapp sigma (f, V.Neu (x,V.Emp)))
  | (App (id, sp), a) ->
    let vtp = synthIdType id in
    let vtpr = chkSp (sp, vtp) in
    let eqns = equal vtpr a in
    solvable gamma eqns
  | (Id id, a) -> chk' (App (id, []), a)
  | (Type, V.Type) -> ()
  | (Pi (x,a,b), V.Type) | (Sigma (x,a,b), V.Type) ->
    chk' (a,V.Type); chk sigma ((x,V.eval sigma a)::gamma) (b, V.Type)
  | (Arr (a,b), V.Type) -> chk' (a,V.Type); chk' (b,V.Type)
  and chkSp = function
    | []    , a            -> a
    | t::ts , V.Fun (a, f) -> chk' (t,a); chkSp (ts, V.vapp sigma (f, V.eval sigma t))
  and synthIdType id =
    try match V.lookuptp sigma id with
      | V.Constr vtp -> vtp
      | V.Def (vtp, _) -> vtp
    with V.Free -> try V.lookuptp gamma id with V.Free -> raise V.Violation
  in chk'

let rec chkPat sigma (p,tp) = match p with
  | App (ident,ps) ->
    let V.Constr vtp = V.lookuptp sigma ident in 
    let (gamma1, vtp') = chkPats sigma (ps, vtp) in
    let eqns = equal vtp' tp in
    (gamma1@eqns)
  | Id ident ->
    try let V.Constr vtp = V.lookuptp sigma ident in equal vtp tp
    with V.Free -> [(ident,tp)] (* It's a variable *)

and chkPat1 sigma p a f =
  let gamma1 = chkPat sigma (p,a) in
  let p' = V.eval sigma p in
  let vtp0 = V.vapp sigma (f, p') in
  (gamma1,vtp0)

and chkPats sigma = function
  | ([], a) -> ([], a)
  | (p::ps, V.Fun (a,f)) ->
    let (gamma1,vtp0) = chkPat1 sigma p a f in
    let (gamma2,vtp') = chkPats sigma (ps, vtp0) in
    (gamma1@gamma2, vtp')
  | (p::ps, _) -> raise IllTyped

let chkBranch sigma (Br (ps,e)) vtp =
  let (gamma,vtp') = chkPats sigma (ps,vtp) in
  chk sigma gamma (e, vtp')

let rec chkDecl sigma = function
  | (Def (name,tp,body)) ->
     chk sigma [] (tp, V.Type);
     let vtp = V.eval sigma tp in
     List.iter (fun br -> chkBranch sigma br vtp) body;
     [(name,(V.Def (vtp,body)))]
  | (Data (name, constructors)) ->
    let d = (name,V.Constr V.Type) in
     d::(List.map (fun (Con (cname, ctp)) ->
       chk (d::sigma) [] (ctp, V.Type);
       (cname,(V.Constr (V.eval sigma ctp)))) constructors)

let rec chkDeclList sigma defs = match defs with
  | [] -> ()
  | (d::ds) ->
    let vd = chkDecl sigma d in
    chkDeclList (vd@sigma) ds

let chkMod (Prog defs) = chkDeclList [] defs



