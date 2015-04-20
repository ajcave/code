open AbsSyntax
module V = Value

exception IllTyped

let rec equal = function
  | V.ConApp (id1,sp1), V.ConApp (id2,sp2) when id1 = id2 -> equalSp (sp1,sp2)
  | V.Type , V.Type -> []
  | V.Neu (x1, sp1), V.Neu (x2, sp2) when x1 = x2 -> equalSp (sp1, sp2)
  | V.Neu (x, V.Emp) , v | v , V.Neu (x, V.Emp) -> [x,v]
  | v1 , v2 ->
    (if v1 = v2 then
      []
    else
      []);
    raise V.NotImplemented
and equalSp = function
  | V.Emp, V.Emp -> []
  | V.Snoc (sp1, v1), V.Snoc (sp2, v2) -> (equalSp (sp1,sp2)) @ (equal (v1,v2))

let solvable gamma [] = () (* TODO *)

let rec chk sigma gamma =
  (* TODO: Bug: matching directly on the type here isn't good enough if we intend to do
     eta expansion for singleton types *)
  let rec chk' = function
  | (Lam (x, e), V.Fun (a, f)) -> chk sigma ((x, a)::gamma) (e, V.vapp sigma (f, V.Neu (x,V.Emp)))
  | (App (id, sp), a) ->
    let vtp = synthIdType id in
    let vtpr = chkSp (sp, vtp) in
    let eqns = equal (vtpr, a) in
    solvable gamma eqns
  | (Id id, a) -> chk' (App (id, []), a)
  | (Type, V.Type) -> ()
  | (Pi (x,a,b), V.Type) -> chk' (a,V.Type); chk sigma ((x,V.eval sigma a)::gamma) (b, V.Type)
  | (Arr (a,b), V.Type) ->  chk' (a,V.Type); chk' (b,V.Type)
  and chkSp = function
    | []    , a            -> a
    | t::ts , V.Fun (a, f) -> chk' (t,a); chkSp (ts, V.vapp sigma (f, V.eval sigma t))
  and synthIdType id =
    try match V.lookuptp sigma id with
      | V.Constr vtp -> vtp
      | V.Def (vtp, _) -> vtp
    with V.Free -> try V.lookuptp gamma id with V.Free -> raise V.Violation
  in chk'

(* let rec applyEqn ((y,v) as eq) = function *)
(*   | [] -> [] *)
(*   | (x,tp)::gamma when x = y -> (x, V.Singleton (v,tp))::gamma *)
(*   | b::gamma -> b::(applyEqn eq gamma) *)

(* let rec applyEqns gamma = function *)
(*   | [] -> gamma *)
(*   | eq::eqns -> applyEqn eq (applyEqns gamma eqns) *)

type 'a slist = Nil | Snoc of 'a * 'a slist
type judgment = Oft of E.Ident * V.tpvalue | ChkPat of E.exp * E.Ident * V.tpvalue

(* let rec chkPat sigma (p,tp) = match p with *)
(*   | App (ident,ps) -> *)
(*     let V.Constr vtp = V.lookuptp sigma ident in  *)
(*     let (gamma1, vtp') = chkPats sigma (ps, vtp) in *)
(*     let eqns = equal (vtp', tp) in *)
(*     (applyEqns gamma1 eqns) (\* TODO: BUG: Aren't we applying these too eagerly? *)
(* 			       We might need to apply them to bindings we don't have yet?*\) *)
(*   | Id ident -> *)
(*     try let V.Constr vtp = V.lookuptp sigma ident in equal (vtp, tp) *)
(*     with V.Free -> [(ident,tp)] (\* It's a variable *\) *)

(* and chkPat1 sigma p a f = *)
(*   let gamma1 = chkPat sigma (p,a) in *)
(*   let p' = V.eval sigma p in *)
(*   let vtp0 = V.vapp sigma (f, p') in *)
(*   (gamma1,vtp0) *)

and chkPat' sigma (g0, p, x, a) = match p with
  | App (c,ps) ->
    let V.Constr vtp = V.lookuptp sigma c in 
    let (g0',[]), [], V.ConApp (d,sp) = traverseChkPats sigma ((g0,[]), ps, vtp) in
     (* Crap, in general this is going to learn some instantiations which we are going to need
        to propagate out. So we shouldn't reuse traverseChkPats? 
        Or we should generalize it... *)
    let V.ConApp (d',vs) = a in
    applyEqns g0' (sp,vs) , Bind (x, V.ConApp (c, ???)) (* Should be the list of variables we bound. Actually, compose it with the equations we learned from the body? *)
      (* Maybe we shouldn't actually go deeper into the body eagerly? Just add the postponed things*)
      (* This also needs to be able to say "stuck" by just returning the original problem *)
  | Id z ->
    try let V.Constr vtp = V.lookuptp sigma z in equal (vtp, a)
    with V.Free -> Snoc (g0, Oft (z,a)) , Bind (x,z) (* It's a variable *)

and processJudgment sigma (g0,j) = match j with
  | ChkPat (p,x,a) -> chkPat' sigma (g0, p, x, a)
  | Oft (x,a) -> Snoc (g0, Oft (x,a)), Id

and traverseChkPats sigma = function
  | (g0,[]), p::ps, V.Fun (a,V.Clo (x,b,rho) as f) ->
    traverseChkPats sigma ((g0,[ChkPat (p,x,a)]), ps, V.vapp sigma (f, V.Neu (x, V.Emp))) (* TODO: This will need g0 also, which might supply bindings for some variables*)
  | (g0,[]), ps, a) -> (g0,[]), ps, a (* Stuck until we learn about 'a', or ps is done *)
  | (g0,j::js), ps, vtp -> 
    let (g0', inst) = processJudgment sigma (g0,j) in
    traverseChkPats sigma ((g0',map (applyInstJ inst js)), ps, applyInstT inst vtp)
(* Idea is to repeat traverseChkPats until we no longer make any progress.
   If it's done, then check body
   If it's stuck, fail. *)

(* and chkPats sigma = function *)
(*   | ([], a) -> ([], a) *)
(*   | (p::ps, V.Fun (a,f)) -> *)
(*     let (gamma1,vtp0) = chkPat1 sigma p a f in *)
(*     let (gamma2,vtp') = chkPats sigma (ps, vtp0) in (\* Might need to use the equations gathered from p here? *)
(* 		       Yes: if the next type is by large elim on a previous thing *\) *)
(*     (gamma2@gamma1, vtp') (\* We should check disjointness here *\) *)
(*   | (p::ps, _) -> raise IllTyped *)

let chkBranch sigma gamma0 (Br (ps,e)) vtp =
  let (gamma,vtp') = chkPats sigma [] (ps,vtp) in
  chk sigma (gamma@gamma0) (e, vtp')

let rec chkDecl sigma = function
  | (Def (name,tp,body)) ->
     chk sigma [] (tp, V.Type);
     let vtp = V.eval sigma tp in
     List.iter (fun br -> chkBranch sigma [Oft (name,vtp)] br vtp) body;
     [(name,(V.Def (vtp,body)))]
  | (Data (name, tp, constructors)) ->
    chk sigma [] (tp, V.Type);
    let d = (name,V.Constr (V.eval sigma tp)) in
     d::(List.map (fun (Con (cname, ctp)) ->
       chk (d::sigma) [] (ctp, V.Type);
       (cname,(V.Constr (V.eval (d::sigma) ctp)))) constructors)

let rec chkDeclList sigma defs = match defs with
  | [] -> ()
  | (d::ds) ->
    let vd = chkDecl sigma d in
    chkDeclList (vd@sigma) ds

let chkMod (Prog defs) = chkDeclList [] defs



