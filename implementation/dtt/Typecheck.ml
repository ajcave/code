open AbsSyntax
module V = Value

exception IllTyped

type 'a slist = Nil | Snoc of 'a slist * 'a
type judgment = Oft of ident * V.tpvalue | ChkPat of exp * ident * V.tpvalue

let rec lookuptp' gamma x = match gamma with
  | Nil -> raise V.Free
  | Snoc (gamma', Oft (y, vtp)) when x = y -> vtp
  | Snoc (gamma', _) -> lookuptp' gamma' x

let rec equal = function
  | V.ConApp (id1,sp1), V.ConApp (id2,sp2) when id1 = id2 -> equalSp (sp1,sp2)
  | V.Type , V.Type -> []
  | V.Neu (x1, sp1), V.Neu (x2, sp2) when x1 = x2 -> equalSp (sp1, sp2)
  | V.Neu (x, V.Emp) , v | v , V.Neu (x, V.Emp) -> [x,v]
  | v1 , v2 ->
    raise V.NotImplemented
and equalSp = function
  | V.Emp, V.Emp -> []
  | V.Snoc (sp1, v1), V.Snoc (sp2, v2) -> (equalSp (sp1,sp2)) @ (equal (v1,v2))

let solvable gamma xs = () (* TODO *)

let rec chk sigma gamma =
  (* TODO: Bug: matching directly on the type here isn't good enough if we intend to do
     eta expansion for singleton types *)
  let rec chk' = function
  | (Lam (x, e), V.Fun (a, f)) -> chk sigma (Snoc (gamma, Oft (x, a))) (e, V.vapp sigma (f, V.Neu (x,V.Emp)))
  | (App (id, sp), a) ->
    let vtp = synthIdType id in
    let vtpr = chkSp (sp, vtp) in
    let eqns = equal (vtpr, a) in
    solvable gamma eqns
  | (Id id, a) -> chk' (App (id, []), a)
  | (Type, V.Type) -> ()
  | (Pi (x,a,b), V.Type) -> chk' (a,V.Type); chk sigma (Snoc (gamma, Oft (x,V.eval sigma a))) (b, V.Type)
  | (Arr (a,b), V.Type) ->  chk' (a,V.Type); chk' (b,V.Type)
  and chkSp = function
    | []    , a            -> a
    | t::ts , V.Fun (a, f) -> chk' (t,a); chkSp (ts, V.vapp sigma (f, V.eval sigma t))
  and synthIdType id =
    try match V.lookuptp sigma id with
      | V.Constr vtp -> vtp
      | V.Def (vtp, _) -> vtp
    with V.Free -> try lookuptp' gamma id with V.Free -> raise V.Violation
  in chk'

exception IllTypedPattern

let applyEqn g (u,v) = g , [] (* TODO! (First-order) unification (see "equal" above) *)

let rec applyEqns g = function
  | (V.Emp,V.Emp) -> g , []
  | (V.Snoc (us, u), V.Snoc (vs, v)) ->
    let g' , bindings = applyEqns g (us,vs) in (* The bindings should have already been applied to g'.. *)
    let g'' , bindings' = applyEqn g' (u,v) in
    g'' , (bindings@bindings')

and addPats sigma g0 xs = function
  | [] , a -> g0 , xs , a
  | p::ps , V.Fun (a, f) ->
    let x = V.gensym () in
    let xv = V.Neu (x, V.Emp) in
    addPats sigma (Snoc (g0, ChkPat (p, x, a))) (V.Snoc (xs, xv)) (ps, V.vapp sigma (f, xv))

and chkConstrPat sigma (g0, (c, ps), x, a) =
  let V.Constr vtp = V.lookuptp sigma c in 
  let g0' , xs , V.ConApp (d, sp) = addPats sigma g0 V.Emp (ps, vtp) in 
  let V.ConApp (d',vs) = a in
  if d <> d' then raise IllTypedPattern;
  let g0'', bindings = applyEqns g0' (sp,vs) in
  g0'', (x, V.ConApp (c, xs))::bindings

and chkPat' sigma (g0, p, x, a) = match p with
  | App (c,ps) -> chkConstrPat sigma (g0, (c, ps), x, a)
    (* This also needs to be able to raise "stuck" which will just keep the original problem *)
  | Id z ->
    try chkConstrPat sigma (g0, (z, []), x, a) (* If it's a constructor.. *)
    with V.Free -> Snoc (g0, Oft (z,a)) , [(x,V.Neu (z, V.Emp))] (* It's a variable *)

and processJudgment sigma (g0,j) = match j with
  | ChkPat (p,x,a) -> chkPat' sigma (g0, p, x, a)
  | Oft (x,a) -> Snoc (g0, Oft (x,a)), []

and applyInstJ inst j = j (* TODO *)
and applyInstT inst tp = tp (* TODO *)

and traverseChkPats sigma = function
  | (g0,[]), p::ps, V.Fun (a,f) ->
    let x = V.gensym () in
    traverseChkPats sigma ((g0,[ChkPat (p,x,a)]), ps, V.vapp sigma (f, V.Neu (x, V.Emp)))
    (* TODO: V.app will need g0 also, which might supply bindings for some variables*)
  | (g0,[]), ps, a -> (g0,[]), ps, a (* Stuck until we learn about 'a', or ps is done *)
  | (g0,j::js), ps, vtp -> 
    let (g0', inst) = processJudgment sigma (g0,j) in
    traverseChkPats sigma ((g0',List.map (applyInstJ inst) js), ps, applyInstT inst vtp)

and complete = function
  | Nil -> true
  | Snoc (g, Oft (_x, _a)) -> complete g
  | Snoc (g, _) -> false

and rev g acc = match g with
  | Nil -> acc
  | Snoc (g, j) -> rev g (j::acc)

and chkPats sigma state =
 let state' = traverseChkPats sigma state in
 match state' with
   | (g',[]), [] , a when complete g' -> g', a
   | (g',js), ps , a -> chkPats sigma ((Nil, rev g' js), ps , a)
   (* TODO: Need to detect stuck states and raise an error *)

let chkBranch sigma (recname,rectyp) (Br (ps,e)) vtp =
  let (gamma,vtp') = chkPats sigma ((Nil,[]), ps, vtp) in
  chk sigma (Snoc (gamma, Oft (recname ,rectyp))) (e, vtp')

let rec chkDecl sigma = function
  | (Def (name,tp,body)) ->
     chk sigma Nil (tp, V.Type);
     let vtp = V.eval sigma tp in
     List.iter (fun br -> chkBranch sigma (name,vtp) br vtp) body;
     [(name,(V.Def (vtp,body)))]
  | (Data (name, tp, constructors)) ->
    chk sigma Nil (tp, V.Type);
    let d = (name,V.Constr (V.eval sigma tp)) in
     d::(List.map (fun (Con (cname, ctp)) ->
       chk (d::sigma) Nil (ctp, V.Type);
       (cname,(V.Constr (V.eval (d::sigma) ctp)))) constructors)

let rec chkDeclList sigma defs = match defs with
  | [] -> ()
  | (d::ds) ->
    let vd = chkDecl sigma d in
    chkDeclList (vd@sigma) ds

let chkMod (Prog defs) = chkDeclList [] defs



