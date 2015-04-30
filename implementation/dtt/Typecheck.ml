open AbsSyntax
module V = Value

exception IllTyped

type 'a slist = Nil | Snoc of 'a slist * 'a
type judgment =
    Oft of ident * V.tpvalue
  | OftBind of ident * V.value * V.tpvalue
  | ChkPat of exp * ident * V.tpvalue
  | ChkPatBind of exp * ident * V.value * V.tpvalue
type 'a option = None | Some of 'a

let rec lookuptp' gamma x = match gamma with
  | Nil -> raise V.Free
  | Snoc (gamma', Oft (y, vtp)) when x = y -> vtp
  | Snoc (gamma', OftBind (y, v, vtp)) when x = y -> vtp
  | Snoc (gamma', _) -> lookuptp' gamma' x

let valof = function
  | Oft (x,_) -> V.Neu (x, V.Emp) , x
  | OftBind (x,v,_) -> v , x

(* Bug: when we pull things past shadowing variables? *)
let rec idenv = function
  | Nil -> V.Empty
  | Snoc (g, j) -> V.Dot (idenv g, valof j)

let eval sigma g t = V.eval' sigma t (idenv g)

let rec equal sigma = function
  | V.ConApp (id1,sp1), V.ConApp (id2,sp2) when id1 = id2 -> equalSp sigma (sp1,sp2)
  | V.Type , V.Type -> []
  | V.Neu (x1, sp1), V.Neu (x2, sp2) when x1 = x2 -> equalSp sigma (sp1, sp2)
  | V.DefApp (f1, sp1) , V.DefApp (f2, sp2) when f1 = f2 -> equalSp sigma (sp1, sp2)
  | V.Fun (a1, f1) , V.Fun (a2, f2) -> (equal sigma (a1, a2)) @ (equal sigma (f1, f2))
  | (V.Clo c1 as f1), (V.Clo c2 as f2) -> 
    let x = V.gensym () in
    let xv = V.Neu (x, V.Emp) in
    equal sigma (V.vapp sigma (f1, xv), V.vapp sigma (f2, xv)) 
  | v1 , v2 ->
    let x = (v1 == v2) in
    raise V.NotImplemented
and equalSp sigma = function
  | V.Emp, V.Emp -> []
  | V.Snoc (sp1, v1), V.Snoc (sp2, v2) -> (equalSp sigma (sp1,sp2)) @ (equal sigma (v1,v2))

let solvable gamma [] = () (* TODO *)

let rec chk sigma gamma =
  let rec chk' = function
  | (Lam (x, e), V.Fun (a, f)) -> chk sigma (Snoc (gamma, Oft (x, a))) (e, V.vapp sigma (f, V.Neu (x,V.Emp)))
  | (App (id, sp), a) ->
    let vtp = synthIdType id in
    let vtpr = chkSp (sp, vtp) in
    let eqns = equal sigma (vtpr, a) in
    solvable gamma eqns
  | (Id id, a) -> chk' (App (id, []), a)
  | (Type, V.Type) -> ()
  | (Pi (x,a,b), V.Type) -> chk' (a,V.Type); chk sigma (Snoc (gamma, Oft (x,eval sigma gamma a))) (b, V.Type)
  | (Arr (a,b), V.Type) ->  chk' (a,V.Type); chk' (b,V.Type)
  and chkSp = function
    | []    , a            -> a
    | t::ts , V.Fun (a, f) -> chk' (t,a); chkSp (ts, V.vapp sigma (f, eval sigma gamma t))
  and synthIdType id =
    try match V.lookuptp sigma id with
      | V.Constr vtp -> vtp
      | V.Def (vtp, _) -> vtp
    with V.Free -> try lookuptp' gamma id with V.Free -> raise V.Violation
  in chk'

exception IllTypedPattern


let rec assignEqn g (x,v) = match g with
  | Snoc (g', Oft (y, a)) when x = y -> Snoc (g', OftBind (x, v, a))
  | Snoc (g', ChkPat (p, y, a)) when x = y -> Snoc (g', ChkPatBind (p, y, v, a))
  | Snoc (g', (OftBind (y, u, a) as j)) when x = y -> Snoc (applyEqn g' (u,v), j)
  | Snoc (g', (ChkPatBind (p, y, u, a) as j)) when x = y -> Snoc (applyEqn g' (u,v), j)
  | Snoc (g', j) -> Snoc (assignEqn g' (x,v), j)
(* TODO: This can form cycles; we need to check occurrences, and also move some things backward *)

and applyEqn g = function
  | V.ConApp (id1, sp1), V.ConApp (id2, sp2) when id1 = id2 -> applyEqns g (sp1, sp2)
  | V.Neu (x1, V.Emp) , V.Neu (x2, V.Emp) when x1 = x2 -> g
  | (V.Neu (x, V.Emp) , v) | (v , V.Neu (x, V.Emp)) -> assignEqn g (x,v)

and applyEqns g = function
  | (V.Emp,V.Emp) -> g
  | (V.Snoc (us, u), V.Snoc (vs, v)) ->
    let g' = applyEqns g (us,vs) in (* The bindings should have already been applied to g'.. *)
    applyEqn g' (u,v) (* we may actually need to apply the solutions we already
			 have to u,v in order to make further progress
		         or vice-versa; HO-unification is hard. *)

and addPats sigma g0 xs = function
  | [] , a -> g0 , xs , a
  | p::ps , V.Fun (a, f) ->
    let x = V.gensym () in
    let xv = V.Neu (x, V.Emp) in
    addPats sigma (Snoc (g0, ChkPat (p, x, a))) (V.Snoc (xs, xv)) (ps, V.vapp sigma (f, xv))

and chkConstrPat sigma (g0, (c, ps), x, a) =
  let V.ConApp (d',vs) = a in (* Raise Stuck if not *)
  let V.Constr vtp = V.lookuptp sigma c in 
  let g0' , xs , V.ConApp (d, sp) = addPats sigma g0 V.Emp (ps, vtp) in 
  if d <> d' then raise IllTypedPattern;
  let g0'' = applyEqns g0' (sp,vs) in
  g0'', Some (x, V.ConApp (c, xs), a)

and chkPat' sigma (g0, p, x, a) = match p with
  | App (c,ps) -> chkConstrPat sigma (g0, (c, ps), x, a)
    (* TODO: This also needs to be able to raise "stuck" which will just keep the original problem *)
  | Id z ->
    try chkConstrPat sigma (g0, (z, []), x, a) (* If it's a constructor.. *)
    with V.Free -> Snoc (g0, Oft (z,a)) , Some (x,V.Neu (z, V.Emp), a) (* It's a variable *)

and processJudgment sigma (g0,j) = match j with
  | ChkPat (p,x,a) -> chkPat' sigma (g0, p, x, a)
  | Oft (x,a) -> Snoc (g0, j), None
  | OftBind (x,v,a) -> Snoc (g0, j), None
  | ChkPatBind (p,x,v,a) -> 
    let g0' , Some (x, u, a) = chkPat' sigma (g0, p, x, a) in
    let g0'' = applyEqn g0' (u,v) in
    g0'', Some (x, u, a)

and applyInstJ sigma inst = function
  | ChkPat (p,x,a) -> ChkPat (p,x,applyInstT sigma inst a)
  | Oft (x, a) -> Oft (x, applyInstT sigma inst a)
  | OftBind (x,v,a) -> OftBind (x, applyInstT sigma inst v, applyInstT sigma inst a)
  | ChkPatBind (p, x, v, a) -> ChkPatBind (p,x,applyInstT sigma inst v, applyInstT sigma inst a)
and applyInstT sigma inst a = match inst with
  | None -> a
  | Some (x,v,b) -> normalize sigma (Snoc (Nil, OftBind (x,v,b))) a (* Hmm *)

and traverseChkPats sigma = function
  | (g0,[]), p::ps, V.Fun (a,f) ->
    let x = V.gensym () in
    traverseChkPats sigma ((g0,[ChkPat (p,x,a)]), ps, V.vapp sigma (f, V.Neu (x, V.Emp)))
    (* TODO: V.app will need g0 also, which might supply bindings for some variables*)
  | (g0,[]), ps, a -> (g0,[]), ps, a (* Stuck until we learn about 'a', or ps is done *)
  | (g0,j::js), ps, vtp -> 
    let (g0', inst) = processJudgment sigma (g0,j) in
    (* TODO: Somehow catch stuck, and if the rest is also stuck, well, then we're stuck? *)
    (* How do we 'monotonically combine exceptions'? Do we actually want an exception for success?
       Look for somewhere to make progress, raise if we find one, raise Stuck if we don't? *)
    traverseChkPats sigma ((g0',List.map (applyInstJ sigma inst) js), ps, applyInstT sigma inst vtp)
      (* This removes "internal" variables eagerly, leaving only the ones the user wrote *)
      (* This is kind of annoying; maybe we should just keep them and treat them uniformly with
         the equations we get from unification. *)

and complete = function
  | Nil -> true
  | Snoc (g, Oft (_x, _a))
  | Snoc (g, OftBind (_x, _, _a)) -> complete g
  | Snoc (g, _) -> false

and rev g acc = match g with
  | Nil -> acc
  | Snoc (g, j) -> rev g (j::acc)

and normalize sigma g = function
  | V.Fun (a, f) -> V.Fun (normalize sigma g a, normalize sigma g f)
  | V.Clo (t, rho) -> V.Clo (t, normalizeEnv sigma g rho)
  | V.Type -> V.Type
  | V.ConApp (c, sp) -> V.ConApp (c, normalizeSp sigma g sp)
  | V.DefApp (f, sp) -> V.defapp sigma f (normalizeSp sigma g sp)
  | V.Neu (x, sp) -> V.vappSp sigma (lookupVal x g) (normalizeSp sigma g sp)

(* Bug: If we pull a definition out/through the context past another variable which shadows
   variables in the definition, then we have a problem. Would de Bruijn indices would work better
   internally?  *)
and lookupVal x = function
  | Snoc (g, Oft (y, _)) when y = x -> V.Neu (x, V.Emp)
  | Snoc (g, OftBind (y, v, _)) when y = x -> v
  | Snoc (g, _) -> lookupVal x g
  | Nil -> V.Neu (x, V.Emp)

and normalizeEnv sigma g = function 
  | V.Empty -> V.Empty
  | V.Dot (rho, (v,x)) -> V.Dot (normalizeEnv sigma g rho, (normalize sigma g v, x))

and normalizeSp sigma g = function
  | V.Emp -> V.Emp
  | V.Snoc (sp, v) -> V.Snoc (normalizeSp sigma g sp, normalize sigma g v)

and normalizeJ sigma g = function
  | ChkPat (p, x, a) -> ChkPat (p, x, normalize sigma g a)
  | Oft (x, a) -> Oft (x, normalize sigma g a)
  | OftBind (x, v, a) -> OftBind (x, normalize sigma g v, normalize sigma g a)
  | ChkPatBind (p, x, v, a) -> ChkPatBind (p, x, normalize sigma g v, normalize sigma g a)

and normalizeCtx sigma = function
  | Nil -> Nil
  | Snoc (g, j) -> 
    let g' = normalizeCtx sigma g in
    let j' = normalizeJ sigma g' j in
    Snoc (g', j')

and normalizeState sigma ((g,[]), ps, a) =
  let g = normalizeCtx sigma g in
  let a = normalize sigma g a in
  ((g,[]), ps, a)

and chkPats sigma state =
 let state = traverseChkPats sigma state in
 let state = normalizeState sigma state in
 match state with
   | (g,[]), [] , a when complete g -> g, a
   | (g,[]), ps , a -> chkPats sigma ((Nil, rev g []), ps , a)
   (* TODO: Need to detect stuck states and raise an error *)

let chkBranch sigma (recname,rectyp) (Br (ps,e)) vtp =
  let (gamma,vtp') = chkPats sigma ((Nil,[]), ps, vtp) in
  chk sigma (Snoc (gamma, Oft (recname ,rectyp))) (e, vtp')

let rec chkDecl sigma = function
  | (Def (name,tp,body)) ->
     chk sigma Nil (tp, V.Type);
     let vtp = eval sigma Nil tp in
     List.iter (fun br -> chkBranch sigma (name,vtp) br vtp) body;
     [(name,(V.Def (vtp,body)))]
  | (Data (name, tp, constructors)) ->
    chk sigma Nil (tp, V.Type);
    let d = (name,V.Constr (eval sigma Nil tp)) in
     d::(List.map (fun (Con (cname, ctp)) ->
       chk (d::sigma) Nil (ctp, V.Type);
       (cname,(V.Constr (eval (d::sigma) Nil ctp)))) constructors)

let rec chkDeclList sigma defs = match defs with
  | [] -> ()
  | (d::ds) ->
    let vd = chkDecl sigma d in
    chkDeclList (vd@sigma) ds

let chkMod (Prog defs) = chkDeclList [] defs



