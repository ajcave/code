type var = int

let nextvar = 
  let cell = ref 0 in
  fun _ -> (cell := !cell + 1; !cell)

type tm = 
  | Inl of tm
  | Inr of tm
  | Case of tm * (var * tm) * (var * tm)
  | Lam of var * tm
  | App of tm * tm
  | Var of var 
  | Unit

type norm =
  | NInl of norm
  | NInr of norm
  | NCase of neut * (var * norm) * (var * norm)
  | NLam of norm
  | NUnit
  | Embed of neut
and neut =
  | NVar of var 
  | NApp of neut * norm

type tp = 
  | TUnit
  | Arr of tp * tp
  | Sum of tp * tp

type sem =
  | SUnit
  | SLam of (sem -> sem)
  | SSum of semsum
and semsum =
  | SInl of sem
  | SInr of sem
  | SCase of neut * (var * semsum) * (var * semsum)

let rec reify t s = match (t,s) with 
  | (TUnit, SUnit) -> NUnit
  | (Arr (t1,t2), SLam f) -> NLam (reify t2 (f (reflect t1 (NVar (nextvar ())))))
  | (Sum (t1,t2), SSum s) -> reifysum t1 t2 s 
and reifysum t1 t2 s = match s with
  | SInl s -> reify t1 s
  | SInr s -> reify t2 s
  | SCase (r,(x,s1),(y,s2)) -> NCase (r, (x, reifysum t1 t2 s1), (y,reifysum t1 t2 s2))
and reflect t r = match (t,r) with
  | (TUnit,r) -> SUnit
  | (Arr (t1,t2), r) -> SLam (fun x -> reflect t2 (NApp (r, reify t1 x)))
  | (Sum (t1,t2), r) ->
    let x = nextvar () in
    let y = nextvar () in
    SSum (SCase (r, (x, SInl (reflect t1 (NVar x))), (y,SInr (reflect t2 (NVar y)))))
   (* The var selection here is wrong.. the SCase needs to come with names? *)

let rcase s b1 b2 = SUnit (* TODO: We need the type here in order to push it in ...*)
 (* Should we annotate the tm case with the return type like we have to in dependent type theory? *)
(* Couldn't we also just sheafify all the semantic type constructions instead of "reducing" them?
   i.e. allow SCase over top of any sem object? *)

let rec scase s b1 b2 = match s with
 | SInl s1 -> b1 s1
 | SInr s2 -> b2 s2
 | SCase (r,(x,s1),(y,s2)) -> rcase r (scase s1 b1 b2) (scase s2 b1 b2)

let extend env (x,s) y = if x = y then s else env y

let rec eval env = function
  | Inl t -> SSum (SInl (eval env t))
  | Inr t -> SSum (SInr (eval env t))
  | Case (t1,(x,b1),(y,b2)) ->
	let SSum s0 = eval env t1 in
	scase s0 
              (fun s -> eval (extend env (x,s)) b1)
	      (fun s -> eval (extend env (y,s)) b2)				
  | Var x -> env x
  | App (t1,t2) -> let SLam f = eval env t1 in f (eval env t2)
  | Lam (x,t) -> SLam (fun s -> eval (extend env (x,s)) t)
  | Unit -> SUnit
