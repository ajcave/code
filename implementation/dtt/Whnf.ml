open IntSyntax

exception TypingViolation

let rec whnf sigma e = match e with
  | App (e1, e2) ->
    let e1 = whnf sigma e1 in
    begin match e1 with
      | Lam (x,e) -> whnf sigma (subst1 e2 e)
      | Var _ | App _ | NatRec _ -> App (e1,e2)
      | Pi _ | Sigma _ | Nat | Set | Unit | Tt | Zero | Suc _ | Plus _ -> raise TypingViolation
      | Subst _ -> raise (Error.Violation "Subst should not occur in whnf")
    end 
  | Pi _ | Sigma _ | Nat | Set | Unit | Tt | Lam _ | Var _ | Zero | Suc _ -> e
  | Subst (s,e) -> whnf sigma (whsubst s e)
  | NatRec (en,aC,ez,(p,ih,es)) ->
    let en = whnf sigma en in
    begin match en with
      | Zero -> ez
      | Suc en' ->
	whnf sigma (subst (Dot (Dot (idsub, en'), NatRec (en', aC, ez, (p,ih,es)))) es)
      | Var _ | App _ | NatRec _ | Plus _ -> NatRec (en, aC, ez, (p,ih,es))
      | Pi _ | Sigma _ | Nat | Set | Unit | Tt | Lam _ -> raise TypingViolation
      | Subst _ -> raise (Error.Violation "Subst should not occur in whnf")
    end
  | Plus (e1,e2) ->
    let rec whnf_plus e1 = match e1 with
      | Zero -> whnf sigma e2
      | Suc e1' -> Suc (whnf_plus e1')
      | Var _ | App _ | NatRec _ | Plus _ -> Plus (e1, e2)
      | Pi _ | Sigma _ | Nat | Set | Unit | Tt | Lam _ -> raise TypingViolation
      | Subst _ -> raise (Error.Violation "Subst should not occur in whnf")
    in whnf_plus (whnf sigma e1)
