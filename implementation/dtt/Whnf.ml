open IntSyntax

exception TypingViolation

let rec whnf sigma e = match e with
  | App (e1, e2) ->
    let e1 = whnf sigma e1 in
    begin match e1 with
      | Lam (x,e) -> whnf sigma (subst1 e2 e)
      | Var _ | App _ | Const _ -> App (e1,e2)
      | Pi _ | Sigma _ | Type -> raise TypingViolation
      | Subst _ -> raise (Error.Violation "Subst should not occur in whnf")
    end 
  | Pi _ | Sigma _ | Type | Lam _ | Var _ | Const _ -> e
  | Subst (s,e) -> whnf sigma (whsubst s e)
