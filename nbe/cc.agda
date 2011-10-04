module cc where

data _≡_ {A : Set} (x : A) : (y : A) -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

subst : ∀ {A : Set} (P : A -> Set) {a b : A} -> a ≡ b -> P a -> P b
subst P refl x = x

postulate
 O : Set

data tp : Set where
 ▹ : (a : O) -> tp
 _×_ : (t u : tp) -> tp
 ⊤ : tp

postulate
 var : tp -> tp -> Set

data exp : tp -> tp -> Set where
 ▹ : ∀ {t s} -> var t s -> exp t s
 _∘_ : ∀ {t u s} -> exp u s -> exp t u -> exp t s
 [_,_] : ∀ {t u s} -> exp t u -> exp t s -> exp t (u × s)
 π₁ : ∀ {t s} -> exp (t × s) t
 π₂ : ∀ {t s} -> exp (t × s) s
 id : ∀ {t} -> exp t t
 tt : ∀ {t} -> exp t ⊤

data _≈_ : ∀ {t u} -> exp t u -> exp t u -> Set where
 refl : ∀ {t u} {m : exp t u} -> m ≈ m
 sym : ∀ {t u} {m n : exp t u} -> m ≈ n -> n ≈ m
 trans : ∀ {t u} {m n p : exp t u} -> n ≈ p -> m ≈ n -> m ≈ p 
 assoc : ∀ {t u s v} {m : exp u s} {n : exp t u} {p : exp v t} -> (m ∘ (n ∘ p)) ≈ ((m ∘ n) ∘ p)
 idL : ∀ {t u} {m : exp t u} -> (id ∘ m) ≈ m
 idR : ∀ {t u} {m : exp t u} -> (m ∘ id) ≈ m
 π₁-β : ∀ {t u s} {m : exp t u} {n : exp t s} -> (π₁ ∘ [ m , n ]) ≈ m
 π₂-β : ∀ {t u s} {m : exp t u} {n : exp t s} -> (π₂ ∘ [ m , n ]) ≈ n
 π-η : ∀ {t u s} {m : exp t (u × s)} -> m ≈ [ π₁ ∘ m , π₂ ∘ m ]
 _∘_ : ∀ {t u s} {m1 m2 : exp u s} {n1 n2 : exp t u} -> m1 ≈ m2 -> n1 ≈ n2 -> (m1 ∘ n1) ≈ (m2 ∘ n2)
 [_,_] : ∀ {t u s} {m1 m2 : exp t u} {n1 n2 : exp t s} -> m1 ≈ m2 -> n1 ≈ n2 -> [ m1 , n1 ] ≈ [ m2 , n2 ]
 ⊤ : ∀ {t} {m1 m2 : exp t ⊤} -> m1 ≈ m2

[]-extensionality : ∀ {t u s} {m n : exp t (u × s)} -> (π₁ ∘ m) ≈ (π₁ ∘ n) -> (π₂ ∘ m) ≈ (π₂ ∘ n) -> m ≈ n
[]-extensionality p q = trans (trans (sym π-η) [ p , q ]) π-η

mutual
 data neut : tp -> tp -> Set where
  id : ∀ {t} -> neut t t
  π₁∘ : ∀ {t u s} -> neut t (u × s) -> neut t u
  π₂∘ : ∀ {t u s} -> neut t (u × s) -> neut t s
  _∘_ : ∀ {t u s} -> var u s -> norm t u -> neut t s 
 data norm : tp -> tp -> Set where
  ▹ : ∀ {t a} -> neut t (▹ a) -> norm t (▹ a)
  [_,_] : ∀ {t u s} -> norm t u -> norm t s -> norm t (u × s)
  tt : ∀ {t} -> norm t ⊤

η-expand : ∀ {u t} -> neut t u -> norm t u
η-expand {▹ a} R = ▹ R
η-expand {t × u} R = [ (η-expand (π₁∘ R)) , (η-expand (π₂∘ R)) ]
η-expand {⊤} R = tt

proj1 : ∀ {t u s} -> norm t (u × s) -> norm t u
proj1 [ M , N ] = M

proj2 : ∀ {t u s} -> norm t (u × s) -> norm t s
proj2 [ M , N ] = N

eval2 : ∀ {u t s} -> exp t u -> norm s t -> norm s u
eval2 (▹ y) n = η-expand (y ∘ n)
eval2 (y ∘ y') n = eval2 y (eval2 y' n)
eval2 [ y , y' ] n = [ (eval2 y n) , (eval2 y' n) ]
eval2 π₁ n = proj1 n
eval2 π₂ n = proj2 n
eval2 id n = n
eval2 tt n = tt

eval1 : ∀ {t u} -> exp t u -> norm t u
eval1 m = eval2 m (η-expand id)

mutual
 embr : ∀ {t u} -> neut t u -> exp t u
 embr id = id
 embr (π₁∘ r) = π₁ ∘ (embr r)
 embr (π₂∘ r) = π₂ ∘ embr r
 embr (M ∘ n) = (▹ M) ∘ (emb n)

 emb : ∀ {t u} -> norm t u -> exp t u
 emb (▹ r) = embr r
 emb [ m , n ] = [ (emb m) , (emb n) ]
 emb tt = tt

{- η-cut : ∀ {s t u} (r : neut u s) (m : norm t u) -> ((η-expand r) ⊙ m) ≡ (cutr r m)
η-cut {▹ a} r m = refl
η-cut {t × u} r m rewrite η-cut (π₁∘ r) m | η-cut (π₂∘ r) m = {!!} -- just prove eta
η-cut {⊤} r m = {!!} -- just prove extensionality

mutual
 eval-embr : ∀ {t u} (r : neut t u) -> eval (embr r) ≡ (η-expand r)
 eval-embr id = refl
 eval-embr (π₁∘ y) rewrite eval-embr y | η-cut (π₁∘ id) (η-expand y) = refl
 eval-embr (π₂∘ y) rewrite eval-embr y | η-cut (π₂∘ id) (η-expand y) = refl
 eval-embr (M ∘ m) rewrite eval-emb m | η-cut (M ∘ η-expand id) m | η-cut id m = refl

 eval-emb : ∀ {t u} (n : norm t u) -> eval (emb n) ≡ n
 eval-emb (▹ r) = eval-embr r
 eval-emb [ m , n ] rewrite eval-emb m | eval-emb n = refl
 eval-emb tt = refl

soundness : ∀ {t u} {m n : exp t u} -> m ≈ n -> (eval m) ≡ (eval n)
soundness E = {!!} -- "Easy" -}

mutual
 cut2 : ∀ {s t u} (n : norm u s) (r : neut t u) -> norm t s
 cut2 (▹ y) r = ▹ (cutr2 y r)
 cut2 [ y , y' ] r = [ cut2 y r , cut2 y' r ]
 cut2 tt r = tt
 cutr2 : ∀ {s t u} (r1 : neut u s) (r2 : neut t u) -> neut t s
 cutr2 id r2 = r2
 cutr2 (π₁∘ y) r2 = π₁∘ (cutr2 y r2)
 cutr2 (π₂∘ y) r2 = π₂∘ (cutr2 y r2)
 cutr2 (y ∘ y') r2 = y ∘ (cut2 y' r2)

mutual
 embr-cut2 : ∀ {s t u} (m : norm u s) (r : neut t u) -> emb (cut2 m r) ≈ (emb m ∘ embr r)
 embr-cut2 (▹ y) r = embr-cutr2 y r
 embr-cut2 [ y , y' ] r = trans (sym π-η) [ (trans (sym assoc) (trans ((sym π₁-β) ∘ refl) (embr-cut2 y r)))
                                          , (trans (sym assoc) (trans ((sym π₂-β) ∘ refl) (embr-cut2 y' r))) ]
 embr-cut2 tt r = ⊤
 embr-cutr2 : ∀ {s t u} (y : neut u s) (n : neut t u) -> embr (cutr2 y n) ≈ (embr y ∘ embr n)
 embr-cutr2 id n = sym idL
 embr-cutr2 (π₁∘ y) n = trans assoc (refl ∘ (embr-cutr2 y n))
 embr-cutr2 (π₂∘ y) n = trans assoc (refl ∘ (embr-cutr2 y n))
 embr-cutr2 (y ∘ y') n = trans assoc (refl ∘ embr-cut2 y' n)

emb-η : ∀ {s t u} (y : neut u s) (n : neut t u) -> emb (η-expand (cutr2 y n)) ≈ (embr y ∘ embr n)
emb-η {▹ a} y n = embr-cutr2 y n
emb-η {t × u} y n = trans (trans (sym π-η) [ (sym assoc) , (sym assoc) ]) [ emb-η (π₁∘ y) n , emb-η (π₂∘ y) n ]
emb-η {⊤} y n = ⊤

emb-id : ∀ {t} -> emb (η-expand (id {t})) ≈ id
emb-id = trans idL (emb-η id id)

emb-eval : ∀ {t u s} (m : exp u s) (n : norm t u) -> emb (eval2 m n) ≈ (m ∘ (emb n))
emb-eval (▹ y) n = trans idL (emb-η id (y ∘ n))
emb-eval (y ∘ y') n = trans (trans assoc (refl ∘ (emb-eval y' n))) (emb-eval y (eval2 y' n))
emb-eval [ y , y' ] n = trans (trans (sym π-η) [ (trans (sym assoc) ((sym π₁-β) ∘ refl)) , (trans (sym assoc) ((sym π₂-β) ∘ refl)) ]) [ (emb-eval y n) , (emb-eval y' n) ]
emb-eval π₁ [ y , y' ] = sym π₁-β
emb-eval π₂ [ y , y' ] = sym π₂-β
emb-eval id n = sym idL
emb-eval tt n = ⊤

completeness' : ∀ {t u s} (m1 m2 : exp u s) (n1 n2 : norm t u) -> (eval2 m1 n1) ≡ (eval2 m2 n2) -> (m1 ∘ (emb n1)) ≈ (m2 ∘ (emb n2))
completeness' m1 m2 n1 n2 H = trans (emb-eval m2 n2) (trans (subst (λ x -> emb (eval2 m1 n1) ≈ emb x) H refl) (sym (emb-eval m1 n1)))

completeness : ∀ {t u} (m1 m2 : exp t u) -> (eval1 m1) ≡ (eval1 m2) -> m1 ≈ m2
completeness {t} {u} m1 m2 H = trans idR (trans (refl ∘ emb-id) (trans (trans (completeness' m1 m2 _ _ H) (refl ∘ (sym emb-id))) (sym idR)))