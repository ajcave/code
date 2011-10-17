module cc (O : Set) where

open import eq

data tp : Set where
 ▹ : (a : O) -> tp
 _×_ : (t u : tp) -> tp
 ⊤ : tp

module foo (var : tp -> tp -> Set) where

 data exp : tp -> tp -> Set where
  _∘_ : ∀ {t u s} -> exp u s -> exp t u -> exp t s
  id : ∀ {t} -> exp t t
  ▹ : ∀ {t s} -> var t s -> exp t s
  [_,_] : ∀ {t u s} -> exp t u -> exp t s -> exp t (u × s)
  π₁ : ∀ {t s} -> exp (t × s) t
  π₂ : ∀ {t s} -> exp (t × s) s
  tt : ∀ {t} -> exp t ⊤

 data _≈_ : ∀ {t u} -> exp t u -> exp t u -> Set where
  refl : ∀ {t u} {m : exp t u} -> m ≈ m
  sym : ∀ {t u} {m n : exp t u} -> m ≈ n -> n ≈ m
  trans : ∀ {t u} {m n p : exp t u} -> n ≈ p -> m ≈ n -> m ≈ p 
  assoc : ∀ {t u s v} {m : exp u s} {n : exp t u} {p : exp v t} -> (m ∘ (n ∘ p)) ≈ ((m ∘ n) ∘ p)
  idL : ∀ {t u} {m : exp t u} -> (id ∘ m) ≈ m
  idR : ∀ {t u} {m : exp t u} -> (m ∘ id) ≈ m
  _∘_ : ∀ {t u s} {m1 m2 : exp u s} {n1 n2 : exp t u} -> m1 ≈ m2 -> n1 ≈ n2 -> (m1 ∘ n1) ≈ (m2 ∘ n2)
  π₁-β : ∀ {t u s} {m : exp t u} {n : exp t s} -> (π₁ ∘ [ m , n ]) ≈ m
  π₂-β : ∀ {t u s} {m : exp t u} {n : exp t s} -> (π₂ ∘ [ m , n ]) ≈ n
  π-η : ∀ {t u s} {m : exp t (u × s)} -> m ≈ [ π₁ ∘ m , π₂ ∘ m ]
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

 mutual
  embr : ∀ {t u} -> neut t u -> exp t u
  embr id = id
  embr (π₁∘ r) = π₁ ∘ embr r
  embr (π₂∘ r) = π₂ ∘ embr r
  embr (M ∘ n) = (▹ M) ∘ (emb n)

  emb : ∀ {t u} -> norm t u -> exp t u
  emb (▹ r) = embr r
  emb [ m , n ] = [ (emb m) , (emb n) ]
  emb tt = tt

 mutual
  _◆_ : ∀ {s t u} (n : norm u s) (r : neut t u) -> norm t s
  ▹ r1 ◆ r2 = ▹ (r1 ◇ r2)
  [ n1 , n2 ] ◆ r = [ n1 ◆ r , n2 ◆ r ]
  tt ◆ r = tt

  _◇_ : ∀ {s t u} (r1 : neut u s) (r2 : neut t u) -> neut t s
  id ◇ r2 = r2
  π₁∘ r1 ◇ r2 = π₁∘ (r1 ◇ r2)
  π₂∘ r1 ◇ r2 = π₂∘ (r1 ◇ r2)
  (M ∘ n) ◇ r2 = M ∘ (n ◆ r2)

 mutual
  embr-funct : ∀ {s t u} (m : norm u s) (r : neut t u) -> emb (m ◆ r) ≈ (emb m ∘ embr r)
  embr-funct (▹ y) r = embr-functr y r
  embr-funct [ n1 , n2 ] r = trans (sym π-η) [ (trans (sym assoc) (trans ((sym π₁-β) ∘ refl) (embr-funct n1 r)))
                                             , (trans (sym assoc) (trans ((sym π₂-β) ∘ refl) (embr-funct n2 r))) ]
  embr-funct tt r = ⊤

  embr-functr : ∀ {s t u} (r1 : neut u s) (r2 : neut t u) -> embr (r1 ◇ r2) ≈ (embr r1 ∘ embr r2)
  embr-functr id n = sym idL
  embr-functr (π₁∘ y) n = trans assoc (refl ∘ (embr-functr y n))
  embr-functr (π₂∘ y) n = trans assoc (refl ∘ (embr-functr y n))
  embr-functr (y ∘ y') n = trans assoc (refl ∘ embr-funct y' n)



 emb-η : ∀ {s t u} (r1 : neut u s) (r2 : neut t u) -> emb (η-expand (r1 ◇ r2)) ≈ (embr r1 ∘ embr r2)
 emb-η {▹ a} y n = embr-functr y n
 emb-η {t × u} y n = trans (trans (sym π-η) [ (sym assoc) , (sym assoc) ]) [ emb-η (π₁∘ y) n , emb-η (π₂∘ y) n ]
 emb-η {⊤} y n = ⊤

 emb-id : ∀ {t} -> emb (η-expand (id {t})) ≈ id
 emb-id = trans idL (emb-η id id)

 _⊙_ : ∀ {u t s} -> exp t u -> norm s t -> norm s u
 (▹ θ) ⊙ n = η-expand (θ ∘ n)
 (m1 ∘ m2) ⊙ n = m1 ⊙ (m2 ⊙ n)
 [ n1 , n2 ] ⊙ n = [ (n1 ⊙ n) , (n2 ⊙ n) ]
 π₁ ⊙ [ n , m ] = n
 π₂ ⊙ [ n , m ] = m
 id ⊙ n = n
 tt ⊙ n = tt

 eval1 : ∀ {t u} -> exp t u -> norm t u
 eval1 m = m ⊙ (η-expand id) 

 emb-eval : ∀ {t u s} (m : exp u s) (n : norm t u) -> emb (m ⊙ n) ≈ (m ∘ (emb n))
 emb-eval (▹ y) n = trans idL (emb-η id (y ∘ n))
 emb-eval (y ∘ y') n = trans (trans assoc (refl ∘ (emb-eval y' n))) (emb-eval y (y' ⊙ n))
 emb-eval [ y , y' ] n = trans (trans (sym π-η) [ (trans (sym assoc) ((sym π₁-β) ∘ refl)) , (trans (sym assoc) ((sym π₂-β) ∘ refl)) ]) [ (emb-eval y n) , (emb-eval y' n) ]
 emb-eval π₁ [ y , y' ] = sym π₁-β
 emb-eval π₂ [ y , y' ] = sym π₂-β
 emb-eval id n = sym idL
 emb-eval tt n = ⊤

 completeness' : ∀ {t u s} (m1 m2 : exp u s) (n1 n2 : norm t u) -> (m1 ⊙ n1) ≡ (m2 ⊙ n2) -> (m1 ∘ (emb n1)) ≈ (m2 ∘ (emb n2))
 completeness' m1 m2 n1 n2 H = trans (emb-eval m2 n2) (trans (≡-subst (λ x -> emb (m1 ⊙ n1) ≈ emb x) H refl) (sym (emb-eval m1 n1)))

 completeness : ∀ {t u} (m1 m2 : exp t u) -> (eval1 m1) ≡ (eval1 m2) -> m1 ≈ m2
 completeness {t} {u} m1 m2 H = trans idR (trans (refl ∘ emb-id) (trans (trans (completeness' m1 m2 _ _ H) (refl ∘ (sym emb-id))) (sym idR)))
