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

 emb-η : ∀ {s t} (r : neut t s) -> emb (η-expand r) ≈ embr r
 emb-η {▹ a} r = refl
 emb-η {t × u} r = trans (sym π-η) [ (emb-η (π₁∘ r)) , (emb-η (π₂∘ r)) ]
 emb-η {⊤} r = ⊤

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
 emb-eval (▹ y) n = emb-η (y ∘ n)
 emb-eval (y ∘ y') n = trans (trans assoc (refl ∘ (emb-eval y' n))) (emb-eval y (y' ⊙ n))
 emb-eval [ y , y' ] n = trans (trans (sym π-η) [ (trans (sym assoc) ((sym π₁-β) ∘ refl))
                                                , (trans (sym assoc) ((sym π₂-β) ∘ refl)) ])
                                                [ (emb-eval y n) , (emb-eval y' n) ]
 emb-eval π₁ [ y , y' ] = sym π₁-β
 emb-eval π₂ [ y , y' ] = sym π₂-β
 emb-eval id n = sym idL
 emb-eval tt n = ⊤

 completeness' : ∀ {t u s} (m1 m2 : exp u s) (n1 n2 : norm t u) -> (m1 ⊙ n1) ≡ (m2 ⊙ n2) -> (m1 ∘ (emb n1)) ≈ (m2 ∘ (emb n2))
 completeness' m1 m2 n1 n2 H = trans (emb-eval m2 n2) (trans (≡-subst (λ x -> emb (m1 ⊙ n1) ≈ emb x) H refl) (sym (emb-eval m1 n1)))

 completeness : ∀ {t u} (m1 m2 : exp t u) -> (eval1 m1) ≡ (eval1 m2) -> m1 ≈ m2
 completeness {t} {u} m1 m2 H = trans idR (trans (refl ∘ emb-η id) (trans (trans (completeness' m1 m2 _ _ H) (refl ∘ (sym (emb-η id)))) (sym idR)))
