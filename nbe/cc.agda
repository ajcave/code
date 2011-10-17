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
  ! : ∀ {t} -> exp t ⊤

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
  ! : ∀ {t} {m1 m2 : exp t ⊤} -> m1 ≈ m2

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
   ! : ∀ {t} -> norm t ⊤

 η-expand : ∀ {u t} -> neut t u -> norm t u
 η-expand {▹ a} R = ▹ R
 η-expand {t × u} R = [ (η-expand (π₁∘ R)) , (η-expand (π₂∘ R)) ]
 η-expand {⊤} R = !

 mutual
  embr : ∀ {t u} -> neut t u -> exp t u
  embr id = id
  embr (π₁∘ r) = π₁ ∘ embr r
  embr (π₂∘ r) = π₂ ∘ embr r
  embr (M ∘ n) = (▹ M) ∘ (emb n)

  emb : ∀ {t u} -> norm t u -> exp t u
  emb (▹ r) = embr r
  emb [ m , n ] = [ (emb m) , (emb n) ]
  emb ! = !

 emb-η : ∀ {s t} (r : neut t s) -> embr r ≈ emb (η-expand r)
 emb-η {▹ a} r = refl
 emb-η {t × u} r = trans [ (emb-η (π₁∘ r)) , (emb-η (π₂∘ r)) ] π-η
 emb-η {⊤} r = !

 _⊙_ : ∀ {u t s} -> exp t u -> norm s t -> norm s u
 (▹ θ) ⊙ n = η-expand (θ ∘ n)
 (m1 ∘ m2) ⊙ n = m1 ⊙ (m2 ⊙ n)
 [ n1 , n2 ] ⊙ n = [ (n1 ⊙ n) , (n2 ⊙ n) ]
 π₁ ⊙ [ n , m ] = n
 π₂ ⊙ [ n , m ] = m
 id ⊙ n = n
 ! ⊙ n = !

 eval : ∀ {t u} -> exp t u -> norm t u
 eval m = m ⊙ (η-expand id) 

 emb-eval : ∀ {t u s} (m : exp u s) (n : norm t u) -> (m ∘ (emb n)) ≈ emb (m ⊙ n)
 emb-eval (m1 ∘ m2) n = trans (emb-eval m1 (m2 ⊙ n)) (trans (refl ∘ (emb-eval m2 n)) (sym assoc))
 emb-eval id n = idL
 emb-eval (▹ M) n = emb-η (M ∘ n)
 emb-eval [ m1 , m2 ] n = trans [ trans (emb-eval m1 n) (trans (π₁-β ∘ refl) assoc)
                                , trans (emb-eval m2 n) (trans (π₂-β ∘ refl) assoc) ] π-η
 emb-eval π₁ [ n1 , n2 ] = π₁-β
 emb-eval π₂ [ n1 , n2 ] = π₂-β
 emb-eval ! n = !
-- Is there a way to define emb-eval simultaneously with ⊙ and emb-η with η-expand kind of like how intrinsically typed means we're defining substitution simultaneously with the proof of the substitution lemma?
 
 ≡-emb : ∀ {t u} {n1 n2 : norm t u} -> n1 ≡ n2 -> emb n1 ≈ emb n2
 ≡-emb refl = refl

 completeness' : ∀ {t u s} (m1 m2 : exp u s) (n1 n2 : norm t u) -> (m1 ⊙ n1) ≡ (m2 ⊙ n2) -> (m1 ∘ (emb n1)) ≈ (m2 ∘ (emb n2))
 completeness' m1 m2 n1 n2 H = trans (sym (emb-eval m2 n2)) (trans (≡-emb H) (emb-eval m1 n1))

 completeness : ∀ {t u} (m1 m2 : exp t u) -> (eval m1) ≡ (eval m2) -> m1 ≈ m2
 completeness {t} {u} m1 m2 H = trans idR (trans (refl ∘ (sym (emb-η id))) (trans (trans (completeness' m1 m2 _ _ H) (refl ∘ (emb-η id))) (sym idR)))
