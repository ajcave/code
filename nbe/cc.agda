module cc where

data _≡_ {A : Set} (x : A) : (y : A) -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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

mutual
 cutr : ∀ {t u s} -> neut u s -> norm t u -> norm t s
 cutr id n = n
 cutr (π₁∘ r) n = proj1 (cutr r n)
 cutr (π₂∘ r) n = proj2 (cutr r n)
 cutr (M ∘ m) n = η-expand (M ∘ (m ⊙ n))

 _⊙_ : ∀ {t u s} -> norm u s -> norm t u -> norm t s
 _⊙_ (▹ r) n = cutr r n
 _⊙_ [ m1 , m2 ] n = [ (m1 ⊙ n) , (m2 ⊙ n) ]
 _⊙_ tt n = tt

eval : ∀ {t u} -> exp t u -> norm t u
eval (▹ M) = η-expand (M ∘ (η-expand id))
eval (m ∘ n) = (eval m) ⊙ (eval n)
eval [ m , n ] = [ (eval m) , (eval n) ]
eval π₁ = η-expand (π₁∘ id)
eval π₂ = η-expand (π₂∘ id)
eval id = η-expand id
eval tt = tt

mutual
 eval2r : ∀ {u t s} -> exp t (▹ u) -> norm s t -> neut s (▹ u)
 eval2r (▹ y) m = y ∘ {!!}
 eval2r (y ∘ y') m = eval2r y {!!}
 eval2r π₁ m = π₁∘ {!eval2r!}
 eval2r π₂ m = {!!}
 eval2r id m = {!!}
 eval2 : ∀ {u t} -> exp t u -> norm t u
 eval2 {▹ a} m = ▹ (eval2r m {!!})
 eval2 {t × u} m = [ (eval2 (π₁ ∘ m)) , (eval2 (π₂ ∘ m)) ]
 eval2 {⊤} m = tt

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

η-cut : ∀ {s t u} (r : neut u s) (m : norm t u) -> ((η-expand r) ⊙ m) ≡ (cutr r m)
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

emb-eval : ∀ {t u} (n : exp t u) -> emb (eval n) ≈ n
emb-eval (▹ M) = {!!}
emb-eval (m ∘ n) = {!!}
emb-eval [ m , n ] = []-extensionality (trans (trans (sym π₁-β) (emb-eval m)) π₁-β) (trans (trans (sym π₂-β) (emb-eval n)) π₂-β)
emb-eval π₁ = {!!}
emb-eval π₂ = {!!}
emb-eval id = {!!}
emb-eval tt = refl

pf : ∀ {t u} (m n : exp t u) -> (eval m) ≡ (eval n) -> m ≈ n
pf (▹ y) (▹ y') E = {!!}
pf (▹ y) (y' ∘ y0) E = {!!}
pf (▹ y) [ y' , y0 ] E = {!!}
pf (▹ y) π₁ E = {!!}
pf (▹ y) π₂ E = {!!}
pf (▹ y) id E = {!!}
pf (▹ y) tt E = {!!}
pf (y ∘ y') n E = {!!}
pf [ y , y' ] n E = {!!}
pf π₁ n E = {!!}
pf π₂ n E = {!!}
pf id n E = {!!}
pf tt n E = {!!}

subst : ∀ {A : Set} (P : A -> Set) {a1 a2 : A} -> a1 ≡ a2 -> P a1 -> P a2
subst P refl x = x

pf1 : ∀ {u t} {m n : exp t u} -> (eval m) ≡ (eval n) -> m ≈ n
pf1 {▹ a} E = {!!}
pf1 {t' × u} {t} {m} {n} E = []-extensionality (pf1 (subst (λ x → ((eval π₁) ⊙ eval m) ≡ (eval π₁ ⊙ x)) E refl))
                                               (pf1 (subst (λ x → ((eval π₂) ⊙ eval m) ≡ (eval π₂ ⊙ x)) E refl))
pf1 {⊤} E = ⊤