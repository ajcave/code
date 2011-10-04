module cc where

postulate
 O : Set

data tp : Set where
 ▹ : (a : O) -> tp
 _×_ : (t u : tp) -> tp

postulate
 var : tp -> tp -> Set

data exp : tp -> tp -> Set where
 ▹ : ∀ {t s} -> var t s -> exp t s
 _∘_ : ∀ {t u s} -> exp u s -> exp t u -> exp t s
 [_,_] : ∀ {t u s} -> exp t u -> exp t s -> exp t (u × s)
 π₁ : ∀ {t s} -> exp (t × s) t
 π₂ : ∀ {t s} -> exp (t × s) s
 id : ∀ {t} -> exp t t

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

mutual
 data neut : tp -> tp -> Set where
  id : ∀ {t} -> neut t t
  π1∘ : ∀ {t u s} -> neut t (u × s) -> neut t u
  π2∘ : ∀ {t u s} -> neut t (u × s) -> neut t s
  _∘_ : ∀ {t u s} -> var u s -> norm t u -> neut t s 
 data norm : tp -> tp -> Set where
  ▹ : ∀ {t a} -> neut t (▹ a) -> norm t (▹ a)
  [_,_] : ∀ {t u s} -> norm t u -> norm t s -> norm t (u × s)

η-expand : ∀ {u t} -> neut t u -> norm t u
η-expand {▹ a} R = ▹ R
η-expand {t × u} R = [ (η-expand (π1∘ R)) , (η-expand (π2∘ R)) ]

proj1 : ∀ {t u s} -> norm t (u × s) -> norm t u
proj1 [ M , N ] = M

proj2 : ∀ {t u s} -> norm t (u × s) -> norm t s
proj2 [ M , N ] = N

mutual
 cutr : ∀ {t u s} -> neut u s -> norm t u -> norm t s
 cutr id n = n
 cutr (π1∘ r) n = proj1 (cutr r n)
 cutr (π2∘ r) n = proj2 (cutr r n)
 cutr (M ∘ m) n = η-expand (M ∘ (cut m n))

 cut : ∀ {t u s} -> norm u s -> norm t u -> norm t s
 cut (▹ r) n = cutr r n
 cut [ m1 , m2 ] n = [ (cut m1 n) , (cut m2 n) ]