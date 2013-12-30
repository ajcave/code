module subsequentialspaces where
open import Data.Product
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

record Subseq : Set where
 constructor _,_
 field
  f : ℕ -> ℕ
  monotone : ∀ {m n} -> m < n -> f m < f n

ConvRel : Set -> Set₁
ConvRel U = (ℕ -> U) -> U -> Set

-- record PreSubSeqSpace : Set₁ where
--  constructor presub
--  field
--   U : Set
--   ↝ : ConvRel U

record SubSeqSpace (U : Set) (_↝_ : ConvRel U) : Set₁ where
 constructor subseq
 field
  idconv : ∀ x -> (λ _ -> x) ↝ x
  subseqProp : ∀ {xs x} -> xs ↝ x -> (i : Subseq) -> (xs ∘ (Subseq.f i)) ↝ x
  star : ∀ {xs x} -> (∀ (i : Subseq) -> ∃ (λ k -> (xs ∘ (Subseq.f i) ∘ (Subseq.f k)) ↝ x)) -> xs ↝ x

1̂ : SubSeqSpace Unit (λ _ _ -> ⊤)
1̂ = subseq (λ _ -> tt) (λ x₁ i → tt) (λ x₁ → tt)

data Cl {U : Set} (_↝_ : ConvRel U) : ConvRel U where
 idconv : ∀ x -> Cl _↝_ (λ _ -> x) x
 base : ∀ {xs x} -> xs ↝ x -> Cl _↝_ xs x
 subseq : ∀ {xs x} -> Cl _↝_ xs x -> (i : Subseq)  -> Cl _↝_ (xs ∘ (Subseq.f i)) x
 star : ∀ {xs x} -> (∀ (i : Subseq) -> ∃ (λ k -> Cl _↝_ (xs ∘ (Subseq.f i) ∘ (Subseq.f k)) x)) -> Cl _↝_ xs x

Cl-is-SubSeqSpace : ∀ {U} (_↝_ : ConvRel U) -> SubSeqSpace U (Cl _↝_)
Cl-is-SubSeqSpace _↝_ = subseq idconv subseq star

module _ (A B : Set) (_↝A_ : ConvRel A) (_↝B_ : ConvRel B) where
 data Sum↝ : ConvRel (A ⊎ B) where
  inl : ∀ {xs x} -> xs ↝A x -> Sum↝ (inj₁ ∘ xs) (inj₁ x)
  inr : ∀ {ys y} -> ys ↝B y -> Sum↝ (inj₂ ∘ ys) (inj₂ y)

 _⊎⁺_ : SubSeqSpace (A ⊎ B) (Cl Sum↝)
 _⊎⁺_ = Cl-is-SubSeqSpace Sum↝

×rel :  ∀ {A B} (_↝A_ : ConvRel A) (_↝B_ : ConvRel B) -> ConvRel (A × B)
×rel _↝A_ _↝B_ xs x = ((proj₁ ∘ xs) ↝A proj₁ x) × ((proj₂ ∘ xs) ↝B proj₂ x)

module _ {A B : Set} (_↝A_ : ConvRel A) (pa : SubSeqSpace A _↝A_) (_↝B_ : ConvRel B) (pb : SubSeqSpace B _↝B_) where
 private module A = SubSeqSpace pa
 private module B = SubSeqSpace pb
 ×idconv : ∀ x -> ×rel _↝A_ _↝B_ (λ _ -> x) x
 ×idconv x = A.idconv (proj₁ x) , B.idconv (proj₂ x)

 ×subseq : ∀ {xs x} -> ×rel _↝A_ _↝B_ xs x -> (i : Subseq) -> ×rel _↝A_ _↝B_ (xs ∘ (Subseq.f i)) x
 ×subseq (r1 , r2) i = A.subseqProp r1 i , B.subseqProp r2 i
 
 ×star : ∀ {xs x} -> (∀ (i : Subseq) -> ∃ (λ k -> ×rel _↝A_ _↝B_ (xs ∘ (Subseq.f i) ∘ (Subseq.f k)) x)) -> ×rel _↝A_ _↝B_ xs x
 ×star f = (A.star (λ i → proj₁ (f i) , proj₁ (proj₂ (f i)))) , B.star (λ i → (proj₁ (f i)) , (proj₂ (proj₂ (f i))))

 _×⁺_ : SubSeqSpace (A × B) (×rel _↝A_ _↝B_)
 _×⁺_ = subseq ×idconv ×subseq ×star

module _ (A : Set) (_↝A_ : ConvRel A) (B : Set) (_↝B_ : ConvRel B) where
 IsContinuous : (f : A -> B) -> Set
 IsContinuous f = ∀ {xs x} -> xs ↝A x -> (f ∘ xs) ↝B (f x)

 record Arr : Set where
  constructor _,_
  field
   f : A -> B
   cont : IsContinuous f

⇒rel :  ∀ {A B} (_↝A_ : ConvRel A) (_↝B_ : ConvRel B) -> ConvRel (Arr A _↝A_ B _↝B_)
⇒rel _↝A_ _↝B_ fs f = ∀ {xs x} → xs ↝A x → (λ n → Arr.f (fs n) (xs n)) ↝B Arr.f f x

module _ {A B : Set} (_↝A_ : ConvRel A) (pa : SubSeqSpace A _↝A_) (_↝B_ : ConvRel B) (pb : SubSeqSpace B _↝B_) where
 private module A = SubSeqSpace pa
 private module B = SubSeqSpace pb

 ⇒idconv : ∀ x -> ⇒rel _↝A_ _↝B_ (λ _ -> x) x
 ⇒idconv (f , cont) = cont

 ⇒subseq : ∀ {fs f} -> ⇒rel _↝A_ _↝B_ fs f -> (i : Subseq) -> ⇒rel _↝A_ _↝B_ (fs ∘ (Subseq.f i)) f
 ⇒subseq {fs} {f} g i {xs} {x} xs↝x = {!!}

-- _⇒⁺_ : SubSeqSpace -> SubSeqSpace -> SubSeqSpace
-- A ⇒⁺ B = record { U = (Arr A B) ; ↝ = (λ fs f →
--          ∀ {xs x} → SubSeqSpace.↝ A xs x → SubSeqSpace.↝ B (λ n → Arr.f (fs n) (xs n)) (Arr.f f x)) ; idconv = λ x x₂ → Arr.cont x x₂ }

-- tt⁺ : ∀ {A} -> Arr A 1⁺
-- tt⁺ = (λ x → unit) , (λ x₁ → tt)

-- inl⁺ : ∀ {A B} -> Arr A (A ⊎⁺ B)
-- inl⁺ = inj₁ , inl

-- inr⁺ : ∀ {A B} -> Arr B (A ⊎⁺ B)
-- inr⁺ = inj₂ , inr

-- _∘⁺_ : ∀ {A B C} -> Arr B C -> Arr A B -> Arr A C
-- (f , contf) ∘⁺ (g , contg)  = (f ∘ g) , contf ∘ contg

-- id⁺ : ∀ {A} -> Arr A A
-- id⁺ = id , id

-- fst⁺ : ∀ {A B} -> Arr (A ×⁺ B) A
-- fst⁺ = proj₁ , proj₁

-- snd⁺ : ∀ {A B} -> Arr (A ×⁺ B) B
-- snd⁺ = proj₂ , proj₂

-- <_,⁺_> : ∀ {A B C} -> Arr C A -> Arr C B -> Arr C (A ×⁺ B)
-- < (f , contf) ,⁺ (g , contg) > = < f , g > , < contf , contg >

-- [_,⁺_] : ∀ {A B C} -> Arr A C -> Arr B C -> Arr (A ⊎⁺ B) C
-- [_,⁺_] {subseq UA _↝₁_ ida} {subseq UB _↝₂_ idb} {subseq UC _↝₃_ idc} (f , contf) (g , contg) = [ f , g ] , helper
--  where helper : {xs : ℕ → UA ⊎ UB} {x : UA ⊎ UB} → Sum↝ (subseq UA _↝₁_ ida) (subseq UB _↝₂_ idb) xs x → ([ f , g ] ∘ xs) ↝₃ ([ f , g ] x)
--        helper (inl x) = contf x
--        helper (inr x) = contg x

-- λ⁺ : ∀ {A B C} -> Arr (A ×⁺ B) C -> Arr A (B ⇒⁺ C)
-- λ⁺ {subseq UA _↝₁_ ida} (f , cont) = (λ x → (λ x₁ → f (x , x₁)) , (λ x₂ → cont (ida x , x₂))) , (λ x₁ x₃ → cont (x₁ , x₃))

-- eval⁺ : ∀ {A B} -> Arr ((A ⇒⁺ B) ×⁺ A) B
-- eval⁺ = (λ { ((f , cont1) , x)  → f x }) , (λ { (fconv , xconv) → fconv xconv })

-- record ↝ℕ (ns : ℕ -> ℕ) (n : ℕ) : Set where
--  field 
--   bound : ℕ -- Can make irrelevant...
--   prop : ∀ m → m ≥ bound → ns m ≡ n

-- constConvℕ : (n : ℕ) -> ↝ℕ (λ _ -> n) n
-- constConvℕ n = record { bound = 0; prop = λ m x → refl }

-- ℕ⁺ : SubSeqSpace
-- ℕ⁺ = subseq ℕ ↝ℕ constConvℕ

-- 0⁺ : ∀ {Γ} -> Arr Γ ℕ⁺
-- 0⁺ {subseq UΓ ↝γ idγ} = (λ _ → 0) , (λ _ → constConvℕ 0)

-- suc⁺ : Arr ℕ⁺ ℕ⁺
-- suc⁺ = suc , (λ x₁ → record { bound = ↝ℕ.bound x₁; prop = λ m x → cong suc (↝ℕ.prop x₁ m x) })

-- iter : ∀ C -> Arr 1⁺ C -> Arr C C -> ℕ -> SubSeqSpace.U C
-- iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) zero = f unit
-- iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) (suc n) = f₁ (iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) n)

-- iter-cont :  ∀ C (z : Arr 1⁺ C) (f : Arr C C) -> IsContinuous ℕ⁺ C (iter C z f)
-- iter-cont C z f {xs} {zero} xs→x = {!xs→x!}
-- iter-cont C z f {xs} {suc x} xs→x = {!!}

-- rec⁺ : ∀ {Γ C} -> Arr Γ C -> Arr (Γ ×⁺ C) C -> Arr Γ ℕ⁺ -> Arr Γ C
-- rec⁺ {subseq U ↝ idconv} {subseq U₁ ↝₁ idconv₁} (f , cont) (f₁ , cont₁) (f₂ , cont₂) = {!!} , {!!}