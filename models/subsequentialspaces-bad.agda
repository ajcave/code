module subsequentialspaces where
open import Data.Product
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

record SubSeq : Set₁ where
 constructor subseq
 field
  U : Set
  ↝ : (ℕ -> U) -> U -> Set
  idconv : ∀ x -> ↝ (λ n -> x) x

1⁺ : SubSeq
1⁺ = record { U = Unit ; ↝ = (λ x x₁ → ⊤) ; idconv = λ x → tt }

module _ (A B : SubSeq) where
 private
  Underlying : Set
  Underlying = (SubSeq.U A) ⊎ (SubSeq.U B)
 -- TODO: Crap, this needs to be able to flop around a little. Need a kind of closure operator
 data Sum↝ : (ℕ -> Underlying) -> Underlying -> Set where
  inl : ∀ {xs x} -> SubSeq.↝ A xs x -> Sum↝ (inj₁ ∘ xs) (inj₁ x)
  inr : ∀ {ys y} -> SubSeq.↝ B ys y -> Sum↝ (inj₂ ∘ ys) (inj₂ y)

 idsum : ∀ u -> Sum↝ (λ _ -> u) u
 idsum (inj₁ x) = inl (SubSeq.idconv A x)
 idsum (inj₂ y) = inr (SubSeq.idconv B y)

 _⊎⁺_ : SubSeq
 _⊎⁺_ = record { U = Underlying ; ↝ = Sum↝ ; idconv = idsum }

_×⁺_ : SubSeq -> SubSeq -> SubSeq
A ×⁺ B = record { U = ((SubSeq.U A) × (SubSeq.U B)) ; ↝ = (λ xs x → (SubSeq.↝ A (proj₁ ∘ xs) (proj₁ x)) × (SubSeq.↝ B (proj₂ ∘ xs) (proj₂ x))) ; idconv = λ x → (SubSeq.idconv A (proj₁ x)) , SubSeq.idconv B (proj₂ x) }

IsContinuous : (A B : SubSeq) (f : SubSeq.U A -> SubSeq.U B) -> Set
IsContinuous A B f = ∀ {xs x} -> SubSeq.↝ A xs x -> SubSeq.↝ B (f ∘ xs) (f x)

record Arr (A B : SubSeq) : Set where
 constructor _,_
 field
  f : SubSeq.U A -> SubSeq.U B
  cont : IsContinuous A B f

_⇒⁺_ : SubSeq -> SubSeq -> SubSeq
A ⇒⁺ B = record { U = (Arr A B) ; ↝ = (λ fs f →
         ∀ {xs x} → SubSeq.↝ A xs x → SubSeq.↝ B (λ n → Arr.f (fs n) (xs n)) (Arr.f f x)) ; idconv = λ x x₂ → Arr.cont x x₂ }

tt⁺ : ∀ {A} -> Arr A 1⁺
tt⁺ = (λ x → unit) , (λ x₁ → tt)

inl⁺ : ∀ {A B} -> Arr A (A ⊎⁺ B)
inl⁺ = inj₁ , inl

inr⁺ : ∀ {A B} -> Arr B (A ⊎⁺ B)
inr⁺ = inj₂ , inr

_∘⁺_ : ∀ {A B C} -> Arr B C -> Arr A B -> Arr A C
(f , contf) ∘⁺ (g , contg)  = (f ∘ g) , contf ∘ contg

id⁺ : ∀ {A} -> Arr A A
id⁺ = id , id

fst⁺ : ∀ {A B} -> Arr (A ×⁺ B) A
fst⁺ = proj₁ , proj₁

snd⁺ : ∀ {A B} -> Arr (A ×⁺ B) B
snd⁺ = proj₂ , proj₂

<_,⁺_> : ∀ {A B C} -> Arr C A -> Arr C B -> Arr C (A ×⁺ B)
< (f , contf) ,⁺ (g , contg) > = < f , g > , < contf , contg >

[_,⁺_] : ∀ {A B C} -> Arr A C -> Arr B C -> Arr (A ⊎⁺ B) C
[_,⁺_] {subseq UA _↝₁_ ida} {subseq UB _↝₂_ idb} {subseq UC _↝₃_ idc} (f , contf) (g , contg) = [ f , g ] , helper
 where helper : {xs : ℕ → UA ⊎ UB} {x : UA ⊎ UB} → Sum↝ (subseq UA _↝₁_ ida) (subseq UB _↝₂_ idb) xs x → ([ f , g ] ∘ xs) ↝₃ ([ f , g ] x)
       helper (inl x) = contf x
       helper (inr x) = contg x

λ⁺ : ∀ {A B C} -> Arr (A ×⁺ B) C -> Arr A (B ⇒⁺ C)
λ⁺ {subseq UA _↝₁_ ida} (f , cont) = (λ x → (λ x₁ → f (x , x₁)) , (λ x₂ → cont (ida x , x₂))) , (λ x₁ x₃ → cont (x₁ , x₃))

eval⁺ : ∀ {A B} -> Arr ((A ⇒⁺ B) ×⁺ A) B
eval⁺ = (λ { ((f , cont1) , x)  → f x }) , (λ { (fconv , xconv) → fconv xconv })

record ↝ℕ (ns : ℕ -> ℕ) (n : ℕ) : Set where
 field 
  bound : ℕ -- Can make irrelevant...
  prop : ∀ m → m ≥ bound → ns m ≡ n

constConvℕ : (n : ℕ) -> ↝ℕ (λ _ -> n) n
constConvℕ n = record { bound = 0; prop = λ m x → refl }

ℕ⁺ : SubSeq
ℕ⁺ = subseq ℕ ↝ℕ constConvℕ

0⁺ : ∀ {Γ} -> Arr Γ ℕ⁺
0⁺ {subseq UΓ ↝γ idγ} = (λ _ → 0) , (λ _ → constConvℕ 0)

suc⁺ : Arr ℕ⁺ ℕ⁺
suc⁺ = suc , (λ x₁ → record { bound = ↝ℕ.bound x₁; prop = λ m x → cong suc (↝ℕ.prop x₁ m x) })

iter : ∀ C -> Arr 1⁺ C -> Arr C C -> ℕ -> SubSeq.U C
iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) zero = f unit
iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) (suc n) = f₁ (iter (subseq U ↝ idconv) (f , cont) (f₁ , cont₁) n)

iter-cont :  ∀ C (z : Arr 1⁺ C) (f : Arr C C) -> IsContinuous ℕ⁺ C (iter C z f)
iter-cont C z f {xs} {zero} xs→x = {!xs→x!}
iter-cont C z f {xs} {suc x} xs→x = {!!}

rec⁺ : ∀ {Γ C} -> Arr Γ C -> Arr (Γ ×⁺ C) C -> Arr Γ ℕ⁺ -> Arr Γ C
rec⁺ {subseq U ↝ idconv} {subseq U₁ ↝₁ idconv₁} (f , cont) (f₁ , cont₁) (f₂ , cont₂) = {!!} , {!!}