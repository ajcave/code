module rec-types-cbpv where
open import FinMap
open import Unit
open import Product
open import Data.List
open import Data.Nat

{- We want this if we want both computational rec types and value rec types
data sort : Set where
 comp : sort
 val : sort
-}

* : Unitz
* = tt

mutual
 data ctpf (Δ : ctx Unitz) : Set where
  _⇒_ : (A : vtpf Δ) (B : ctpf Δ) -> ctpf Δ
  F : (A : vtpf Δ) -> ctpf Δ  -- embedding/producer/lift type
 data vtpf (Δ : ctx Unitz) : Set where
  μ : (T : vtpf (Δ , *)) -> vtpf Δ
  ▹ : (X : var Δ *) -> vtpf Δ
  U : (B : ctpf Δ) -> vtpf Δ -- thunk

mutual
 [_]ctr : ∀ {Δ1 Δ2} -> vsubst Δ1 Δ2 -> ctpf Δ1 -> ctpf Δ2
 [_]ctr σ (T ⇒ T₁) = ([ σ ]vtr T) ⇒ ([ σ ]ctr T₁)
 [_]ctr σ (F A) = F ([ σ ]vtr A)

 [_]vtr : ∀ {Δ1 Δ2} -> vsubst Δ1 Δ2 -> vtpf Δ1 -> vtpf Δ2
 [_]vtr σ (▹ X) = ▹ ([ σ ]v X)
 [_]vtr σ (μ T) = μ ([ vsub-ext σ ]vtr T)
 [_]vtr σ (U B) = U ([ σ ]ctr B)

fsubst : ∀ (Δ1 Δ2 : ctx Unitz) -> Set
fsubst Δ1 Δ2 = gksubst Δ1 (vtpf Δ2)

fsubst-ext : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> fsubst (Δ1 , *) (Δ2 , *)
fsubst-ext σ = (gmap [ wkn-vsub ]vtr σ) , (▹ top)

mutual
 [_]ct : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> ctpf Δ1 -> ctpf Δ2
 [_]ct σ (T ⇒ T₁) = ([ σ ]vt T) ⇒ ([ σ ]ct T₁)
 [_]ct σ (F A) = F ([ σ ]vt A)

 [_]vt : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> vtpf Δ1 -> vtpf Δ2
 [_]vt σ (▹ X) = [ σ ]v X
 [_]vt σ (μ T) = μ ([ fsubst-ext σ ]vt T)
 [_]vt σ (U B) = U ([ σ ]ct B)

id-fsub : ∀ {Δ : ctx Unitz} -> fsubst Δ Δ
id-fsub {⊡} = tt
id-fsub {Δ , T} = fsubst-ext id-fsub

[_/X]c : ∀ {Δ} -> vtpf Δ -> ctpf (Δ , *) -> ctpf Δ
[ A /X]c B = [ id-fsub , A ]ct B

[_/X]v : ∀ {Δ} -> vtpf Δ -> vtpf (Δ , *) -> vtpf Δ
[ A /X]v A₁ = [ id-fsub , A ]vt A₁

vtp : Set
vtp = vtpf ⊡

ctp : Set
ctp = ctpf ⊡

mutual
 data val (Γ : ctx Unitz) : Set where
  ▹ : (x : var Γ *) -> val Γ
  roll : (v : val Γ) -> val Γ
  thunk : (e : tm Γ) -> val Γ
 data tm (Γ : ctx Unitz) : Set where
  ƛ : (e : tm (Γ , *)) -> tm Γ
  _·_ : (e1 : tm Γ) (v : val Γ) -> tm Γ
  pm : ∀ (v : val Γ) (e : tm (Γ , *)) -> tm Γ -- aka let x = unfold y in ...
--  letbe : ∀ (v : val Γ) (e : tm (Γ , *)) -> tm Γ
  produce : (v : val Γ) -> tm Γ 
  _to_ : (e1 : tm Γ) (e2 : tm (Γ , *)) -> tm Γ
  force : (v : val Γ) -> tm Γ

〈_〉 : ctx vtp -> ctx Unitz
〈 ⊡ 〉 = ⊡
〈 Γ , T 〉 = 〈 Γ 〉 , *

〈_〉v : ∀ {Γ T} -> var Γ T -> var 〈 Γ 〉 *
〈 top 〉v = top
〈 pop x 〉v = pop 〈 x 〉v

mutual
 data _⊢v_∶_ (Γ : ctx vtp) : val 〈 Γ 〉 -> vtp -> Set where
   ▹ : ∀ {A} (x : var Γ A) -> Γ ⊢v ▹ 〈 x 〉v ∶ A
   roll : ∀ (A : vtpf (⊡ , *)) {e} -> Γ ⊢v e ∶ ([ μ A /X]v A) -> Γ ⊢v (roll e) ∶ (μ A)
   thunk : ∀ {B} {e} -> Γ ⊢c e ∶ B -> Γ ⊢v (thunk e) ∶ (U B)
 data _⊢c_∶_ (Γ : ctx vtp) : tm 〈 Γ 〉 -> ctp -> Set where
   ƛ : ∀ {A B} {e} -> (Γ , A) ⊢c e ∶ B -> Γ ⊢c (ƛ e) ∶ (A ⇒ B)
   _·_ : ∀ {A B} {e v} -> Γ ⊢c e ∶ (A ⇒ B) -> Γ ⊢v v ∶ A -> Γ ⊢c (e · v) ∶ B
   pm : ∀ {A : vtpf (⊡ , *)} {B} {v e} -> Γ ⊢v v ∶ (μ A) -> (Γ , [ μ A /X]v A) ⊢c e ∶ B -> Γ ⊢c (pm v e) ∶ B
   produce : ∀ {A v} -> Γ ⊢v v ∶ A -> Γ ⊢c (produce v) ∶ (F A)
   _to_ : ∀ {A B e1 e2} -> Γ ⊢c e1 ∶ (F A) -> (Γ , A) ⊢c e2 ∶ B -> Γ ⊢c (e1 to e2) ∶ B
   force : ∀ {B v} -> Γ ⊢v v ∶ (U B) -> Γ ⊢c (force v) ∶ B

-- If all we care about is CBV, then is there a more direct CK machine way to do it?
-- Something like A normal form?

mutual
 [_]vr : ∀ {Γ1 Γ2} -> vsubst Γ1 Γ2 -> val Γ1 -> val Γ2
 [_]vr w (▹ x) = ▹ ([ w ]v x)
 [_]vr w (roll e) = roll ([ w ]vr e)
 [_]vr w (thunk e) = thunk ([ w ]cr e)
 
 [_]cr : ∀ {Γ1 Γ2} -> vsubst Γ1 Γ2 -> tm Γ1 -> tm Γ2
 [_]cr w (ƛ e) = ƛ ([ vsub-ext w ]cr e)
 [_]cr w (e · e₁) = ([ w ]cr e) · ([ w ]vr e₁)
 [_]cr w (pm v e) = pm ([ w ]vr v) ([ vsub-ext w ]cr e)
 [_]cr w (produce v) = produce ([ w ]vr v)
 [_]cr w (e1 to e2) = ([ w ]cr e1) to ([ vsub-ext w ]cr e2)
 [_]cr w (force v) = force ([ w ]vr v)

tsubst : ∀ (Δ1 Δ2 : ctx Unitz) -> Set
tsubst Δ1 Δ2 = gksubst Δ1 (val Δ2)

tsubst-ext : ∀ {Δ1 Δ2 T} -> tsubst Δ1 Δ2 -> tsubst (Δ1 , T) (Δ2 , T)
tsubst-ext σ = (gmap [ wkn-vsub ]vr σ) , (▹ top)

mutual
 [_]vv : ∀ {Γ1 Γ2} -> tsubst Γ1 Γ2 -> val Γ1 -> val Γ2
 [_]vv w (▹ x) = [ w ]v x
 [_]vv w (roll e) = roll ([ w ]vv e)
 [_]vv w (thunk e) = thunk ([ w ]cv e)
 
 [_]cv : ∀ {Γ1 Γ2} -> tsubst Γ1 Γ2 -> tm Γ1 -> tm Γ2
 [_]cv w (ƛ e) = ƛ ([ tsubst-ext w ]cv e)
 [_]cv w (e · e₁) = ([ w ]cv e) · ([ w ]vv e₁)
 [_]cv w (pm v e) = pm ([ w ]vv v) ([ tsubst-ext w ]cv e)
 [_]cv w (produce v) = produce ([ w ]vv v)
 [_]cv w (e1 to e2) = ([ w ]cv e1) to ([ tsubst-ext w ]cv e2)
 [_]cv w (force v) = force ([ w ]vv v)


id-tsub : ∀ {Δ : ctx Unitz} -> tsubst Δ Δ
id-tsub {⊡} = tt
id-tsub {Δ , T} = tsubst-ext id-tsub

[_/x] : ∀ {Δ T} -> val Δ -> tm (Δ , T) -> tm Δ
[ e2 /x] e1 = [ id-tsub , e2 ]cv e1

data ε1 : Set where
 []· : val ⊡ -> ε1
 []to : tm (⊡ , *) -> ε1

-- Aka evaluation context
Stack : Set
Stack = List ε1


-- Could think of writing it using a ε [ M ] ↝ ε [ N ] kind of notation instead (just another way to view the stack)

-- Nice: Each computational constructor has a rule, and that's it.
data _∣_↝_∣_ : tm ⊡ -> Stack -> tm ⊡ -> Stack -> Set where
 ƛ : ∀ {K e v} -> (ƛ e) ∣ []· v ∷ K ↝ [ v /x] e ∣ K
 pm : ∀ {K e v} -> (pm (roll v) e) ∣ K ↝ [ v /x] e ∣ K
 to : ∀ {K e1 e2} -> (e1 to e2) ∣ K ↝ e1 ∣ (([]to e2) ∷ K)
 produce : ∀ {K v e} -> (produce v) ∣ ([]to e) ∷ K ↝ [ v /x] e ∣ K
 force : ∀ {K e} -> (force (thunk e)) ∣ K ↝ e ∣ K
 app : ∀ {K e v} -> (e · v) ∣ K ↝ e ∣ ([]· v ∷ K)

data _∣_↝*_∣_ : tm ⊡ -> Stack -> tm ⊡ -> Stack -> Set where
 refl : ∀ {e K} -> e ∣ K ↝* e ∣ K
 trans1 : ∀ {e1 K1 e2 K2 e3 K3} ->
      e1 ∣ K1 ↝  e2 ∣ K2
   -> e2 ∣ K2 ↝* e3 ∣ K3
   -> e1 ∣ K1 ↝* e3 ∣ K3

_↝*_ : tm ⊡ -> tm ⊡ -> Set
e1 ↝* e2 = e1 ∣ [] ↝* e2 ∣ []

VRel : Set₁
VRel = ℕ -> val ⊡ -> val ⊡ -> Set

CRel : Set₁
CRel = ℕ -> tm ⊡ -> tm ⊡ -> Set

relsubst : ctx Unitz -> Set₁
relsubst Δ = gksubst Δ VRel

data U⁺ (R : CRel) : VRel where
 con : ∀ {n e1 e2} -> R n e1 e2 -> U⁺ R n (thunk e1) (thunk e2)

data F⁺ (R : VRel) : CRel where
 con : ∀ {n e1 v1 e2 v2} -> e1 ↝* (produce v1) -> e2 ↝* (produce v2) -> R n v1 v2 -> F⁺ R n e1 e2
   -- TODO: This is wrong. Do something LSLR-ish with a ▹ modality?

data F'⁺ (k : ℕ) (R : ∀ j -> j < k -> val ⊡ -> val ⊡ -> Set) : tm ⊡ -> tm ⊡ -> Set where
 con : ∀ {j e1 v1 e2 v2} (p : j < k) -> e1 ↝* (produce v1) -> e2 ↝* (produce v2) -> R j p v1 v2 -> F'⁺ k R e1 e2

data isRoll (R : val ⊡ -> val ⊡ -> Set) : val ⊡ -> val ⊡ -> Set where
 con : ∀ {v1 v2} -> R v1 v2 -> isRoll R (roll v1) (roll v2)



_⇒⁺_ : VRel -> CRel -> CRel
(VR ⇒⁺ CR) n e1 e2 = {v1 v2 : _} → VR n v1 v2 → CR n (e1 · v1) (e2 · v2)  -- TODO: This will need to become Kripke-ish

{-μ⁺ : (AF : (k : ℕ) -> (∀ j -> j < k -> val ⊡ -> val ⊡ -> Set) -> val ⊡ -> val ⊡ -> Set) -> VRel
μ⁺ AF zero v1 v2 = Unit
μ⁺ AF (suc n) v1 v2 = isRoll (AF n (λ j x → μ⁺ AF j)) v1 v2

extend : ∀ {Δ} {C : Set₁} -> (σ : var Δ * -> C) -> (R : C) -> var (Δ , *) * -> C
extend σ R top = R
extend σ R (pop x) = σ x 

mutual
 V : ∀ {Δ} -> vtpf Δ -> (k : ℕ) -> (var Δ * -> ∀ j -> j < k -> val ⊡ -> val ⊡ -> Set) -> val ⊡ -> val ⊡ -> Set
 V (μ A) k ρ = μ⁺ (λ k₁ x → V A k (extend ρ {!!})) k --(λ k₁ x → V A k₁ (λ j x₁ → extend (ρ j {!!}) (x j x₁)) ) k
 V (▹ X) zero ρ = λ x x₁ → Unit
 V (▹ X) (suc k) ρ = ρ X k {!!}
 V (U B) k ρ = {!!}

 E : ∀ {Δ} -> ctpf Δ -> (k : ℕ) -> (var Δ * -> ∀ j -> j < k ->  val ⊡ -> val ⊡ -> Set) -> tm ⊡ -> tm ⊡ -> Set
 E (A ⇒ B) k ρ = {!!}
 E (F A) k ρ = F'⁺ k (λ j x → V A k ρ)-}

 

iter : ∀ {C : Set₁} -> (AF : C -> C) -> C -> ℕ -> C
iter AF b zero = b
iter AF b (suc n) = AF (iter AF b n)

1⁺ : VRel
1⁺ n v1 v2 = Unit

μ⁺ : (VRel -> VRel) -> VRel
μ⁺ AF n = iter AF 1⁺ (suc n) n

▸ : VRel -> VRel
▸ R zero v1 v2 = Unit
▸ R (suc n) v1 v2 = R n v1 v2

_⇾_ : VRel -> VRel -> Set
T ⇾ S = ∀ n v₁ v₂ → T n v₁ v₂ → S n v₁ v₂

_⇛_ : VRel -> VRel -> VRel
(T ⇛ S) n v1 v2 = ∀ k -> k ≤ n -> T k v1 v2 -> S k v1 v2

CMap : (VRel -> VRel) -> Set₁
CMap G = (X Y : VRel) → ▸ (X ⇛ Y) ⇾ (G X ⇛ G Y)

Map : (VRel -> VRel) -> Set₁
Map G = (X Y : VRel) → (X ⇛ Y) ⇾ (G X ⇛ G Y)

-- inj : ∀ {C : VRel} -> C ⇾ ▸ C
-- inj zero v1 v2 t = tt
-- inj (suc n) v1 v2 t = {!!}

≤refl : ∀ n -> n ≤ n
≤refl zero = z≤n
≤refl (suc n) = s≤s (≤refl n)

≤inc : ∀ {k n} -> k ≤ n -> k ≤ (suc n)
≤inc z≤n = z≤n
≤inc (s≤s p) = s≤s (≤inc p)

≤trans : ∀ {n m k} -> n ≤ m -> m ≤ k -> n ≤ k
≤trans z≤n p2 = z≤n
≤trans (s≤s p1) (s≤s p2) = s≤s (≤trans p1 p2)

-- G locally contractive means that:
-- 1) (G X)(0) -> (G Y)(0) for any X and Y (they're irrelevant cause they occur under ▸)
-- 2) If    ∀ k ≤ n.          X (k) ->    Y (k)
--    Then  ∀ k ≤ (suc n). (G X)(k) -> (G Y)(k)
-- (For covariant G. mixed variance is more complicated..)
-- This looks like a more refined/restricted version of functoriality. Interesting
-- It's an internalized, contractive map (above)

mutual
 bar : ∀ (G : VRel -> VRel) (map : CMap G) n k i v1 v2 -> i < k -> i < n -> (iter G 1⁺ n) i v1 v2 -> (iter G 1⁺ k) i v1 v2
 bar G map n zero i v1 v2 () k≤n x
 bar G map zero (suc k) i v1 v2 i≤k () x
 bar G map (suc n) (suc k) i v1 v2 (s≤s i≤k) (s≤s k≤n) x = map (iter G 1⁺ n) (iter G 1⁺ k) i v1 v2 (baz G map n k i v1 v2 i≤k k≤n) i (≤refl i) x
 
 baz : ∀ (G : VRel -> VRel) (map : CMap G) n k i v1 v2 -> i ≤ k -> i ≤ n -> ▸ ((iter G 1⁺ n) ⇛ (iter G 1⁺ k)) i v1 v2
 baz G map n k zero v1 v2 i<k k≤n = tt
 baz G map .(suc n) .(suc k) (suc i) v1 v2 (s≤s {.i} {k} i<k) (s≤s {.i} {n} k≤n) = λ k₁ x x₁ → bar G map (suc n) (suc k) k₁ v1 v2 (s≤s (≤trans x i<k)) (s≤s (≤trans x k≤n)) x₁ 

mutual
 roll⁺ : ∀ (G : VRel -> VRel) (map : CMap G) -> (μ⁺ G) ⇾ (G (μ⁺ G))
 roll⁺ G map n v1 v2 t = map (iter G 1⁺ n) (μ⁺ G) n v1 v2 (quux G map n v1 v2) n (≤refl _) t

 quux : ∀ (G : VRel -> VRel) (map : CMap G) n v1 v2 -> ▸ (iter G 1⁺ n ⇛ μ⁺ G) n v1 v2
 quux G map zero v1 v2 = tt
 quux G map (suc n) v1 v2 = λ k x x₁ → bar G map (suc n) (suc k) k v1 v2 (≤refl _) (s≤s x) x₁

mutual
 unroll⁺ : ∀ (G : VRel -> VRel) (map : CMap G) -> (G (μ⁺ G)) ⇾ (μ⁺ G)
 unroll⁺ G map n v1 v2 t = map (μ⁺ G) (iter G 1⁺ n) n v1 v2 (unquux G map n v1 v2) n (≤refl _) t

 unquux : ∀ (G : VRel -> VRel) (map : CMap G) n v1 v2 -> ▸ (μ⁺ G ⇛ iter G 1⁺ n) n v1 v2
 unquux G map zero v1 v2 = tt
 unquux G map (suc n) v1 v2 = λ k x x₁ → bar G map (suc k) (suc n) k v1 v2 (s≤s x) (≤refl _) x₁

fix : ∀ {A : VRel} -> ((▸ A) ⇛ A) ⇾ A
fix zero v1 v2 f = f 0 z≤n tt
fix {A} (suc n) v1 v2 f = f (suc n) (≤refl (suc n)) (fix {A} n v1 v2 (λ k x x₁ → f k (≤inc x) x₁)) -- This reminds me of proving well-founded induction..

fix' : ∀ {A : VRel} -> ((▸ A) ⇾ A) -> ∀ n v1 v2 -> A n v1 v2
fix' f zero v1 v2 = f zero v1 v2 tt
fix' f (suc n) v1 v2 = f (suc n) v1 v2 (fix' f n v1 v2)

mutual
 V : ∀ {Δ} -> vtpf Δ -> relsubst Δ -> VRel
 V (μ A) ρ = μ⁺ (λ R → V A (ρ , ▸ R))
 V (▹ X) ρ = [ ρ ]v X
 V (U B) ρ = U⁺ (E B ρ)

 E : ∀ {Δ} -> ctpf Δ -> relsubst Δ -> CRel
 E (A ⇒ B) ρ = V A ρ ⇒⁺ E B ρ
 E (F A)    ρ = F⁺ (V A ρ)

 
 

