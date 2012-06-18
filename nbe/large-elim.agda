module large-elim where

-- Pretty much a direct transcription of McBride's "Outrageous but Meaningful Coincidences"
record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Σ (A : Set) (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

record Unit : Set where
 constructor tt

data Bool : Set where
 true false : Bool

postulate
 atomic_tp : Set

mutual
 data U : Set where
  unit bool : U
  Π : (S : U) -> (T : El S -> U) -> U

 El : U -> Set
 El unit = Unit
 El bool = Bool
 El (Π S T) = (s : El S) -> El (T s)

If' : Bool -> U -> U -> U
If' true T F = T
If' false T F = F

mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (T : 〚 Γ 〛c -> U) -> ctx

 〚_〛c : ctx -> Set
 〚 ⊡ 〛c = Unit
 〚 Γ , T 〛c = Σ 〚 Γ 〛c (λ γ  → El (T γ))

_∘_ : ∀ {R : Set} {S : R -> Set} {T : (r : R) -> S r -> Set}
 -> (∀ {r} (s : S r) -> T r s)
 -> (g : (r : R) -> S r)
 -> (r : R) -> T r (g r)
f ∘ g = λ x -> f (g x)

data _∋_ : (Γ : ctx) -> (T : 〚 Γ 〛c -> U) -> Set where
 top : ∀ {Γ T} -> (Γ , T) ∋ (T ∘ Σ.fst)
 pop : ∀ {Γ T S} -> Γ ∋ T -> (Γ , S) ∋ (T ∘ Σ.fst)

〚_〛v : ∀ {Γ T} -> Γ ∋ T -> (γ : 〚 Γ 〛c) -> El (T γ)
〚_〛v {⊡} () tt
〚_〛v {Γ , T} top (γ , t) = t
〚_〛v {Γ , T} (pop y) (γ , s) = 〚 y 〛v γ

κ : ∀ {Γ : Set} {X : Set} -> X -> Γ -> X 
κ x γ = x

_ss_ : ∀ {Γ : Set} {S : Γ -> Set} {T : (γ : Γ) -> S γ -> Set}
 -> (f : (γ : Γ) (s : S γ) -> T γ s)
 -> (s : (γ : Γ) -> S γ)
 -> (γ : Γ) -> T γ (s γ)
_ss_ = λ f s γ -> f γ (s γ)

infixl 9 _ss_

∨ : ∀ {S T} {P : Σ S T -> Set}
 -> (p : (s : S) (t : T s) -> P (s , t))
 -> ((st : Σ S T) -> P st)
∨ p (s , t) = p s t

∧ : ∀ {S T} {P : Σ S T -> Set}
 -> ((st : Σ S T) -> P st)
 -> (s : S) (t : T s) -> P (s , t)
∧ p s t = p (s , t)

mutual
 data _⋆_ (Γ : ctx) : (T : 〚 Γ 〛c -> U) -> Set where
  unit : Γ ⋆ κ unit 
  bool : Γ ⋆ κ bool
  Π : ∀ {S T} -> Γ ⋆ S -> (Γ , S) ⋆ T
              ------------------------
              -> Γ ⋆ (κ Π ss S ss ∧ T)
  If : ∀ {T F} -> (b : Γ ⊢ κ bool) -> Γ ⋆ T -> Γ ⋆ F
               --------------------------------------
               -> Γ ⋆ (κ If' ss 〚 b 〛⊢ ss T ss F)
 data _⊢_ (Γ : ctx)  : (T : 〚 Γ 〛c -> U) -> Set where
  var : ∀ {T} -> Γ ∋ T -> Γ ⊢ T 
  tt : Γ ⊢ κ unit
  true false : Γ ⊢ κ bool
  If : ∀ {P} -> (b : Γ ⊢ κ bool) -> (Γ , κ bool) ⋆ P -> Γ ⊢ ((∧ P) ss κ true) -> Γ ⊢ ((∧ P) ss κ false)
             -> Γ ⊢ ((∧ P) ss 〚 b 〛⊢)
  ƛ : ∀ {S T} -> (Γ , S) ⊢ (∨ T) -> Γ ⊢ λ γ → Π (S γ) (T γ)
  _·_ : ∀ {S} {T : (γ : 〚 Γ 〛c) -> El (S γ) -> U} -> (Γ ⊢ λ γ → Π (S γ) (T γ)) -> (s : Γ ⊢ S) -> Γ ⊢ λ γ → T γ (〚 s 〛⊢ γ) 

 〚_〛⊢ : ∀ {Γ T} -> Γ ⊢ T -> (γ : 〚 Γ 〛c) -> El (T γ)
 〚_〛⊢ (var y) = 〚 y 〛v
 〚_〛⊢ tt = κ tt
 〚_〛⊢ true = κ true
 〚_〛⊢ false = κ true
 〚_〛⊢ (If {P} b _ M N) = IfHelp ss 〚 b 〛⊢
  where IfHelp : (γ : _) (b : Bool) -> El (P (γ , b))
        IfHelp γ true = 〚 M 〛⊢ γ
        IfHelp γ false = 〚 N 〛⊢ γ
 〚_〛⊢ (ƛ M) = ∧ 〚 M 〛⊢
 〚_〛⊢ (M · N) = 〚 M 〛⊢ ss 〚 N 〛⊢

-- Can we define "sem" and do NbE? (Which would be a "nicer" NbE than Abel's "NbE for MLTT with one universe")
-- Also McBride outlines in the appendix how to extend Kipling with a universe. Could we tehn do NbE for it?
-- Remember that T is not a type in the same way anymore.. now it's a "section(?)" (display map(?)) (Σ Γ T -> Γ) 