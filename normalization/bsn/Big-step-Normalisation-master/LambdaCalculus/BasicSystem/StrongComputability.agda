module BasicSystem.StrongComputability where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPEBigStep
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.BigStepSemantics

SCV : forall {Γ σ} -> Val Γ σ -> Set
SCV {Γ} {ι}     (nev n) = Σ (NeN Γ ι) \m -> quotⁿ n ⇓ m × (embⁿ n ≃ nembⁿ m)
SCV {Γ} {σ ⇒ τ} v       = forall {B}(f : OPE B Γ)(a : Val B σ) -> SCV a -> 
  Σ (Val B τ) 
    \w -> (vmap f v $$ a ⇓ w) ∧ SCV w ∧ (emb (vmap f v) $ emb a ≃ emb w)  

SCV2 : forall {Γ σ} -> Val Γ σ -> Set
SCV2 {Γ} {ι}     (nev n) = Σ (NeN Γ ι) \m -> quotⁿ n ⇓ m
SCV2 {Γ} {σ ⇒ τ} v       = forall {B}(f : OPE B Γ)(a : Val B σ) -> SCV2 a -> 
  Σ (Val B τ) 
    \w -> (vmap f v $$ a ⇓ w) × SCV2 w

data SCE {Γ : Con} : forall {Δ} -> Env Γ Δ -> Set where
  sε : SCE ε
  s<< : forall {Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} ->
        SCE vs -> SCV v -> SCE (vs << v)

data SCE2 {Γ : Con} : forall {Δ} -> Env Γ Δ -> Set where
  sε : SCE2 ε
  s<< : forall {Δ σ}{vs : Env Γ Δ}{v : Val Γ σ} ->
        SCE2 vs -> SCV2 v -> SCE2 (vs << v)

helper : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ} ->
    Σ (Val Θ τ) (\v -> (f' $$ a ⇓ v) ∧ SCV v ∧ (emb f' $ emb a ≃ emb v)) ->
    Σ (Val Θ τ) \v -> (f $$ a ⇓ v) ∧ SCV v ∧ (emb f $ emb a ≃ emb v)
helper refl⁼ p = p 

helper2 : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ} ->
    Σ (Val Θ τ) (\v -> (f' $$ a ⇓ v) × SCV2 v) ->
    Σ (Val Θ τ) \v -> (f $$ a ⇓ v) × SCV2 v
helper2 refl⁼ p = p 

helper' : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ}{v : Val Θ τ}-> f' $$ a ⇓ v -> f $$ a ⇓ v
helper' refl⁼ p = p 

helper'' : forall {Θ}{σ}{τ}{f f' : Val Θ (σ ⇒ τ)} -> f == f' -> 
    {a : Val Θ σ}{v : Val Θ τ} -> 
    emb f' $ emb a ≃ emb v -> emb f $ emb a ≃ emb v
helper'' refl⁼ p = p 

scvmap : forall {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) -> SCV v -> SCV (vmap f v)
scvmap {σ = ι}     f (nev m) (sig n (pr p q)) = 
  sig (nenmap f n) 
      (pr (quotⁿ⇓map f p) 
          (trans (onevemb f m) (trans (cong[] q reflˢ) (sym (onenemb f n)))))
scvmap {σ = σ ⇒ τ} f v       sv = \f' a sa -> 
  helper (compvmap f' f v) (sv (comp f' f) a sa) 

scvmap2 : forall {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) -> SCV2 v -> SCV2 (vmap f v)
scvmap2 {σ = ι}     f (nev m) (sig n p) = 
  sig (nenmap f n) (quotⁿ⇓map f p)
scvmap2 {σ = σ ⇒ τ} f v       sv = \f' a sa -> {!!}
--  helper2 (compvmap f' f v) (sv (comp f' f) a sa) 

scemap : forall {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) -> 
         SCE vs -> SCE (emap f vs)
scemap f ε         sε         = sε 
scemap f (vs << v) (s<< p p') = s<< (scemap f vs p) (scvmap f v p') 

scemap2 : forall {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) -> 
         SCE2 vs -> SCE2 (emap f vs)
scemap2 f ε         sε         = sε 
scemap2 f (vs << v) (s<< p p') = s<< (scemap2 f vs p) (scvmap2 f v p') 
