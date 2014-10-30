module BasicSystem.TerminationandCompleteness2 where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPEBigStep
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.BigStepSemantics
open import BasicSystem.StrongComputability
open import BasicSystem.IdentityEnvironment

mutual
  fundthrm : forall {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) -> SCE2 vs ->
             Σ (Val Γ σ) 
               \v -> eval t & vs ⇓ v × SCV2 v
  fundthrm top        (vs << v) (s<< svs sv) = sig v (pr rvar sv) 
  fundthrm (t [ ts ]) vs svs = 
     sig (σ₁ sw) 
         (pr (rsubs (π₁ (σ₂ sws)) (π₁ (σ₂ sw))) 
             (π₂ (σ₂ sw)))
     where
     sws = fundthrmˢ ts vs svs
     sw  = fundthrm t (σ₁ sws) (π₂ (σ₂ sws))
  fundthrm (λt t)      vs svs = 
    sig (λv t vs) 
        (pr rlam 
            (\{_} f a sa -> 
              let st = fundthrm t (emap f vs << a) (s<< (scemap2 f vs svs) sa) 
              in  sig (σ₁ st)
                      (pr (r$lam (π₁ (σ₂ st)))
                          (π₂ (σ₂ st))))
            )
  fundthrm (t $ u)    vs svs = 
    sig (σ₁ stu) 
        (pr (rapp (π₁ (σ₂ st)) 
                  (π₁ (σ₂ su)) 
                  (helper' (sym⁼ (oidvmap (σ₁ st))) (π₁ (σ₂ stu)))) 
            (π₂ (σ₂ stu)) 
            )
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = π₂ (σ₂ st) oid (σ₁ su) (π₂ (σ₂ su))

  fundthrmˢ : forall {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ) -> SCE2 vs ->
              Σ (Env B Δ) 
                \ws -> 
                  evalˢ ts & vs ⇓ ws × SCE2 ws
  fundthrmˢ (pop σ)   (vs << v) (s<< svs sv) = sig vs (pr rˢpop svs) 
  fundthrmˢ (ts < t)  vs        svs          = 
    sig (σ₁ sts << σ₁ st) 
        (pr (rˢcons (π₁ (σ₂ sts)) (π₁ (σ₂ st))) 
            (s<< (π₂ (σ₂ sts)) (π₂ (σ₂ st))) 
            ) 
    where
    sts = fundthrmˢ ts vs svs
    st  = fundthrm  t  vs svs
  fundthrmˢ id        vs        svs          = sig vs (pr rˢid svs) 
  fundthrmˢ (ts ○ us) vs        svs          = 
    sig (σ₁ sts) 
        (pr (rˢcomp (π₁ (σ₂ sus)) (π₁ (σ₂ sts))) 
            (π₂ (σ₂ sts))) 
    where
    sus = fundthrmˢ us vs svs
    sts = fundthrmˢ ts (σ₁ sus) (π₂ (σ₂ sus))

mutual
  quotlema : forall {Γ} σ {v : Val Γ σ} -> 
              SCV2 v -> Σ (Nf Γ σ) (\m -> quot v ⇓ m)
  quotlema ι {nev n} (sig m p) = sig (ne m) (qbase p)
  quotlema {Γ} (σ ⇒ τ) {v} sv =
    sig (λn (σ₁ qvvZ)) 
        (qarr (π₁ (σ₂ svvZ)) (σ₂ qvvZ))
    where
    svZ = quotlemb σ {varV (vZ {Γ})} qⁿvar
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotlema τ (π₂ (σ₂ svvZ))

  quotlemb : forall {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} -> 
              quotⁿ n ⇓ m -> SCV2 (nev n)
  quotlemb ι       {n} p = sig _ p
  quotlemb (σ ⇒ τ) {n}{m} p = \f a sa -> 
    let qla = quotlema σ sa
    in  sig (nev (appV (nevmap f n) a)) 
            (pr r$ne 
                (quotlemb τ 
                           (qⁿapp (quotⁿ⇓map f p) (σ₂ qla)) 
                           ))


scvar : forall {Γ σ}(x : Var Γ σ) -> SCV2 (nev (varV x))
scvar x = quotlemb _ qⁿvar

scid : forall Γ -> SCE2 (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap2 (weak σ) _ (scid Γ)) (scvar vZ) 

normthrm : forall {Γ σ}(t : Tm Γ σ) -> Σ (Nf Γ σ) \n -> nf t ⇓ n
normthrm t = sig (σ₁ qt) (norm⇓ (π₁ (σ₂ ft)) (σ₂ qt))
  where
  ft = fundthrm t vid (scid _)
  qt = quotlema _ (π₂ (σ₂ ft))