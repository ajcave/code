module ModelProperties where
open import Syntax
open import SyntaxTm
open import Model
open import Sym
open import Transitivity
open import Cumulativity
open Syn Exp
open import Data.Product
open import Eval
open import Util
open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

⟦,⟧ctx-sym : HSYM ⊨_≈_ctx ⟦_⟧hctx ⊨_≈_ctx ⟦_⟧hctx
⟦,⟧ctx-sym tt tt tt = tt
⟦,⟧ctx-sym (dγ1 , x) (dγ2 , x₁) (vρ , x₂) = (⟦,⟧ctx-sym dγ1 dγ2 vρ) , (hsym* (x vρ) (x₁ (⟦,⟧ctx-sym dγ1 dγ2 vρ)) x₂)

