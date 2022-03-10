{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module SystemF-NRGsem where

{-
part of the experiment about predicative systemF. see old/SystemF.agda
-}

-- open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Data.Vec
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.FinData.Base as FIN
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Functions.FunExtEquiv
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Prod
-- open import Cubical.Data.Sigma using (_×_ ; ≃-× ; ≡-×)
-- open import Cubical.Foundations.Function
open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import NativeReflGraphRelator
open import SystemF

{-
In what follows we give an interpretation of predicative systemF open types α₁ : *ℓ₁ , ... , αₙ : * ℓₙ ⊢ A : *ℓ
as native relators ⟦A⟧ : Typeℓ₁ × ... × Typeℓₙ → Type ℓ
This can be regarded as a shallow embedding of systemF: the agda term `λ X x → x` plays the
same role than the systemF term `Λ X. λ x. x`.          (*)
The absence of cumulativity in agda
(1) makes it difficult to define a notion of model encompassing the "interpretation by unquoting"
    that we give here
(2) forces us to keep track of the universe levels and results in interpretation maps being dependent functions, instead
    of functions.

With more work, the (*) correspondance above could be made formal, ie systemF terms can be interpreted as well.
And in fact the obtained sysF model is a parametric one: denotation of terms respect relations. This is due to the
fact that we interpret types as native relators, and that we have a parametricity theorem for native relators.
-}

-- we interpret *i ↦ Type i
toL : FKind → Level
toL 0 = ℓ-zero
toL (suc n) = ℓ-suc (toL n)

⟦_⟧kind : (ℓ : FKind) → Type (ℓ-suc (toL ℓ))
⟦_⟧kind ℓ = Type (toL ℓ)


-- maxKind : ∀ {n} (Θ : FKindCtx n) → FKind
-- maxKind [] = 0
-- maxKind (ℓ ∷ Θ) = max ℓ (maxKind Θ)

-- maxLev : ∀ {n} (Θ : FKindCtx n) → Level
-- maxLev Θ = toL (maxKind Θ)

-- the intent is that ⟦ Θ ⟧ = Typeℓ₁ × ... × Type ℓₙ : Type (withLev Θ) (= 0 | max_i (ℓᵢ + 1))
withLev :  ∀ {n} (Θ : FKindCtx n) → Level
withLev [] = ℓ-zero
withLev (ℓ ∷ Θ) = ℓ-max (ℓ-suc (toL ℓ)) (withLev Θ)

toType : ∀ {n} (Θ : FKindCtx n) → Type (withLev Θ)
toType [] = ⊤
toType (ℓ ∷ Θ) = (Type (toL ℓ)) × (toType Θ)

-- maxLev : ∀ {n} → Vec Level n → Level
-- maxLev [] = ℓ-zero
-- maxLev (ℓ ∷ v) = ℓ-max ℓ (maxLev v)



-- -- heterogeneous vectors
-- data hVec : (n : ℕ) → (vℓ : Vec Level n) → Type (maxLev vℓ)
--   atIndex : Fin n → hVec n vℓ

-- it : ∀ {a} {A : Set a} → {{A}} → A
-- it {{x}} = x

-- -- recursively defined `instance` 's can not exist
-- hasNRGSemCtx : ∀ {n} (Θ : FKindCtx n) → HasNRGraph (toType Θ)
-- hasNRGSemCtx [] = it
-- hasNRGSemCtx (ℓ ∷ Θ) = prodHasNRG ⦃ hnrgH = hasNRGSemCtx Θ ⦄

-- ⟦_⟧kctx : ∀ {n} (Θ : FKindCtx n) → NRGraph (withLev Θ)
-- ⟦_⟧kctx Θ = mkNRGraph (toType Θ) ⦃ has-nativergraph = hasNRGSemCtx Θ ⦄



-- ⟦_⟧kjudg : ∀ {n} {Θ : FKindCtx n} {ℓ : FKind} → FKjudg Θ ℓ → NRelator' ⟦ Θ ⟧kctx  ⟦ ℓ ⟧kind
-- ⟦_⟧kjudg (FtyvarJ zero) = record { nobjMap = {!!} ; nedgeMap = {!!} ; nativ-rel = {!!} } 
-- ⟦_⟧kjudg (FtyvarJ (suc k)) = {!!}
-- ⟦_⟧kjudg _ = {!!}
