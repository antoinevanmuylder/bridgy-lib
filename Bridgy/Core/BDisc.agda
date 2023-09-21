{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.BDisc where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit

lsen : ∀ {ℓ} {A : Type ℓ} {a0 a1 : A} → (a0 ≡ a1) → BridgeP (λ _ → A) a0 a1
lsen {A = A} {a0 = a0} aa = transport (λ i → BridgeP (λ _ → A) (aa i0) (aa i)) (λ _ → a0)


isBDisc : ∀ {ℓ} (A : Type ℓ) → Type ℓ
isBDisc A = ∀ (a0 a1 : A) → isEquiv (lsen {A = A} {a0 = a0} {a1 = a1})

BDisc : (ℓ : Level) → Type (ℓ-suc ℓ)
BDisc ℓ = Σ (Type ℓ) isBDisc

isBDisc→equiv : ∀ {ℓ} (A : Type ℓ) (bd : isBDisc A) (a0 a1 : A) →
  (a0 ≡ a1) ≃ (BridgeP (λ _ → A) a0 a1)
isBDisc→equiv A bd a0 a1 = lsen , (bd a0 a1)

-- being bridge-discrete over a bridge discrete type.
isBDiscP : ∀ {lA lB} (A : Type lA) (bd : isBDisc A) (B : A → Type lB) → Type (ℓ-max lA lB)
isBDiscP A bd B =
  ∀ (a0 a1 : A) (b0 : B a0) (b1 : B a1)
  (aa : a0 ≡ a1) (abdg : Bridge A a0 a1) (aprf : aa [ isBDisc→equiv A bd a0 a1 ] abdg) →
  PathP (λ i → B (aa i)) b0 b1 ≃ BridgeP (λ x → B (abdg x)) b0 b1
