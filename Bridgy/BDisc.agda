{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module Bridgy.BDisc where

open import Bridgy.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv


lsen : ∀ {ℓ} {A : Type ℓ} {a0 a1 : A} → (a0 ≡ a1) → BridgeP (λ _ → A) a0 a1
lsen {A = A} {a0 = a0} aa = transport (λ i → BridgeP (λ _ → A) (aa i0) (aa i)) (λ _ → a0)


isBDisc : ∀ {ℓ} (A : Type ℓ) → Type ℓ
isBDisc A = ∀ (a0 a1 : A) → isEquiv (lsen {A = A} {a0 = a0} {a1 = a1})

BDisc : (ℓ : Level) → Type (ℓ-suc ℓ)
BDisc ℓ = Σ (Type ℓ) isBDisc

isBDisc→equiv : ∀ {ℓ} (A : Type ℓ) (bd : isBDisc A) (a0 a1 : A) →
  (a0 ≡ a1) ≃ (BridgeP (λ _ → A) a0 a1)
isBDisc→equiv A bd a0 a1 = lsen , (bd a0 a1)
