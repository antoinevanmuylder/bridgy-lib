------------------------------------------------------------------------
-- In this file we prove the church encoding for booleans in a
-- low level style, as done in theorem 3.1 of the CH paper
-- https://lmcs.episciences.org/8651/. This is to compare with our
-- churchBool theorem from Bridgy.Examples.Church.
------------------------------------------------------------------------
{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.LowLevel where


-- we don't import anything from ROTT
open import Bridgy.Core.BridgePrims
open import Bridgy.Core.ExtentExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool



lowChurchBool : ∀ {l} → ( ∀ (X : Type l) → X → X → X ) ≃ Bool
lowChurchBool {l} = isoToEquiv (iso
  chToBool
  boolToCh
  (λ { true → refl ; false → refl })
  -- using the notations of CH, and closely following their proof.
  λ k → funExt λ A → funExt λ t → funExt λ f →
    ungl k A t f)

  where

    boolToCh : ∀ {l} → Bool → ( ∀ (X : Type l) → X → X → X )
    boolToCh true X xt xf = xt
    boolToCh false X xt xf = xf

    chToBool : ∀ {l} → ( ∀ (X : Type l) → X → X → X ) → Bool
    chToBool ch = ch (Lift Bool) (lift true) (lift false) .lower

    module CH-inverse-cond {l} (k : ∀ (X : Type l) → X → X → X) (A : Type l) (t f : A) where

      R : Lift Bool → A → Type l
      R = λ b a → (boolToCh (b .lower) A t f) ≡ a

      k-Gelx : (@tick x : BI) → primGel (Lift Bool) A  R x → primGel (Lift Bool) A R x → primGel (Lift Bool) A R x 
      k-Gelx x = k (primGel (Lift Bool) A  R x)

      k-Gelx-gel-gel : (@tick x : BI) → primGel (Lift Bool) A R x
      k-Gelx-gel-gel x = k-Gelx x (prim^gel (lift true) t (refl) x) ((prim^gel (lift false) f (refl) x))

      asBdg : BridgeP (λ x → primGel (Lift Bool) A R x) (k (Lift Bool) (lift true) (lift false)) (k A t f)
      asBdg x = k-Gelx-gel-gel x

      ungl : R (k (Lift Bool) (lift true) (lift false)) (k A t f)
      ungl = prim^ungel {R = R} λ x → asBdg x
  
    open CH-inverse-cond
