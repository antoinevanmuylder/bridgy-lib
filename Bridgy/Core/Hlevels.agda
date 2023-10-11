------------------------------------------------------------------------
-- Some theorems describing the h-level of the BridgeP former in
-- various situations
------------------------------------------------------------------------
{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Core.Hlevels where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BridgeExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels


module _ {ℓ} {P : (@tick x : BI) → Type ℓ} (isp : (@tick x : BI) → isProp (P x)) {p0 : P bi0} {p1 : P bi1} where

  BridgeP-over-propline : isProp (BridgeP P p0 p1)
  BridgeP-over-propline q0 q1 =
    invEq (PathPvsBridgeP (λ x i → P x) {a00 = p0} {a10 = p1} {a01 = p0} {a11 = p1} {left = refl} {right = refl} {down = q0} {up = q1})
    (hlp λ x i → isp x (q0 x) (q1 x) i)

    where
  
      hlp-left : refl ≡ (λ i → isp bi0 (q0 bi0) (q1 bi0) i)
      hlp-left = isOfHLevelPath {A = P bi0} 1 (isp bi0) p0 p0 refl (λ i → isp bi0 (q0 bi0) (q1 bi0) i)

      hlp-right : (λ i → isp bi1 (q0 bi1) (q1 bi1) i) ≡ refl
      hlp-right = isOfHLevelPath {A = P bi1} 1 (isp bi1) p1 p1 (λ i → isp bi1 (q0 bi1) (q1 bi1) i) refl

      hlp = change-line' (λ x → q0 x ≡ q1 x) (λ x → q0 x ≡ q1 x)
        (λ i → isp bi0 (q0 bi0) (q1 bi0) i) (λ i → isp bi1 (q0 bi1) (q1 bi1) i) refl refl
        (λ x e → e) (sym hlp-left) hlp-right


isSetBridgeP : ∀ {l} (A : Type l) → isSet A → ∀ (a0 a1 : A) → isSet (Bridge A a0 a1)
isSetBridgeP A sA a0 a1 q0 q1 =
  isOfHLevelRespectEquiv {A = BridgeP (λ x → q0 x ≡ q1 x) refl refl } 1 (invEquiv charac)
  (BridgeP-over-propline {P = λ x → q0 x ≡ q1 x}
  λ x → isOfHLevelPath' 1 sA (q0 x) (q1 x))

  where

    charac : (q0 ≡ q1) ≃ BridgeP (λ x → q0 x ≡ q1 x) refl refl 
    charac = PathPvsBridgeP (λ x i → A) {a00 = a0} {a10 = a1} {a01 = a0} {a11 = a1} {left = refl} {right = refl} {down = q0} {up = q1}
