{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module SimpleParam where

open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import NativeReflGraphRelator
open import ParamNativeRelator
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.Transport


churchUnit : ∀ {ℓ} → ( (X : Type ℓ) → X → X )  ≃  ⊤
churchUnit = isoToEquiv (iso
                        (λ _ → tt)
                        (λ where _ → λ X x → x)
                        (λ where _ → refl)
                        -- church encdoding  is a retract of ⊤, by param
                        λ f → funExt λ A → funExt λ a → -- goal is ∀ (f : (X : Type ℓ) → X → X) A a, a ≡ f A a 
                          param churchUnitNRelator f (Lift ⊤) A (λ _ x → a ≡ x) _ a refl)


churchBool : ∀ {ℓ} → ( (X : Type ℓ) → X → X → X ) ≃ Bool
churchBool = isoToEquiv (iso
                        (λ f → (f (Lift Bool) (lift true) (lift false)) .lower)
                        bool→church
                        (λ where
                          true → refl
                          false → refl)
                        -- church encoding is a retract of Bool, by param
                        λ f → funExt λ A → funExt λ aTrue → funExt λ aFalse → -- goal is  bool→church (church→bool f) A aTrue aFalse ≡ f A aTrue aFalse
                          param churchBoolNRelator f (Lift Bool) A (λ where (lift b) a → bool→church b A aTrue aFalse ≡ a) (lift true) (aTrue) refl (lift false) aFalse refl)
  where
  bool→church = (λ where
                   true → λ X xtrue xfalse → xtrue
                   false → λ X xtrue xfalse → xfalse)
   
