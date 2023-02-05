{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module Bridgy.SimpleParam where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Bridgy.NativeReflGraphRelator
open import Bridgy.ParamNativeRelator
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.List


churchUnit : ∀ {ℓ} → ( (X : Type ℓ) → X → X )  ≃  ⊤
churchUnit = isoToEquiv (iso
                        (λ _ → tt)
                        (λ where _ → λ X x → x)
                        (λ where _ → refl)
                        -- church encoding  is a retract of ⊤, by param
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



-- churchList : ∀ {ℓ} (A : Type ℓ) → ( (X : Type ℓ) → X → (A → X → X) → X ) ≃ List A
-- churchList {ℓ} A = isoToEquiv (iso
--                  churchToList
--                  listToChurch
--                  sameList
--                  -- this retract proof must use param.
--                  λ chl → funExt λ X → funExt λ d → funExt λ f → {!!})

--   where

--     churchToList : ( (X : Type ℓ) → X → (A → X → X) → X ) → List A
--     churchToList = (λ f → f (List A) [] _∷_)

--     listToChurch : List A → ( (X : Type ℓ) → X → (A → X → X) → X )
--     listToChurch [] = λ X d f → d
--     listToChurch (a ∷ as) = λ X d f → f a (listToChurch as X d f)

--     sameList : ∀ as → churchToList (listToChurch as) ≡ as
--     sameList [] = refl
--     sameList (a ∷ as) = ListPath.decode _ _
--       (refl ,
--       ListPath.encode (churchToList (listToChurch as)) as
--       (sameList as))
   
