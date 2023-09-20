{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Examples.Church where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Foundations.Function

------------------------------------------------------------------------
-- encoding of 1

-- X:Type ⊨ ElX → ElX dNRG
churchUnitDNRG : ∀ (l : Level) → DispNRG l (TypeNRG l)
churchUnitDNRG l = →Form l l X⊨ElX X⊨ElX

churchUnit : ∀ {l} → Unit ≃ ( ∀ (X : Type l) → X → X )
churchUnit {l} = isoToEquiv (iso
  (λ _ X x → x)
  (λ _ → tt)
  (λ ch → funExt λ X → funExt λ x →
    param (TypeNRG l) (churchUnitDNRG l) ch (Lift Unit) X (λ (lift tt) y → x ≡ y ) (lift tt) x refl)
  λ tt → refl)

-- X:Type ⊨ ElX → (ElX → ElX) dNRG
churchBoolDNRG : ∀ (l : Level) → DispNRG l (TypeNRG l)
churchBoolDNRG l = →Form l l (X⊨ElX) (→Form l l X⊨ElX X⊨ElX)

churchBool : ∀ {l} → Bool ≃ ( ∀ (X : Type l) → X → X → X )
churchBool {l} = isoToEquiv (iso
  boolToCh
  chToBool
  (λ ch → funExt λ A → funExt λ at → funExt λ af →
    param (TypeNRG l) (churchBoolDNRG l) ch (Lift Bool) A (λ lb a → boolToCh (lb .lower) A at af ≡ a) (lift true) at refl (lift false) af refl)
  λ { false → refl ;
       true → refl })
  where
    boolToCh : ∀ {l} → Bool → ( ∀ (X : Type l) → X → X → X )
    boolToCh true X xt xf = xt
    boolToCh false X xt xf = xf

    chToBool : ∀ {l} → ( ∀ (X : Type l) → X → X → X ) → Bool
    chToBool ch = ch (Lift Bool) (lift true) (lift false) .lower

-- X:Type ⊨ ElX → ((ElA → ElX→ ElX) → ElX)
-- where A is a bridge discrete type
churchListDNRG : ∀ (l : Level) → (A : Type l) → (isbA : isBDisc A) → DispNRG l (TypeNRG l)
churchListDNRG l A isbA =
  →Form l l (X⊨ElX)
  (flip (→Form l l) (X⊨ElX)
  (→Form l l
  (bDisc-asDNRG A isbA)
  (→Form l l (X⊨ElX) (X⊨ElX) )))






