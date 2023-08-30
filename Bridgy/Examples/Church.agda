{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Examples.Church where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

------------------------------------------------------------------------
-- encoding of 1

churchUnitDNRG : ∀ (l : Level) → DispNRG l (TypeNRG l)
churchUnitDNRG l = →Form l X⊨ElX l X⊨ElX
  where
    X⊨ElX : ∀ {l : Level} → DispNRG l (TypeNRG l)
    X⊨ElX {l} = El (record {
      tm0 = λ X → X ;
      tm1 = λ X0 X1 XX → XX ;
      tm-nativ = λ X0 X1 XX Xbdg Xprf → Xprf})


churchUnit : ∀ {l} → Unit ≃ ( ∀ (X : Type l) → X → X )
churchUnit {l} = isoToEquiv (iso
  (λ _ X x → x)
  (λ _ → tt)
  (λ ch → funExt λ X → funExt λ x →
    param (TypeNRG l) (churchUnitDNRG l) ch (Lift Unit) X (λ (lift tt) y → x ≡ y ) (lift tt) x refl)
  λ tt → refl)
