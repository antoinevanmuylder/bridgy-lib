{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

-- open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Unit

-- relatedness under equivalences
module Bridgy.Core.EquGraph where

module _ {l : Level} {A0 A1 : Type l} where

  abstract

    _[_]_ : A0 → A0 ≃ A1 → A1 → Type l
    _[_]_ a0 e a1 = (equivFun e a0) ≡ a1

    -- e a0 ≡ a1 → a0 [e] a1
    inEquGr : ∀ {a0 : A0} {e : A0 ≃ A1} {a1 : A1} → 
      (equivFun e a0) ≡ a1 → (a0 [ e ] a1)
    inEquGr prf = prf

    -- a0 ≡ e^-1 a1 → a0 [e] a1
    inEquGrInv : ∀ {a0 : A0} {e : A0 ≃ A1} {a1 : A1} → 
      a0 ≡ (invEq e a1) → a0 [ e ] a1
    inEquGrInv {a0} {e} {a1} hyp = inEquGr {a0 = a0} {e = e} {a1 = a1} ((equivFun (equivAdjointEquiv e) hyp))

    outEquGr : ∀ {a0 : A0} {e : A0 ≃ A1} {a1 : A1} → 
      (a0 [ e ] a1) → (equivFun e a0) ≡ a1
    outEquGr prf = prf

    -- a0 [e] a1 → a0 ≡ e^-1 a1
    outEquGrInv : ∀ {a0 : A0} {e : A0 ≃ A1} {a1 : A1} → 
      (a0 [ e ] a1) → a0 ≡ invEq e a1
    outEquGrInv {e = e} aprf = invEq (equivAdjointEquiv e) aprf

    inOfOut : ∀ {a0 : A0} {e : A0 ≃ A1} {a1 : A1} → 
      (gprf : a0 [ e ] a1) → inEquGr (outEquGr gprf) ≡ gprf
    inOfOut gprf = refl



module _ {l} {A B C : Type l} where

  compGr : ∀ (e : A ≃ B) (f : B ≃ C) (a : A) (b : B) (c : C) → (a [ e ] b) → (b [ f ] c) → (a [ compEquiv e f ] c)
  compGr e f a b c he hf = inEquGr (cong (equivFun f) (outEquGr he) ∙ (outEquGr hf))
