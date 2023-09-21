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
    inEquGr : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) → 
      (equivFun e a0) ≡ a1 → (a0 [ e ] a1)
    inEquGr a0 e a1 prf = prf

    -- a0 ≡ e^-1 a1 → a0 [e] a1
    inEquGrInv : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) →
      a0 ≡ (invEq e a1) → a0 [ e ] a1
    inEquGrInv a0 e a1 hyp = inEquGr a0 e a1 (equivFun (equivAdjointEquiv e) hyp)

    outEquGr : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) →
      (a0 [ e ] a1) → (equivFun e a0) ≡ a1
    outEquGr _ _ _ prf = prf

    -- a0 [e] a1 → a0 ≡ e^-1 a1
    outEquGrInv : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) →
      (a0 [ e ] a1) → a0 ≡ invEq e a1
    outEquGrInv a0 e a1 aprf = invEq (equivAdjointEquiv e) aprf



module _ {l} {A B C : Type l} where

  compGr : ∀ (e : A ≃ B) (f : B ≃ C) (a : A) (b : B) (c : C) → (a [ e ] b) → (b [ f ] c) → (a [ compEquiv e f ] c)
  compGr e f a b c he hf = inEquGr _ _ _ (cong (equivFun f) (outEquGr _ _ _ he) ∙ (outEquGr _ _ _ hf))
