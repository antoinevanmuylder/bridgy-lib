{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

{-
  This file defines a type of monads on Type with squashed equations
  This is is presumably not well behaved according to Amy Liao
-}

module Bridgy.MonadType where

open import Bridgy.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation.Base
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Data.Sigma using (_×_)
-- open import Agda.Builtin.Unit

record HasPreMonad {ℓ : Level} (M : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    ret : {X : Type ℓ} → X → M X
    dnib : {X Y : Type ℓ} → (X → M Y) → M X → M Y
open HasPreMonad ⦃ ... ⦄ public

record HasMonadEqs {ℓ : Level} (M : Type ℓ → Type ℓ) ⦃ hpmndM : HasPreMonad M ⦄ : Type (ℓ-suc ℓ) where
  field
    ret-then-fun : {X Y : Type ℓ} (f : X → M Y) → ∥ (dnib f) ∘ ret ≡ f ∥
    fun-then-ret : {X Y : Type ℓ} (f : X → M Y) → ∥ (dnib ret) ∘ f ≡ f ∥
    assoc-mnd : {X Y Z : Type ℓ} (xx : M X) (f : X → M Y) (g : Y → M Z) →
       ∥ dnib (λ x → dnib g (f x)) xx  ≡ dnib g (dnib f xx) ∥
open HasMonadEqs ⦃ ... ⦄ 

-- smart-packed monad
record Monad {ℓ : Level} : Type (ℓ-suc ℓ) where
  constructor mkMonad
  field
    mnd-cr : Type ℓ → Type ℓ
    ⦃ has-pmnd ⦄ : HasPreMonad mnd-cr
    ⦃ has-eqs ⦄ : HasMonadEqs mnd-cr
open Monad public

-- record HasMndEqs
  
