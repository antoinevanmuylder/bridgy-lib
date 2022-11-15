{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

{-
  This file defines a type of monads on Type with squashed equations
  This is is presumably not well behaved according to Amy Liao
-}

module Bridgy.Monad where

open import Bridgy.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Foundations.HLevels


-- if F : A → Type is a native relator then Σ A F is a native relator as well?


record HasMonad {ℓ : Level} (M : hSet ℓ → hSet ℓ) : Type (ℓ-suc ℓ) where

