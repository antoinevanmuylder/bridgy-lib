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


-- We have to prove
-- (1) hSet ℓ → hSet ℓ is a native reflexive graph
--     To that end, sufficient to prove that hSet ℓ is a nRG
-- (2) HasMonad : M ↦ Type (ℓ-suc ℓ) is a native relator
--
-- then Monad := Σ (hSet ℓ → hSet ℓ) HasMonad


record HasMonad {ℓ : Level} (M : hSet ℓ → hSet ℓ) : Type (ℓ-suc ℓ) where



