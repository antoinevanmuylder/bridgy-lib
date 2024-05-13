{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Experimental.VecChurch where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Bridgy.Core.BDisc

module _ {l : Level} (A : Type l) (isbA : isBDisc A) where

  -- being a model of the theory of vectors.
  -- see signature of Vec.
  Vecp : (ℕ → Type l) → Type l
  Vecp V = V 0 × (∀ n → A → V n → V (suc n))

  ModTVec = Σ (ℕ → Type l) Vecp

  nilOf : (M : ModTVec) → M .fst 0
  nilOf M = M .snd .fst

  consOf : (M : ModTVec) → (∀ n → A → M .fst n → M .fst (suc n))
  consOf M = M .snd .snd

  -- from syntax to semantics. Note the indexing.
  toSem : ∀ n → Vec A n → ((M : ModTVec) → M .fst n)
  toSem 0 nil M = nilOf M
  toSem (suc n) (a ∷ as)  M = consOf M n a (toSem n as M)

  -- from semantics to syntax. need to register Vec as a model
  VecAsMod : ModTVec
  VecAsMod = Vec A , [] , λ n → _∷_  

  toSyn : ∀ n → ((M : ModTVec) → M .fst n) → Vec A n
  toSyn n op = op VecAsMod

  -- syntax <= semantics
  syn<=sem : ∀ n (v : Vec A n) → toSyn n (toSem n v) ≡ v
  syn<=sem 0 [] = refl
  syn<=sem (suc n) (a ∷ as) = cong (_∷_ a) (syn<=sem n as)

  -- sem <= syntax. need parametricity.
  sem<=syn : ∀ n (op : (M : ModTVec) → M .fst n) → toSem n (toSyn n op) ≡ op
  sem<=syn 0 op = funExt λ M → {!!}
  

  

