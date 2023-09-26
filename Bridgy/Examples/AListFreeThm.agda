------------------------------------------------------------------------
-- We show a standard free theorem for polymorphic programs
-- p : List X → List X → List X
------------------------------------------------------------------------

{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.AListFreeThm where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.List
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.Rules
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty


X⊨ListX→ListX→ListX : ∀ {l} → DispNRG l (TypeNRG l)
X⊨ListX→ListX→ListX {l} = →Form l l ListdNRG (→Form l l ListdNRG ListdNRG)


fthm : ∀ {l} (p : ∀ X → List X → List X → List X) (A0 A1 : Type l) (xs ys : List A0) (f : A0 → A1) →
  map f (p _ xs ys) ≡ p _ (map f xs) (map f ys)
fthm {l} p A0 A1 xs ys f =
  graph-lemma _ _
  auxparam

  where

    param-obl : ∀ as0  → ListdNRG ⦅ as0 , map f as0 ⦆# (λ a0 a1 → f a0 ≡ a1)
    param-obl [] = lift tt
    param-obl (hd ∷ tl) = refl , param-obl tl

    auxparam =
      param (TypeNRG l) X⊨ListX→ListX→ListX p A0 A1 (λ a0 a1 → f a0 ≡ a1)
      xs (map f xs) (param-obl xs)
      ys (map f ys) (param-obl ys)

    graph-lemma : ∀ alist blist → [List (λ a0 a1 → f a0 ≡ a1)] alist blist → map f alist ≡ blist
    graph-lemma [] [] = λ _ → refl
    graph-lemma (hd0 ∷ tl0) [] hyp = rec (hyp .lower)
    graph-lemma [] (hd1 ∷ tl1) hyp = rec (hyp .lower)
    graph-lemma (hd0 ∷ tl0) (hd1 ∷ tl1) (hdd , tll) = λ i → (hdd i) ∷ (graph-lemma tl0 tl1 tll i)
