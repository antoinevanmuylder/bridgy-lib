{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --type-in-type #-} -- --no-termination-check

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Bridgy.Core.GelExamples
open import Bridgy.Core.BridgePrims

module Bridgy.KAry
       (Arity : Set)
  where

  Tuple : Set → Set
  Tuple X = Arity → X

  Relation : Set -> Set₁
  Relation X = Tuple X → Set

  RTuple : {X : Set} (R : Relation X) → Set
  RTuple {X} R = Σ (Tuple X) R

  RTup-field : ∀ {X : Set} {R : Relation X} (i : Arity) (t : RTuple R) (v : X) → Set
  RTup-field n t v = fst t n ≡ v

  paramUnit : (f : ∀ (X : Set) → X → X) →
              (A : Set) (R : Relation A) →
              (x : Tuple A) → R x →
              R (λ n → f A (x n))
  paramUnit f A R x Rx = subst R fstfRx RfxRx
    where
      xRx : RTuple R
      xRx = x , Rx

      fxRx : RTuple R
      fxRx = f (RTuple R) xRx

      RfxRx : R (fst fxRx)
      RfxRx = snd fxRx

      Rxxi : ∀ i → RTup-field i xRx (x i)
      Rxxi i = refl

      B : (i : Arity) → (@tick r : BI) → Set
      B n = primGel (RTuple R) A (RTup-field n)

      fBi : (n : Arity) → BridgeP (B n) fxRx (f A (x n))
      fBi n r = f (B n r) (prim^gel {R = RTup-field n} xRx (x n) refl r)

      fstfRx : fst fxRx ≡ λ n → f A (x n)
      fstfRx i n = prim^ungel {R = RTup-field n} (λ r → fBi n r) i

