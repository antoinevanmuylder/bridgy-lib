{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module Bridgy.ExtentExamples where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism


------------------------------------------------------------------------
-- extent primitive
------------------------------------------------------------------------


module PlayExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
                  (N0 : (a0 : A bi0) → B bi0 a0) (N1 : (a1 : A bi1) → B bi1 a1) where
  
  -- we wish to show bridge-funext: an equivalence btw the two foll. types
  -- pointwise will be a retract thanks to extent beta rule
  pointwise = (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)

  -- related will be a retract thanks to extent eta rule
  related = BridgeP (λ x → (a : A x) → B x a) N0 N1

  -- bridge-funext, hard direction
  bf-hard : pointwise → related
  bf-hard NN = λ r M → primExtent N0 N1 NN r M


  bf-easy : related -> pointwise
  bf-easy p = λ a0 a1 aa x → p x (aa x)


  pointwise-retract : (H : pointwise) -> H ≡ bf-easy (bf-hard H)
  pointwise-retract H i = H

  -- uses "casing by extent" proof technique.
  -- when proving that a fully applied bridge equals extent `q x ≡ primExtent ...`
  -- one can use extent itself!
  related-retract : (q : related) -> q ≡ bf-hard ( bf-easy q )
  related-retract q = bridgePPath λ x → funExt λ a → primExtent {B = λ x a → q x a ≡ primExtent N0 N1 (λ c0 c1 cc y → q y (cc y)) x a}
                                                       (λ a0 → refl) (λ a1 → refl) (λ a0 a1 aa y → refl) x a

open PlayExtent public


module ΠBridgeP {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
                  {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1} where


  ΠBridgeP : ( (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1) ) →
             BridgeP (λ x → (a : A x) → B x a) N0 N1
  ΠBridgeP NN = λ r M → primExtent N0 N1 NN r M

  ΠvsBridgeP : ( (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1) )
               ≃
               BridgeP (λ x → (a : A x) → B x a) N0 N1
  ΠvsBridgeP = isoToEquiv (iso ΠBridgeP
                               (bf-easy N0 N1)
                               (λ q → sym (related-retract N0 N1 q))
                               λ H → sym (pointwise-retract {B = B} N0 N1 H))
open ΠBridgeP public


module BetaExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
               {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1}
               {NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)}
               {M' : (@tick j : BI) → A j} {@tick r : BI} where


  extent-beta : primExtent {A = A} {B = B} N0 N1 NN r (M' r) ≡ NN (M' bi0) (M' bi1) (λ j → M' j) r
  extent-beta = refl
  
  -- try C-c C-n this. extent fails to reduce because of issue #2
  -- the semi freshness check r ∉ M' r fails but it should pass.
  -- when issue #2 is solved this should work
  extent-beta' : B r (M' r)
  extent-beta' = primExtent {A = A} {B = B} N0 N1 NN r (M' r)


  

module NotSemiFreshExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
               {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1}
               {NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)}
               {@tick r : BI} {b : Bool} {M' : Bool → A r} where

  -- try C-c C-n this
  -- this one should indded not reduce because r is not semifresh for M' b since M' b contains
  -- b which is a timefull r-later.
  -- However the reason why it does not reduce here is issue #2: r itself is wronlgy 
  -- considered a timefull r-later
  -- When issue #2 gets fixed, this will still not reduce, as expected 
  not-sfresh-M : B r (M' b)
  not-sfresh-M = primExtent {A = A} {B = B} N0 N1 NN r (M' b)
