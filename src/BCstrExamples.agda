{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.def.fun:10 -v tc.lhs.top:30 -v tc.lhs.split:30  #-}
module BCstrExamples where

open import BridgePrims
open import Cubical.Foundations.Prelude



-- ψ : BCstr
-- ψ = bno b∨ ( (bi0 =bi1) b∨ (byes b∨ bno) )

-- ψ2 : BCstr
-- ψ2 = (bno b∨ bno) b∨ byes

-- indeed : BHolds ψ
-- indeed = BitHolds

-- module BPartialBehaviour {ℓ} (ψ : BCstr) (A : Type ℓ) where

--   test : BCstr
--   test = {!BPartial ψ A!} --C-c C-n this




-- module TestMatch {ℓ} (x : BI) (y : BI) (A : Type ℓ) (a0 a1 : A) where

--   foo : BPartial ((x =bi0) b∨ (y =bi0)) A
--   foo (x = bi0) = a0


module TestMatchCub {ℓ} (x : I) (y : I) (A : Type ℓ) (a0 a1 : A) where

  foo : Partial (x ∨ y) A
  foo (x = i1) = a0
  foo (y = i1) = a1
