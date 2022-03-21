{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.def.fun:10 -v tc.lhs.top:30 -v tc.lhs.split:40  -v tc.constr:30 #-}
module BCstrExamples where

open import BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)


-- ψ : BCstr
-- ψ = bno b∨ ( (bi0 =bi1) b∨ (byes b∨ bno) )

-- ψ2 : BCstr
-- ψ2 = (bno b∨ bno) b∨ byes

-- indeed : BHolds ψ
-- indeed = BitHolds

-- module BPartialBehaviour {ℓ} (ψ : BCstr) (A : Type ℓ) where

--   test : BCstr
--   test = {!BPartial ψ A!} --C-c C-n this




module TestMatch {ℓ} (x : BI) (y : BI) (A : Type ℓ) (a0 a1 : A) where

  foo : BPartial ((x =bi0) b∨ (y =bi1)) A
  foo (x = bi0) = a0


-- module TestMatchCub {ℓ} (x : I) (y : I) (A : Type ℓ) (a0 a1 : A) where

--   postulate
--     p : PathP (λ _ → Type) ℕ ℕ

--   foo : Partial (x ∨ ~ x) ((p x) → ⊤)
--   foo (x = i1) n = tt
--   foo (x = i0) n = tt


--   bar : Partial (i0) A
--   bar (i0 = i1) = a1

