{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.def.fun:40 -v tc.fun.def:40 -v tc.lhs.top:30 -v tc.lhs.split:40  -v tc.constr:30 -v tc.sys.cover:30 #-}
module BCstrExamples where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit -- renaming (Unit to ⊤)
open import Cubical.Foundations.Prelude
open import BridgePrims




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

  foo : BPartial ((x =bi0) b∨ ((y =bi1) b∨ (y =bi0))) A
  foo (y = bi1) = a1
  foo (y = i0) = a0
  foo (x = bi0) = a0

  fee : BPartial bno A
  fee _ = a0





-- module TestMatchCub {ℓ} (x : I) (y : I) (A : Type ℓ) (a0 a1 : A) where

--   foo : Partial (~ x ∨ y) A
--   foo (x = i0)          = a0
--   foo (y = i1)          = a0

--   postulate
--     p : PathP (λ _ → Type) ℕ ℕ

--   foo : Partial (x ∨ ~ x) ((p x) → ⊤)
--   foo (x = i1) n = tt
--   foo (x = i0) n = tt


--   bar : Partial (i0) A
--   bar (i0 = i1) = a1

