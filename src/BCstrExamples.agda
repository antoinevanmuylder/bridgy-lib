{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.def.fun:40 -v tc.fun.def:40 -v tc.lhs.top:30 -v tc.lhs.split:40  -v tc.constr:30 -v tc.sys.cover:30 #-}
module BCstrExamples where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit -- renaming (Unit to ⊤)
open import Cubical.Foundations.Prelude
open import BridgePrims

module _ (@tick x : BI) (@tick y : BI) where

  something : CstrUniv --note: CstrUniv : univSort CstrUniv
  something = BCstr

  ψ1 : BCstr
  ψ1 = bno b∨ bi0 =bi1 b∨ byes b∨ bno

  ψ2 : BCstr
  ψ2 = bno b∨ x =bi1 b∨ ( y =bi0 b∨ bno ) b∨ (bi0 =bi1 b∨ bi1 =bi0)

  indeed : BHolds ψ1
  indeed = BitHolds

  ψx : BCstr
  ψx = (x =bi0)

  -- a bridge depending on a cstr mentioning x
  smBdg : BPartial ψx (BridgeP (λ _ → ⊤) tt tt)
  smBdg = λ prf z → tt

  -- we can not apply x to this bridge
  -- applyX : (BHolds ψx) → ⊤
  -- applyX prf = {!smth prf x!}

module _ {ℓ} (@tick x : BI) (@tick y : BI) (t : I) (A : Type ℓ) (a0 a1 : A) where

  -- try ommiting a clause: coverage check raises a legit error.
  -- coherence check should not pass at x=bi0, y=bi1 though
  -- because a0 != a1 computationally.
  foo : BPartial ((x =bi0) b∨ (y =bi1) b∨ (y =bi0)) A
  foo (y = bi1) = a1
  foo (x = bi0) = a0
  foo (y = bi0) = a0

module _ {ℓ} {B : Type ℓ}
         (b0 b1 : B) (q : BridgeP (λ _ → B) b0 b1)
         (@tick x : BI) (@tick y : BI) where 

  foo2 : BPartial ((x =bi0) b∨ (y =bi0) b∨ (y =bi1)) B
  foo2 (x = bi0) = q y
  foo2 (y = bi1) = b0
  foo2 (y = bi0) = b0
  foo2 (y = bi0) = b1


  -- foo2 : BPartial ((x =bi0) b∨ (y =bi1) b∨ (y =bi0) b∨ bi1 =bi1) A
  -- foo2 (y = bi1) = a1
  -- foo2 (x = bi0) = a0
  -- foo2 (y = bi0) = a0
  -- -- foo2 (bi1 = bi1) = a0

  -- fee : BPartial bno A
  -- fee _ = a0






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

