{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.def.fun:40 -v tc.fun.def:40 -v tc.lhs.top:30 -v tc.lhs.split:40  -v tc.constr:30 -v tc.sys.cover:30 -v tc.conv.bdgfaces:50 -v tc.conv.substctx:50  -v conv.forall:20 #-}
module Bridgy.CstrExamples where



open import Agda.Builtin.Nat
open import Agda.Builtin.Unit -- renaming (Unit to ⊤)
open import Cubical.Foundations.Prelude
open import Bridgy.BridgePrims

module BCSTR (@tick x : BI) (@tick y : BI) where

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

module BPARTIAL {ℓ} (@tick x : BI) (@tick y : BI) (t : I) (A : Type ℓ) (a0 a1 : A) where

  -- try ommiting a clause: coverage check raises a legit error.
  -- coherence check should not pass at x=bi0, y=bi1
  -- because a0 != a1 computationally.
  -- foo : BPartial ((x =bi0) b∨ (y =bi1) b∨ (y =bi0)) A
  -- foo (y = bi1) = a1
  -- foo (x = bi0) = a0
  -- foo (y = bi0) = a0

  fun : BPartial ((x =bi0) b∨ (y =bi1) b∨ (y =bi0)) A
  fun (y = bi1) = a0
  fun (x = bi0) = a0
  fun (y = bi0) = a0  


module _ {ℓ} {B : Type ℓ}
         (b0 b1 : B) (q : BridgeP (λ _ → B) b0 b1)
         (@tick x : BI) (@tick y : BI) where 

  -- coherence check rightly fails here (besides the duplicated clause)
  -- foo2 : BPartial ((x =bi0) b∨ (y =bi0) b∨ (y =bi1)) B
  -- foo2 (x = bi0) = q y
  -- foo2 (y = bi1) = q x
  -- foo2 (y = bi0) = b0
  -- foo2 (y = bi0) = b1


-- checking eta at BPartial
module BPARTIALETA {ℓ} {B : Type ℓ} (b0 b1 : B) (@tick x : BI) (@tick y : BI) (i : I) where

  comp1 : BPartial byes B
  comp1 _ = b0

  comp2 : BPartial byes B
  comp2 _ = b1

  -- skeptic : BridgeP (λ _ → _) comp1 comp2
  -- skeptic = ?

  -- etachecking : Partial (i ∨ ~ i) (BPartial byes B)
  -- etachecking (i = i0) = comp1
  -- etachecking (i = i1) = comp2

module MCSTR (ℓ : Level) (A : Type ℓ) (@tick x : BI) (@tick y : BI) (z : I) where

  mSomething : CstrUniv --note: CstrUniv : univSort CstrUniv
  mSomething = MCstr

  ψyes : BCstr
  ψyes = bno b∨ bi0 =bi1 b∨ byes b∨ bno

  aψ : BCstr
  aψ = bno b∨ x =bi1 b∨ ( y =bi0 b∨ bno ) b∨ (bi0 =bi1 b∨ bi1 =bi0)

  aφ : I
  aφ = ~ z

  ζ : MCstr
  ζ = aφ m∨ aψ

  ζyes : MCstr
  ζyes = i1 m∨ aψ

  ζyes' : MCstr
  ζyes' = aφ m∨ ψyes

  ζno : MCstr
  ζno = i0 m∨ (bi0 =bi1)

  -- a bdg depending on a mixed constraint mentionning x
  smBdg : MPartial (i0 m∨ x =bi0)  (BridgeP (λ _ → ⊤) tt tt)
  smBdg = λ prf z → tt

  -- applyX : MHolds (i0 m∨ x =bi0) → ⊤
  -- applyX prf = smBdg prf x

  mpart1 : MPartial myes A
  mpart1 = {!!}

  mpart2 : MPartial mno A
  mpart2 = {!!}

  mpart3 : MPartial ζ A
  mpart3 = {!!}

