{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims.agda and-or Agda.Primitive.Cubical

open import Cubical.Core.Everything public

module Prims where
  primitive
    primLockUniv : Type₁
open Prims renaming (primLockUniv to LockU)


------------------------------------------------------------------------
-- CH primitives for internal parametricity
------------------------------------------------------------------------

{-# BUILTIN BRIDGEINTERVAL BI  #-}  -- BI : LockU

{-# BUILTIN BIZERO    bi0 #-}       -- bi0, bi1 : BI
{-# BUILTIN BIONE     bi1 #-}


-- heterogenous bridges over line A.
postulate
  BridgeP : ∀ {ℓ} (A : (@tick x : BI) → Type ℓ) → A bi0 → A bi1 → Type ℓ

{-# BUILTIN BRIDGEP        BridgeP     #-}

-- NN = pointwise relatedness of N0 N1
primitive
  primExtent : ∀ {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
               (N0 : (a0 : A bi0) → B bi0 a0)
               (N1 : (a1 : A bi1) → B bi1 a1)
               (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1))
               (@tick r : BI) (M : A r) →
               B r M


primitive
  primGel : ∀ {ℓ} (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) (@tick r : BI) → Type ℓ


-- caution: R is implicit but can not be inferred from the following args
primitive
  prim^gel : ∀ {ℓ} {A0 A1 : Type ℓ} {R : A0 → A1 → Type ℓ}
               (M0 : A0) (M1 : A1) (P : R M0 M1) (@tick r : BI) →
               primGel A0 A1 R r


primitive
  prim^ungel : ∀ {ℓ} {A0 A1 : Type ℓ} {R : A0 → A1 → Type ℓ}
               (absQ : (@tick x : BI) → primGel A0 A1 R x) →
               R (absQ bi0) (absQ bi1)



{-# BUILTIN CSTRUNIV CstrUniv #-} -- CstrUniv : UnivSort _

postulate
  BCstr : CstrUniv

{-# BUILTIN BCSTR BCstr #-}



module BCstrPrims where
  primitive
    primBno : BCstr
    primByes : BCstr
    primBisone : BI → BCstr
    primBiszero : BI → BCstr
    primBconj : BCstr → BCstr → BCstr
open BCstrPrims public
  renaming ( primBno         to bno
           ; primByes        to byes
           ; primBisone      to _=bi1
           ; primBiszero     to _=bi0
           ; primBconj       to infixl 19 _b∨_ )


{-# BUILTIN BHOLDS BHolds #-} -- BHolds : BCstr → Setω. similar to IsOne

postulate
  BitHolds : BHolds byes

{-# BUILTIN BITHOLDS BitHolds #-} -- similar to itIsOne.


-- BPartial : ∀{ℓ} (ψ : BCstr) (A : Set ℓ) → Set ℓ
-- BPartial ψ A = BHolds ψ → A
-- and reduces to .(BHolds ψ) → A
{-# BUILTIN BPARTIAL  BPartial  #-} -- wonder if SSet ℓ as tgt (instead of SSet 0) is useful.

