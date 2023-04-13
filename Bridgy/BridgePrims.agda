{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module Bridgy.BridgePrims where

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

{-# BUILTIN BCSTR BCstr #-} -- BCstr : CstrUniv



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



-- BPartial : ∀{ℓ} (ψ : BCstr) (A : Set ℓ) → SSet ℓ
-- BPartial ψ A = BHolds ψ → A
-- and reduces to .(BHolds ψ) → A
{-# BUILTIN BPARTIAL  BPartial  #-} -- wonder if SSet ℓ as tgt (instead of SSet 0) is useful.


{-# BUILTIN MCSTR MCstr #-} -- MCstr : CstrUniv
module MCstrPrims where
  primitive
    primMno : MCstr
    primMyes : MCstr
    primMkmc : I → BCstr → MCstr
open MCstrPrims public
  renaming ( primMno    to mno
           ; primMyes   to myes
           ; primMkmc   to infixl 18 _m∨_ )
{-# BUILTIN MHOLDS MHolds #-} -- MHolds : MCstr → SSet ℓ-zero
postulate
  MitHolds : MHolds myes
{-# BUILTIN MITHOLDS MitHolds #-}
{-# BUILTIN MPARTIAL MPartial #-} -- MPartial : ∀{ℓ} (ζ : MCstr) (A : Set ℓ) → SSet ℓ ; MPartial ζ A = MHolds ζ → A ; and reduces to .(MHolds ζ) → A
-- auxiliary builtins/prims for mixed hocom
-- builtinEmbd, builtinMixedOr, builtinMPartialP, builtinMHoldsEmpty, builtinMHolds1, builtinMHolds2, builtinMPOr
module AuxMhocom0 where
  primitive
    primReflectMCstr : ∀ {φ : I} -> .(MHolds (φ m∨ bno)) -> IsOne φ
    primPrsvMCstr : ∀ {φ : I} → .(IsOne φ) → MHolds (φ m∨ bno)
    primEmbd : I → MCstr
    primMixedOr : MCstr → MCstr → MCstr
open AuxMhocom0 public
  renaming ( primMixedOr to infixl 17 _∨∨_ 
           ; primEmbd to embdI
           ; primPrsvMCstr to embdI⋆ --push fwd ( \* )
           ; primReflectMCstr to embdI*) --pull back
{-# BUILTIN MPARTIALP MPartialP #-}
postulate
  mholdsEmpty : ∀ {ℓ} {A : MPartial mno (Set ℓ)} → MPartialP mno A
  MHolds1 : ∀ ζ1 ζ2 → .(MHolds ζ1) → MHolds (ζ1 ∨∨ ζ2)
  MHolds2 : ∀ ζ1 ζ2 → .(MHolds ζ2) → MHolds (ζ1 ∨∨ ζ2)
{-# BUILTIN MHOLDSEMPTY mholdsEmpty #-}
{-# BUILTIN MHOLDS1 MHolds1 #-}
{-# BUILTIN MHOLDS2 MHolds2 #-}
primitive
  prim^mpor : ∀ {ℓ} ζ1 ζ2 → {A : MPartial (ζ1 ∨∨ ζ2) (Type ℓ)} →
               (u : MPartialP ζ1 (λ o1 → A (MHolds1 ζ1 ζ2 o1)))
               (v : MPartialP ζ2 (λ o2 → A (MHolds2 ζ1 ζ2 o2)))
               → MPartialP (ζ1 ∨∨ ζ2) A
module MixedKan where
  primitive
    primMHComp : ∀ {ℓ} {A : Type ℓ} {ζ : MCstr} (u : ∀ i → MPartial ζ A) (u0 : A) → A
open MixedKan public
  renaming ( primMHComp to mhocom )
module AllMCstr where
  primitive
    primAllMCstr : ((@tick x : BI) → MCstr) → MCstr
    primAllMCstrCounit : {absζ : ((@tick x : BI) → MCstr)} → .(oall : MHolds (primAllMCstr absζ)) → (@tick x : BI) → MHolds (absζ x)
open AllMCstr public
  renaming ( primAllMCstr to ∀-mcstr
           ; primAllMCstrCounit to ∀-mcstr-ε )
primitive
  primRefoldMhocom : ∀ {ℓ} {T : Type ℓ} → T → T

