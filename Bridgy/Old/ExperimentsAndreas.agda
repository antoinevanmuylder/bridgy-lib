{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.constr:60 -v tc.conv:50 -v tc.cover.iapply:40 -v tc.iapply:40 -v tc.conv.face:40 #-} -- 
module Cubical.Bridges.ExperimentsAndreas where

open import Cubical.Bridges.BridgePrims
open import Cubical.Foundations.Prelude

module _ {A : (@tick i : BI) → Type} {B : (@tick i : BI) → A i → Type} (f : (@tick i : BI) → (x : A i) → B i x) where
  extent-f : (@tick i : BI) → (x : A i) → B i x
  extent-f = primExtent (f bi0) (f bi1) λ a0 a1 a* i → f i (a* i)

  double-extent-f : (@tick i : BI) → (x : A i) → B i x
  double-extent-f = primExtent (f bi0) (f bi1) λ a0 a1 a* i → extent-f i (a* i)

  idempotent-extent-f : extent-f ≡ double-extent-f
  idempotent-extent-f = λ v i a → {!extent-f i a!}
  -- the constraints for this hole's endpoints do not normalize to the same thing, yet the goal is accepted!
