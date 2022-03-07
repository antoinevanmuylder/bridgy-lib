{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module ParamNativeRelator where

open import BridgePrims
open import BridgeExamples
open import NativeReflGraphRelator
open import GelExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Agda.Builtin.Unit


-- param ≈says all nonvariant native diagrams F : I → Type ℓ
-- have parametric limits, given by Pi types. Here we just
-- prove that the pi types are parametric cones (sufficient for free thms)
module ParamNRel {ℓ ℓ'} {I : Type ℓ} ⦃ hnrgI : HasNRGraph I ⦄
                     (F : NRelator I (Type ℓ')) where

  -- idea!
  -- goal is fa [Fr] fb in Type.
  -- apply ~relativity (relation witnesses are ≃ bridges). goal is Bdg (Gel Fa Fb Fr) fa fb
  -- because F is native we can *change the above line* Gel Fa Fb Fr into
  -- (λ x → F (I-tobdg-r x)) where I-tobdg-r is (r:I{a,b}) ↦ Bdg (_.I) a b
  -- goal is now Bdg (λ x → F (I-tobdg-r x)) fa fb. Can "bridge apply" f and provide I-tobdg-r
  param : ∀ (f : (x : I) → F .nobjMap x) →
    (a b : I) (r : nedge a b) → F .nedgeMap r (f a) (f b)
  param f a b r = bdg-over-gel (F .nedgeMap r) (f a) (f b) .fst
                  (change-line' (λ x → F .nobjMap (nativ a b .fst r x)) (primGel (F .nobjMap a) (F .nobjMap b) (F .nedgeMap r))
                    (f a) (f b) (f a) (f b)
                    (λ x w → transport (λ i → (switchNativeRelSqu _ _ F a b) i r x) w) (transportRefl _) (transportRefl _)
                  λ x → f (nativ a b .fst r x))
open ParamNRel public

