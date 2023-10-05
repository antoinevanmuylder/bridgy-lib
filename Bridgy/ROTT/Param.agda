{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module Bridgy.ROTT.Param where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Bridgy.Core.MyPathToEquiv






-- The following is the param theorem stated for dNRGs.
-- it says that "dependent functions preserve logical relations"
module ParamDNRG {l l' : Level} (Γ : NRGraph l) (A : DispNRG l' Γ) where

  -- Γ NRG    Γ ⊨ A dNRG   f:∀ g → A g    g0,g1:Γ   gg:Γ ⦅ g0 , g1 ⦆
  -- ----------------------------------------------------------------
  -- param Γ A f g0 g1 gg : A ⦅ f g0 , f g1 ⦆# gg
  param : (f : ∀ g → A .dcr g) (g0 g1 : Γ .nrg-cr)
    (gg : Γ ⦅ g0 , g1 ⦆ ) → A ⦅ f g0 , f g1 ⦆# gg
  param f g0 g1 gg =
    let
      fwd = equivFun (Γ .nativ g0 g1)
      bwd = invEq (A .dnativ g0 g1 gg (fwd gg) (inEquGr refl) (f g0) (f g1))
    in
      bwd λ x → f ( fwd gg x )

open ParamDNRG public


-- -- A similar param theorem but formulated using native relators instead.
-- -- Contrary to the one above, this one requires the existence of a universe TypeNRG
-- module ParamNRel {ℓ ℓ'} {G : NRGraph ℓ}
--                         (F : NRelator G (TypeNRG ℓ')) where

--   -- idea!
--   -- goal is fa [Fr] fb in Type.
--   -- apply ~relativity (relation witnesses are ≃ bridges). goal is Bdg (Gel Fa Fb Fr) fa fb
--   -- because F is native we can *change the above line* Gel Fa Fb Fr into
--   -- (λ x → F (I-tobdg-r x)) where I-tobdg-r is (r:I{a,b}) ↦ Bdg (_.I) a b
--   -- goal is now Bdg (λ x → F (I-tobdg-r x)) fa fb. Can "bridge apply" f and provide I-tobdg-r
--   paramNRel : ∀ (f : (x : I .nrg-cr) → F .nobjMap x) →
--     (a b : I .nrg-cr) (r : I .nedge a b) → F .nedgeMap r (f a) (f b)
--   paramNRel f a b r = bdg-over-gel (F .nedgeMap r) (f a) (f b) .fst
--     (change-line' (λ x → F .nobjMap (I. nativ a b .fst r x))
--                   (primGel (F .nobjMap a) (F .nobjMap b) (F .nedgeMap r))
--                   (f a) (f b) (f a) (f b)
--                   (λ x w → transport (λ i → (switchNativeRelSqu _ _ F a b) i r x) w) (transportRefl _) (transportRefl _)
--                   λ x → f (I .nativ a b .fst r x))
-- open ParamNRel public







-- JUNK


    -- where
      -- adjust-base-lrel : {l l' : Level} (G : NRGraph l) (A : DispNRG l' G)
      --   (g0 g1 : G .nrg-cr) (a0 : A .dcr g0) (a1 : A .dcr g1) (gg : G ⦅ g0 , g1 ⦆ )  →
      --   (A ⦅ a0 , a1 ⦆# gg) ≃ (A ⦅ a0 , a1 ⦆# (invEq (G .nativ g0 g1) (equivFun (G .nativ g0 g1) gg)))
      -- adjust-base-lrel G A g0 g1 a0 a1 gg =
      --   mypathToEquiv λ i → A ⦅ a0 , a1 ⦆# (sym (retEq (G .nativ g0 g1) gg) i)
