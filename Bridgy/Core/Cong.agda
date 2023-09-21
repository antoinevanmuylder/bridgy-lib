------------------------------------------------------------------------
-- When are 2 sigma/pi types equivalent?
------------------------------------------------------------------------
{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.Cong where

open import Bridgy.Core.EquGraph
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

module _ {lA lB : Level} (A A' : Type lA) (B : A → Type lB) (B' : A' → Type lB) where


  -- Σ-cong-equiv : (e : A ≃ A')
  --              → ((x : A) → B x ≃ B' (equivFun e x))
  --              → Σ A B ≃ Σ A' B'
  -- Σ-cong-equiv e e' = isoToEquiv (Σ-cong-iso (equivToIso e) (equivToIso ∘ e'))

  -- a 2-ary version of the above
  Σ-cong-equiv-2ary : (eA : A ≃ A') →
    ((a : A) (a' : A') (aprf : a [ eA ] a') → B a ≃ B' a') →
    Σ A B ≃ Σ A' B'
  Σ-cong-equiv-2ary eA ptEqu =
    Σ-cong-equiv eA λ a →
    ptEqu a (equivFun eA a) (inEquGr _ _ _ refl) 
