{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.MoreRules where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.CubicalLemmas
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.Core.List
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.List hiding ( [_] )

-- temp file for writing new ROTT rules

-- app rule
-- Γ ⊨ f : A → B      Γ ⊨ a : A
-- -------------------------------
-- Γ ⊨ f a : B
app : ∀ {l lA lB} →
  (Γ : NRGraph l) (A : DispNRG lA Γ) (B : DispNRG lB Γ) 
  (f : TermDNRG Γ (→Form _ _ A B))
  (a : TermDNRG Γ A) →
  TermDNRG Γ B
app Γ A B f a =
  record {
    tm0 = λ g → f .tm0 g (a .tm0 g) ;
    tm1 = λ g0 g1 gg →  f .tm1 g0 g1 gg (a .tm0 g0) (a .tm0 g1) (a .tm1 g0 g1 gg) ;
    tm-nativ = λ g0 g1 gg gbdg gprf →
      {!!}
  }

