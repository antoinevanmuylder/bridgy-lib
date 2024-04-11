{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.MoreVarRules where


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
open import Cubical.Foundations.Path
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.List hiding ( [_] )


-- last last last variable.
-- Γ NRG
-- Γ ⊨ A dNRG
-- (Γ # A) ⊨ B dNRG
-- Γ # A # B ⊨ C dNRG
-- -------------------------------------
-- Γ , (a : A) , (b : B), (c : C) ⊨ a : A
var2 : ∀ {l lA lB lC} {Γ : NRGraph l} →
  {A : DispNRG lA Γ} (B : DispNRG lB (Γ # A)) (C : DispNRG lC (Γ # A # B)) →
  TermDNRG (Γ # A # B # C) (wkn (wkn (wkn A)))
var2 {Γ = Γ} {A = A} B C =
  record {
    tm0 = λ gabc → gabc .fst .fst .snd ;
    tm1 = λ gabc0 gabc1 gabcc → gabcc .fst .fst .snd ;
    tm-nativ = λ gabc0 gabc1 gabcc gabcBdg gabcPrf →
      let fs = nativ-#-proj1 (Γ # A # B) C _ _ _ _ _ _ _ _ gabcPrf in
      let fsfs = nativ-#-proj1 (Γ # A) B _ _ _ _ _ _ _ _ fs in
      nativ-#-proj2 Γ A _ _ _ _ _ _ _ _ fsfs
  }


