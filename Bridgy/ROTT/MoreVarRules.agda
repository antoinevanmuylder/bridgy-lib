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



nativ-#-proj1' : ∀ {lΓ lA} (Γ : NRGraph lΓ) (A : DispNRG lA Γ) →
  ∀ ga0 ga1 gaa gaBdg →
  gaa [ (Γ # A) .nativ ga0  ga1 ] gaBdg → 
  gaa .fst [ Γ .nativ (ga0 .fst) (ga1 .fst) ] (λ x → gaBdg x .fst)
nativ-#-proj1' Γ A ga0 ga1 gaa gaBdg gaprf =
  inEquGr λ i x → outEquGr gaprf i x .fst

nativ-#-proj2' : ∀ {lΓ lA} (Γ : NRGraph lΓ) (A : DispNRG lA Γ) →
  ∀ ga0 ga1 gaa gaBdg →
  (gaPrf : gaa [ (Γ # A) .nativ ga0  ga1 ] gaBdg) → 
  gaa .snd
    [ A .dnativ (ga0 .fst) (ga1 .fst) (gaa .fst) (λ x → gaBdg x .fst)
    (nativ-#-proj1' Γ A ga0 ga1 gaa gaBdg gaPrf) (ga0 .snd) (ga1 .snd) ]
  λ x → gaBdg x .snd
nativ-#-proj2' Γ A ga0 ga1 gaa gaBdg gaprf =
  nativ-#-proj2 Γ A (ga0 .fst) (ga1 .fst) (gaa .fst) (λ x → gaBdg x .fst) (ga0 .snd) (ga1 .snd) (gaa .snd) (λ x → gaBdg x .snd) gaprf



-- replacing placeholders with the actual values will speed up typechecking

-- last last last variable.
-- Γ NRG
-- Γ ⊨ A dNRG
-- (Γ # A) ⊨ B dNRG
-- Γ # A # B ⊨ C dNRG
-- -------------------------------------
-- Γ , (a : A) , (b : B), (c : C) ⊨ a : A
var2 : ∀ {l lA lB lC} (Γ : NRGraph l) →
  (A : DispNRG lA Γ) (B : DispNRG lB (Γ # A)) (C : DispNRG lC (Γ # A # B)) →
  TermDNRG (Γ # A # B # C) (wkn (wkn (wkn A)))
var2 Γ A B C =
  record {
    tm0 = λ gabc → gabc .fst .fst .snd ;
    tm1 = λ gabc0 gabc1 gabcc → gabcc .fst .fst .snd ;
    tm-nativ = λ gabc0 gabc1 gabcc gabcBdg gabcPrf →
      let
        fs = nativ-#-proj1' (Γ # A # B) C gabc0 gabc1 gabcc gabcBdg gabcPrf
        fsfs = nativ-#-proj1' (Γ # A) B (gabc0 .fst) (gabc1 .fst) (gabcc .fst) (λ x → gabcBdg x .fst) fs
      in
      nativ-#-proj2' Γ A (gabc0 .fst .fst) (gabc1 .fst .fst) (gabcc .fst .fst) (λ x → gabcBdg x .fst .fst) fsfs

  }


-- Γ NRG
-- Γ ⊨ A dNRG
-- (Γ # A) ⊨ B dNRG
-- Γ # A # B ⊨ C dNRG
-- Γ # A # B # D ⊨ D dNRG
-- -------------------------------------
-- Γ , (a : A) , (b : B), (c : C), (d : D) ⊨ a : A
var3 : ∀ {l lA lB lC lD} (Γ : NRGraph l) →
  (A : DispNRG lA Γ) (B : DispNRG lB (Γ # A)) (C : DispNRG lC (Γ # A # B)) (D : DispNRG lD (Γ # A # B # C)) →
  TermDNRG (Γ # A # B # C # D) (wkn (wkn (wkn (wkn A))))
var3 Γ A B C D =
  record {
    tm0 = λ gabcd → gabcd .fst .fst .fst .snd ;
    tm1 = λ gabcd0 gabcd1 gabcdd → gabcdd .fst .fst .fst .snd ;
    tm-nativ = λ gabcd0 gabcd1 gabcdd gabcdBdg gabcdPrf →
      let
        fs = nativ-#-proj1' (Γ # A # B # C) D gabcd0 gabcd1 gabcdd gabcdBdg gabcdPrf
        fsfs = nativ-#-proj1' (Γ # A # B) C (gabcd0 .fst) (gabcd1 .fst) (gabcdd .fst) (λ x → gabcdBdg x .fst) fs
        fsfsfs = nativ-#-proj1' (Γ # A) B (gabcd0 .fst .fst) (gabcd1 .fst .fst) (gabcdd .fst .fst) (λ x → gabcdBdg x .fst .fst) fsfs
      in
      nativ-#-proj2' Γ A (gabcd0 .fst .fst .fst) (gabcd1 .fst .fst .fst) (gabcdd .fst .fst .fst) (λ x → gabcdBdg x .fst .fst .fst) fsfsfs 
  }

