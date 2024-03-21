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


-- -- variable rule (last variable)
-- -- Γ NRG     Γ ⊨ A dNRG
-- -- ---------------------
-- -- Γ , X : A ⊨ X : A
-- var0 : ∀ {l lA} → (Γ : NRGraph l) → (A : DispNRG lA Γ) → TermDNRG (Γ # A) (wkn A)
-- var0 Γ A =
--   record {
--     tm0 = λ ga → ga .snd;
--     tm1 = λ ga0 ga1 gaa → gaa .snd ;
--     tm-nativ = λ ga0 ga1 gaa gaBdg gaPrf →
--       nativ-#-proj2 Γ A (ga0 .fst) (ga1 .fst) (gaa .fst) (λ x → gaBdg x .fst) (ga0 .snd) (ga1 .snd) (gaa .snd) (λ x → gaBdg x .snd) gaPrf
--     }

