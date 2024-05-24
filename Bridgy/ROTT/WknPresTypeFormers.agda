{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.WknPresTypeFormers where


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

-- temp file for writing new ROTT rules



-- wkn preserves →Form
-- Γ ⊨ W dRRG
-- Γ ⊨ A dNRG   Γ ⊨ B dNRG
-- Γ . W ⊨ unusable : wkn {W} (A → B)
-- -----------------------------------
-- Γ . W ⊨ usable : (wkn A → wkn B)
wknVs→ : ∀ {l lW lA lB : Level} {Γ : NRGraph l} {W : DispNRG lW Γ} →
  (A : DispNRG lA Γ) (B : DispNRG lB Γ) (unus : TermDNRG (Γ # W) (wkn (→Form _ _ A B))) →
  TermDNRG (Γ # W) (→Form _ _ (wkn A) (wkn B))
wknVs→ A B unus =
  record {
    tm0 = unus .tm0 ;
    tm1 = unus .tm1 ;
    tm-nativ = unus .tm-nativ
  }


-- wkn preserves UForm
-- Γ ⊨ W dRRG
-- Γ . W ⊨ unus : wkn (UForm _)
-- ----------------------------
-- Γ . W ⊨ usable : UForm _
wknVsU : ∀ {lΓ lW l} {Γ : NRGraph lΓ} {W : DispNRG lW Γ} →
  (unus : TermDNRG (Γ # W) (wkn (UForm l))) →
  TermDNRG (Γ # W) (UForm l)
wknVsU unus =
  record {
    tm0 = unus .tm0 ;
    tm1 = unus .tm1 ;
    tm-nativ = unus .tm-nativ
  }


-- Γ . W1 . W2 ⊨ wkn (wkn (UForm _))
-- --------------------------
-- Γ . W1 . W2 ⊨ UForm _
wknWknVsU : ∀ {lΓ l1 l2 l} {Γ : NRGraph lΓ} {W1 : DispNRG l1 Γ} {W2 : DispNRG l2 (Γ # W1)} →
  (unus : TermDNRG (Γ # W1 # W2) (wkn (wkn (UForm l)))) →
  TermDNRG (Γ # W1 # W2) (UForm l)
wknWknVsU unus =
  record {
    tm0 = unus .tm0 ; tm1 = unus .tm1 ; tm-nativ = unus .tm-nativ
  }


