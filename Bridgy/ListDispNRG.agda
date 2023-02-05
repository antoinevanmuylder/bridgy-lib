{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ListDispNRG where

open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma using ( _×_ )

{-

we define the displayed NRG  A:Type ⊢ List A dnrg
we first need a (displayed ) commutation principle Bridge vs Lists

-}

-- List { as0, as1 }# R
-- inspired from the encode-decode technique of List.Properties
ListRCover : ∀ {ℓ} (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) → List A0 → List A1 → Type ℓ
ListRCover A0 A1 R [] [] = Lift Unit
ListRCover A0 A1 R [] (_ ∷ _) = Lift ⊥
ListRCover A0 A1 R (_ ∷ _) [] = Lift ⊥
ListRCover A0 A1 R (a0 ∷ as0) (a1 ∷ as1) = R a0 a1 × ListRCover A0 A1 R as0 as1



ListDispNRG : ∀ {ℓ} → DispNRG ℓ (TypeNRG ℓ)
ListDispNRG = record {
  dcr = List ;
  dedge = λ A0 A1 R → ListRCover A0 A1 R ;
  dnativ = λ A0 A1 Abdg as0 as1 → {!!} } -- het bridges of lists
