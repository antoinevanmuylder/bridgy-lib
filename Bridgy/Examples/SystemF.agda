{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-} -- --no-termination-check

module Bridgy.Examples.SystemF where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.FinData.Base
open import Cubical.Data.List.FinData
open import Cubical.Data.Empty.Base renaming (rec to botrec)

------------------------------------------------------------------------
-- SysF kinding contexts (e.g. (α : *_2 , β : *_6 , γ : *_1))
-- and their translation to ROTT contexts (eg. ( α:Type₂ , β  : Type₆ , γ : Type₁ ))

toLvl : ℕ → Level
toLvl 0 = ℓ-zero
toLvl (suc n) = (ℓ-suc (toLvl n))

-- this kinding context (α : *_2 , β : *_6 , γ : *_1) ⊢ ...
-- is repr by [1, 6, 2]
FKCtx = List ℕ



-- needed to define interpretation of kinding contexts without Type:Type
ctx-sort : FKCtx → Level
ctx-sort [] = ℓ-zero
ctx-sort (l ∷ ls) = ℓ-max (ctx-sort ls) (ℓ-suc (toLvl l))

-- [1, 6, 2] ↦ the ROTT context ( α:Type₂ , β  : Type₆ , γ : Type₁ ) ⊨ ...
⟦_⟧kctx : ∀ (Θ : FKCtx) → NRGraph (ctx-sort Θ)
⟦_⟧kctx [] = topNRG
⟦_⟧kctx (l ∷ ls) =  ⟦ ls ⟧kctx #  (todNRG ⟦ ls ⟧kctx (TypeNRG (toLvl l)))




------------------------------------------------------------------------
-- SysF types and their translation to ROTT types (i.e. dNRGs)


data FType (Θ : FKCtx) : (lτ : ℕ) → Type  where
  Ftyvar : (i : Fin (length Θ)) → FType Θ (lookup Θ i)   --de bruijn indices
  _⟶_ : ∀ {l-left l-right : ℕ} → FType Θ l-left → FType Θ l-right → FType Θ (max l-left l-right)
  F∀ : ∀ {l-extra lτ : ℕ} → FType (l-extra ∷ Θ) lτ → FType Θ (max (suc l-extra) lτ)

ty-sort : (Θ : FKCtx) (lτ : ℕ) → (FType Θ lτ) → Level
ty-sort Θ lτ (Ftyvar i) = toLvl (lookup Θ i)
ty-sort Θ lτ (_⟶_ {l-left} {l-right} tyl tyr) = ℓ-max (ty-sort Θ l-left tyl) (ty-sort Θ l-right tyr)
ty-sort Θ lτ (F∀ {l-extra} {l-ττ} τ) = ℓ-max (ℓ-suc (toLvl l-extra)) (ty-sort (l-extra ∷ Θ) l-ττ τ)



-- the part of the translation `⟦_⟧type` mapping sysF types that are variables
⟦Ftyvar⟧ : ∀ (Θ : FKCtx) (i : Fin (length Θ)) → DispNRG (toLvl (lookup Θ i)) (⟦ Θ ⟧kctx)
⟦Ftyvar⟧ [] i = botrec (¬Fin0 i)
⟦Ftyvar⟧ (l ∷ Θ) zero = lastType
⟦Ftyvar⟧ (l ∷ Θ) (suc i) = wkn (⟦Ftyvar⟧ Θ i)

-- The translation.
-- Θ ⊢ τ : *_lτ
-- -------------------------------
-- ⟦ Θ ⟧kctx ⊨ ⟦ τ ⟧type dNRG (lτ)
⟦_⟧type : ∀ {Θ : FKCtx} {lτ : ℕ} → (τ : FType Θ lτ) → DispNRG (ty-sort Θ lτ τ) (⟦ Θ ⟧kctx)
⟦_⟧type {Θ} {lτ} (Ftyvar i) = ⟦Ftyvar⟧ Θ i
⟦_⟧type {Θ} {lτ} (tyl ⟶ tyr) = →Form _ _ (⟦ tyl ⟧type) (⟦ tyr ⟧type)
⟦_⟧type {Θ} {lτ} (F∀ {l-extra} {l} τ) = ΠForm (todNRG ⟦ Θ ⟧kctx (TypeNRG (toLvl l-extra))) ⟦ τ ⟧type


module SysFParam (Θ : FKCtx) (lτ : ℕ) (τ : FType Θ lτ) where

  -- Reynold's abstraction theorem
  -- all sysf denotations are parametric
  sysf-param :
    (f : (g : ⟦ Θ ⟧kctx .nrg-cr) → ⟦ τ ⟧type .dcr g)
    (g0 g1 : ⟦ Θ ⟧kctx .nrg-cr) (gg : ⟦ Θ ⟧kctx ⦅ g0 , g1 ⦆) →
    ⟦ τ ⟧type ⦅ f g0 , f g1 ⦆# gg
  sysf-param f g0 g1 gg = param ⟦ Θ ⟧kctx ⟦ τ ⟧type _ _ _ _






