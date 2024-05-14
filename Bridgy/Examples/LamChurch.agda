{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}



module Bridgy.Examples.LamChurch where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
--open import Cubical.Data.FinData.Base
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Bool



open import Bridgy.Core.EquGraph
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.Bool

open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.MoreRules
open import Bridgy.ROTT.MoreVarRules


_my<_ : ℕ → ℕ → Bool
0 my< 0 = false
0 my< (suc n) = true
(suc n) my< 0 = false
(suc n) my< (suc m) = n my< m

data Lam : ℕ → Type where
  var : ∀ n i → (i my< n ≡ true) → Lam n
  lam : ∀ n → Lam (suc n) → Lam n
  appl : ∀ n → Lam n → Lam n → Lam n

------------------------------------------------------------------------
-- lemmas



-- turn the above into a term of ROTT (in an arbitrary context)
-- Γ ⊨ < : nat → nat → Bool
my<Term : ∀ {l} {Γ : NRGraph l} → TermDNRG Γ (→Form _ _ NatForm (→Form _ _ NatForm (BoolForm)))
my<Term = record {
  tm0 = λ _ n m → n my< m  ;
  tm1 = λ _ _ _ → tm1my< ;
  tm-nativ = λ _ _ _ _ _ →
    -- can shortcut by observing that Bool is an hset.
    inEquGrInv (funExt λ n0 → funExt λ n1 → funExt λ nn →  funExt λ m0 →  funExt λ m1 → funExt λ mm → isOfHLevelRespectEquiv 1 (Bool≡≃ _ _) (isSetBool _ _) _ _ )
  }
  where
    tm1my< : ∀ n0 n1 (nn : codeℕ n0 n1) m0 m1 (mm : codeℕ m0 m1) → Bool~ (n0 my< m0) (n1 my< m1)
    tm1my< 0 (suc n) ctr = rec ctr
    tm1my< (suc n) 0 ctr = rec ctr
    tm1my< _ _ _ 0 (suc m) ctr = rec ctr
    tm1my< _ _ _ (suc m) 0 ctr = rec ctr
    tm1my< zero zero nn zero zero mm = tt
    tm1my< zero zero nn (suc m0) (suc m1) mm = tt
    tm1my< (suc n0) (suc n1) nn zero zero mm = tt
    tm1my< (suc n0) (suc n1) nn (suc m0) (suc m1) mm =
      tm1my< n0 n1 nn m0 m1 mm



    
------------------------------------------------------------------------
-- a presentation of the theory of lambda terms, written as a dNRG
-- _:1 , L : ℕ → Type ⊨ (∀ n i → (i my< n ≡ true) → L n) × (∀ n → L (suc n) → L n) × (∀ n → Lam n → Lam n → Lam n)
-- we proceed in three steps.

varDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
varDNRG = ΠForm (NatForm) (ΠForm (NatForm)
  (→Form _ _
  -- (i my< n ≡ true)
  (≡Form (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm # NatForm) BoolForm
    (app2 my<Term
      (let v = var0 ctx13 NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      let v = var1 {Γ = ctx23} NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    (boolCons true))
  -- L n
  (El (app _ NatForm (UForm ℓ-zero)
    (let v = var2 topNRG (→Form _ _ (NatForm) (UForm ℓ-zero)) NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
  let v = var1 {Γ = topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero))} NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))

  where
    ctx03 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm # NatForm)
    ctx13  = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm)
    ctx23 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)

-- (∀ n → L (suc n) → L n)
lamDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
lamDNRG = ΠForm NatForm (
  let
    n = var0 ctx12 NatForm
    L = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)) NatForm
  in
  →Form _ _
  -- L (suc n)
  (El (app ctx02 NatForm (UForm ℓ-zero)
    (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ })
    (app _ _ _ sucTerm (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ }))))

  -- L n
  (El (app ctx02 NatForm (UForm ℓ-zero)
    (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ })
    (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ }))))

  where

    ctx12 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero))
    ctx02 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm



-- (∀ n → Lam n → Lam n → Lam n)
applDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
applDNRG = ΠForm NatForm
  let
    n = var0 ctx12 NatForm
    L = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)) NatForm
    localApp' = app ctx02 NatForm (UForm ℓ-zero)
    localApp = (El (localApp' (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ }) (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ })))
  in
  →Form _ _ localApp (→Form _ _ localApp localApp)

  where
    ctx12 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero))
    ctx02 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm

      
-- _:1 , L : ℕ → Type ⊨ (∀ n i → (i my< n ≡ true) → L n) × (∀ n → L (suc n) → L n) × (∀ n → Lam n → Lam n → Lam n)
LamPres : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
LamPres = ×Form _ _ varDNRG (×Form _ _ lamDNRG applDNRG) 
