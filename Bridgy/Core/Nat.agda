{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.Nat where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.List
open import Bridgy.Core.MyPathToEquiv




-- Nat≃List1 : ℕ ≃ List Unit
-- Nat≃List1 = isoToEquiv (iso
--   natToList
--   length
--   List1<=Nat
--   Nat<=List1)

--   where
--     natToList : ℕ → List Unit
--     natToList zero = []
--     natToList (suc n) = tt ∷ natToList n

--     Nat<=List1 : ∀ n → length (natToList n) ≡ n
--     Nat<=List1 0 = refl
--     Nat<=List1 (suc n) = cong suc (Nat<=List1 n)

--     List1<=Nat : ∀ us → natToList (length us) ≡ us
--     List1<=Nat [] = refl
--     List1<=Nat (tt ∷ us) = cong (_∷_ tt) (List1<=Nat us)

-- BridgeNat≡BridgeList1 : ∀ n0 n1 →
--   Bridge ℕ n0 n1 ≡
--   Bridge (List Unit) (equivFun Nat≃List1 n0) (equivFun Nat≃List1 n1)
-- BridgeNat≡BridgeList1 n0 n1 =
--   change-line-path
--     (λ _ → ℕ) (λ _ → List Unit) n0 n1
--     (equivFun Nat≃List1 n0) (equivFun Nat≃List1 n1)
--     (λ _ → ua Nat≃List1)
--     (transportRefl _)
--     (transportRefl _)

-- -- can compse this with the SIP at Nat which characterize
-- -- ≡_nat as an inductive relation based on the shape of nat
-- SRP-Nat' : ∀ n0 n1 → (n0 ≡ n1) ≃ Bridge ℕ n0 n1
-- SRP-Nat' n0 n1 =
--   flip compEquiv
--   (mypathToEquiv (sym (BridgeNat≡BridgeList1 n0 n1)))
--   (flip compEquiv (ListvsBridge {A = Unit})
--   {![List BridgeP (λ _ → Unit) ]!})

--   where
  
--     hlp : ∀ us0 us1 →
--       (length us0 ≡ length us1)  ≃ [List BridgeP (λ _ → Unit) ] us0 us1
--     hlp = {!!}
    



-- see Bridgy.Core.List for explanation of this kind of proof

-- codeℕ is observational equality of nat in cubical lib
decodeBdgNat : ∀ n0 n1 → codeℕ n0 n1 → Bridge ℕ n0 n1
decodeBdgNat zero zero tt = λ _ → zero
decodeBdgNat (suc n0) (suc n1) prf =
  λ x → suc (decodeBdgNat n0 n1 prf x)


zbdg : BridgeP (λ x → primGel _ _ codeℕ x) zero zero
zbdg = λ x →  prim^gel {R = codeℕ} zero zero tt x

sucbdg : BridgeP (λ x → (primGel _ _ codeℕ x) → (primGel _ _ codeℕ x)) suc suc
sucbdg =
  equivFun (ΠvsBridgeP) λ n0 n1 nn →
  λ y → prim^gel {R = codeℕ} (suc n0) (suc n1) (prim^ungel {R = codeℕ} (λ x → nn x)) y

idbdg : BridgeP (λ x → ℕ → primGel _ _ codeℕ x) (idfun ℕ) (idfun ℕ)
idbdg x zero = zbdg x
idbdg x (suc n) = sucbdg x (idbdg x n)










