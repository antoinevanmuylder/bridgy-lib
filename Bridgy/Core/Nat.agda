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





-- see Bridgy.Core.List for explanation of this kind of proof

-- codeℕ is observational equality of nat in cubical lib
loosenBdgNat : ∀ n0 n1 → codeℕ n0 n1 → Bridge ℕ n0 n1
loosenBdgNat zero zero tt = λ _ → zero
loosenBdgNat (suc n0) (suc n1) prf =
  λ x → suc (loosenBdgNat n0 n1 prf x)


zbdg : BridgeP (λ x → primGel _ _ codeℕ x) zero zero
zbdg = λ x →  prim^gel {R = codeℕ} zero zero tt x

sucbdg : BridgeP (λ x → (primGel _ _ codeℕ x) → (primGel _ _ codeℕ x)) suc suc
sucbdg =
  equivFun (ΠvsBridgeP) λ n0 n1 nn →
  λ y → prim^gel {R = codeℕ} (suc n0) (suc n1) (prim^ungel {R = codeℕ} (λ x → nn x)) y

tightenBdgNat0 : BridgeP (λ x → ℕ → primGel _ _ codeℕ x) (idfun ℕ) (idfun ℕ)
tightenBdgNat0 x zero = zbdg x
tightenBdgNat0 x (suc n) = sucbdg x (tightenBdgNat0 x n)

tightenBdgNat :  ∀ n0 n1 → Bridge ℕ n0 n1 → codeℕ n0 n1
tightenBdgNat n0 n1 nn = prim^ungel {R = codeℕ} (λ x → tightenBdgNat0 x (nn x))


apred : (@tick x : BI) → ℕ → Type
apred x n =
  (primExtent {A = λ _ → ℕ} {B = λ _ _ → ℕ} (idfun _) (idfun _)
  (λ n0 n1 → loosenBdgNat n0 n1 ∘ tightenBdgNat n0 n1) x n)
  ≡ n

apred-z : BridgeP (λ x → apred x zero) refl refl
apred-z x = refl

apred-suc : BridgeP (λ x → (n : ℕ) → apred x n → apred x (suc n))
  (λ n → cong suc) (λ n → cong suc)
apred-suc =
  equivFun (ΠvsBridgeP) λ n0 n1 nn →
  λ x → cong suc

auxnateq : BridgeP (λ x → (n : ℕ) → apred x n) (λ _ → refl) λ _ → refl
auxnateq x zero = apred-z x
auxnateq x (suc n) = apred-suc x n (auxnateq x n)

codeℕ<=Bdg : ∀ n0 n1 (nn : codeℕ n0 n1) →
  tightenBdgNat n0 n1 (loosenBdgNat n0 n1 nn) ≡ nn
codeℕ<=Bdg zero zero tt = refl
codeℕ<=Bdg zero (suc n) ctr = rec ctr
codeℕ<=Bdg (suc n) zero ctr = rec ctr
codeℕ<=Bdg (suc n0) (suc n1) pf = codeℕ<=Bdg n0 n1 pf


SRP-Nat : ∀ n0 n1 → codeℕ n0 n1 ≃ Bridge ℕ n0 n1
SRP-Nat n0 n1 = isoToEquiv (iso
  (loosenBdgNat n0 n1)
  (tightenBdgNat n0 n1)
  (λ nn → λ i x → auxnateq x (nn x) i)
  (codeℕ<=Bdg n0 n1))


SRP-Nat' : ∀ n0 n1 → (n0 ≡ n1) ≃ Bridge ℕ n0 n1
SRP-Nat' n0 n1 = compEquiv (≡ℕ≃Codeℕ _ _) (SRP-Nat _ _)
--note: not *exactly* the same than being bridge discrete
--the latter requires that a specific function ≡ → Bdg is an equivalence.






