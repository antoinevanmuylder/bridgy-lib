{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.Bool where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.List

-- Bool≡ : Bool → Bool → Bool
-- Bool→Type (Bool≡ a b)
Bool~ : Bool → Bool → Type
Bool~ a b = Bool→Type (Bool≡ a b)


loosenBoolEq : ∀ b0 b1 → Bool~ b0 b1 → Bridge Bool b0 b1
loosenBoolEq false false tt = λ _ → false
loosenBoolEq true true tt = λ _ → true

fbdg : BridgeP (λ x → primGel _ _ Bool~ x) false false
fbdg = λ x → prim^gel {R = Bool~} false false tt x

tbdg : BridgeP (λ x → primGel _ _ Bool~ x) true true
tbdg = λ x → prim^gel {R = Bool~} true true tt x

tightenBdgBool0 : BridgeP (λ x → Bool → primGel _ _ Bool~ x) (idfun Bool) (idfun Bool)
tightenBdgBool0 x false = fbdg x
tightenBdgBool0 x true = tbdg x

tightenBdgBool : ∀ b0 b1 → Bridge Bool b0 b1 → Bool~ b0 b1
tightenBdgBool b0 b1 bb = prim^ungel {R = Bool~} (λ x → tightenBdgBool0 x (bb x))

apred : (@tick x : BI) → Bool → Type
apred x n =
  (primExtent {A = λ _ → Bool} {B = λ _ _ → Bool} (idfun _) (idfun _)
  (λ n0 n1 → loosenBoolEq n0 n1 ∘ tightenBdgBool n0 n1) x n)
  ≡ n

apred-f : BridgeP (λ x → apred x false) refl refl
apred-f x = refl

apred-t : BridgeP (λ x → apred x true) refl refl
apred-t x = refl


auxeq : BridgeP (λ x → (b : Bool) → apred x b) (λ _ → refl) (λ _ → refl)
auxeq x false = apred-f x
auxeq x true = apred-t x

Bool~<=Bdg : ∀ b0 b1 bb →
  tightenBdgBool b0 b1 (loosenBoolEq b0 b1 bb) ≡ bb
Bool~<=Bdg false false tt = refl
Bool~<=Bdg true true tt = refl


SRP-Bool : ∀ n0 n1 → Bool~ n0 n1 ≃ Bridge Bool n0 n1
SRP-Bool n0 n1 = isoToEquiv (iso
  (loosenBoolEq n0 n1)
  (tightenBdgBool n0 n1)
  (λ nn → λ i x → auxeq x (nn x) i)
  (Bool~<=Bdg n0 n1))


