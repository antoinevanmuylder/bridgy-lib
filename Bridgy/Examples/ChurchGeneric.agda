{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.ChurchGeneric where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BDisc
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.Rules

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Transport


module _ (S : Type) (Sbd : isBDisc S) (P : S → Set) (PbdP : isBDiscP S Sbd P) where

  SNRG : NRGraph ℓ-zero
  SNRG = bDisc-asNRG S Sbd

  PdNRG : DispNRG ℓ-zero SNRG
  PdNRG = bDiscP-asDNRG S Sbd P PbdP

  



















-- SB : BDisc ℓ-zero
-- SB = S , Sdiscr

-- SNRG : NRGraph ℓ-zero
-- SNRG = discrNRG SB

-- SDispNRG : ∀ {ℓ} {Γ : NRGraph ℓ} → DispNRG ℓ-zero Γ
-- SDispNRG = constDispNRG SNRG

-- F : ∀ {ℓ} → Set ℓ → Set ℓ
-- F X = Σ[ s ∈ S ] (P s → X) 

-- FAlg : Set₁
-- FAlg = Σ[ X ∈ Set ] (F X → X)

-- fmapF : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → F A → F B
-- fmapF f (s , vs) = s , λ pos → f (vs pos)

-- ChF : Set₁
-- ChF = ∀ (X : Set) → (F X → X) → X -- Suggestion: quantify over hSets?

-- ChFold : F ChF → ChF
-- ChFold f X red = red (fmapF (λ fp → fp X red) f)

-- varZero : ∀ {ℓ} → DispNRG ℓ (TypeNRG ℓ)
-- varZero {ℓ} = Nrelator-DispNRG idNRelator

-- PDispNRG : ∀ {ℓ} (Γ : NRGraph ℓ) → DispNRG ℓ-zero (Γ # SDispNRG)
-- dcr (PDispNRG Γ) (γ , s) = P s 
-- dedge (PDispNRG Γ) (γ0 , s0) (γ1 , s1) (γR , eqs) pos0 pos1 = subst P eqs pos0 ≡ pos1
-- dnativ (PDispNRG Γ) (γ0 , s0) (γ1 , s1) γR = Pdiscr s0 s1 (λ i → snd (γR i))

-- FNrel : ∀ {ℓ} → NRelator (TypeNRG ℓ) (TypeNRG ℓ)
-- FNrel {ℓ} = DispNRG-Nrelator (ΣForm SDispNRG
--             (→Form (PDispNRG (TypeNRG ℓ)) (wkn-type-by (TypeNRG ℓ) SDispNRG (varZero {ℓ}))))

-- ChDNRG : DispNRG ℓ-zero (TypeNRG ℓ-zero)
-- ChDNRG = →Form (→Form (tySubst (TypeNRG ℓ-zero) (TypeNRG ℓ-zero) (FNrel {ℓ-zero}) (varZero {ℓ-zero})) (varZero {ℓ-zero})) (varZero {ℓ-zero})

-- -- ChNRel : NRelator (TypeNRG ℓ-zero) (TypeNRG ℓ-zero)
-- -- ChNRel = DispNRG-Nrelator {ℓ-zero} {ℓ-zero} ChDNRG

-- -- ChNRGraph : NRGraph ℓ-zero
-- -- ChNRGraph = ΠNRG {ℓ-zero} {ℓ-zero} (TypeNRG ℓ-zero) ChNRel

-- paramChF : (f : ChF) (A B : Type) (R : A → B → Type)
--              (foldA : F A → A) (foldB : F B → B) →
--              ((fa : F A) (fb : F B) →
--                 (Σ (fst fa ≡ fst fb) (λ eqs →
--                       (pa : P (fst fa)) (pb : P (fst fb)) → subst P eqs pa ≡ pb → R (snd fa pa) (snd fb pb))) →
--                    R (foldA fa) (foldB fb)) →
--              R (f A foldA) (f B foldB)
-- paramChF = param' (TypeNRG ℓ-zero) ChDNRG

-- transport-domain : 
--   ∀ {A : Set} {B : A → Set} {C : Set} {a1 a2 : A} (eq : a1 ≡ a2) (f : B a1 → C) (v : B a2) →
--   transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v)
-- transport-domain {A} {B} {C} {a1} {a2} eq f v =
--   J (λ a2 eq → (v : B a2) → transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v))
--   (λ v → cong (λ f → f v) (transportRefl f) ∙ sym (cong f (substRefl {B = B} v))) 
--   eq v 

-- subst-subst : {A : Set} (B : A → Set) {a1 a2 : A} (eq : a1 ≡ a2) (b : B a2) → subst B eq (subst B (sym eq) b) ≡ b
-- subst-subst B eq b i = transp (λ j → B (eq (j ∨ i))) i (transp (λ j → B (eq (~ j ∨ i))) i b)

-- -- relation to initial algebra as data type?
-- data μF ℓ : Set ℓ where
--   foldμF : F (μF ℓ) → μF ℓ

-- recμF : {M : Set} → (F M → M) → (x : μF ℓ-zero) → M
-- recμF foldM (foldμF (s , vs)) = foldM (s , λ pos → recμF foldM (vs pos))

-- ChFtoμF : ChF → μF ℓ-zero
-- ChFtoμF c = c (μF ℓ-zero) foldμF

-- μFtoChF : μF ℓ-zero → ChF
-- μFtoChF (foldμF (s , vs)) X foldX = foldX (s , λ pos → μFtoChF (vs pos) X foldX)

-- ChFtoμF∘μFtoChF : (x : μF ℓ-zero) → ChFtoμF (μFtoChF x) ≡ x
-- ChFtoμF∘μFtoChF (foldμF (s , vs)) = cong foldμF (cong (s ,_) (funExt λ pos → ChFtoμF∘μFtoChF (vs pos)))

-- congΣ : {A : Set} {B : A → Set} {a1 a2 : A} → (eqs : a1 ≡ a2) →
--         (b1 : B a1) (b2 : B a2) → subst B eqs b1 ≡ b2 → _≡_ {A = Σ A B} (a1 , b1)  (a2 , b2)
-- congΣ eqs b1 b2 eq2 = cong₂ _,_ eqs (toPathP eq2)

-- μFtoChF∘ChFtoμF : (x : ChF) → μFtoChF (ChFtoμF x) ≡ x
-- μFtoChF∘ChFtoμF x = funExt λ X → funExt λ foldX → help foldX
--   where help2 : {X : Set} (foldX : F X → X) → (fa : F (μF ℓ-zero)) (fb : F X) →
--                                                 Σ[ eqs ∈ fst fa ≡ fst fb ]
--                                                   ((pa : P (fst fa)) (pb : P (fst fb)) →
--                                                     subst P eqs pa ≡ pb → μFtoChF (snd fa pa) X foldX ≡ snd fb pb) →
--                                                 μFtoChF (foldμF fa) X foldX ≡ foldX fb
--         help2 {X} foldX (sμ , vsμ) (sx , vx) (eqs , eqvs) = cong foldX (congΣ eqs (λ pos → μFtoChF (vsμ pos) _ foldX) vx ((funExt λ pb → transport-domain eqs (λ pos → μFtoChF (vsμ pos) X foldX) pb) ∙ funExt λ pb → eqvs (subst P (sym eqs) pb) pb (subst-subst P eqs pb) ))
--         help : {X : Set} (foldX : F X → X) → μFtoChF (x (μF ℓ-zero) foldμF) X foldX ≡ x X foldX
--         help {X} foldX = paramChF x (μF ℓ-zero) X (λ v x → μFtoChF v X foldX ≡ x) foldμF foldX (help2 foldX)

-- μFChIso : Iso (μF ℓ-zero) ChF
-- Iso.fun μFChIso = μFtoChF
-- Iso.inv μFChIso = ChFtoμF
-- Iso.rightInv μFChIso = μFtoChF∘ChFtoμF
-- Iso.leftInv μFChIso = ChFtoμF∘μFtoChF

-- μFChFequiv : μF ℓ-zero ≃ ChF
-- μFChFequiv = isoToEquiv μFChIso


-- --   {!ChDNRG .dedge (μF ℓ-zero) X (λ dt elx → recμF {M = X} foldX dt ≡ elx) (x (μF ℓ-zero)) (x X) !} 
