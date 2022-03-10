{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --allow-unsolved-metas #-}
module ChurchCircle where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.HITs.S1

open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import NativeReflGraphRelator
open import ParamNativeRelator


-- in this file we prove a Church encoding for the circle
-- Namely:    ∀ (X⋆ : Type⋆) . Ω X⋆ → X     ≃     S1
-- say ≤ means "retract"
-- S1 ≤ ∀ (X⋆ : Type⋆) . Ω X⋆ → X essentially by computation.
-- ∀ (X⋆ : Type⋆) . Ω X⋆ → X  ≤   S1 by parametricity.
-- the proof is hence similar to eg ∀ X . X → X → X     ≃     Bool
-- (both are instances of yoneda)


-- pointed types
Type⋆ : ∀ (ℓ : Level) → Type (ℓ-suc ℓ)
Type⋆ ℓ = Σ[ X ∈ Type ℓ ] X

Type⋆₀ : Type₁
Type⋆₀ = Type⋆ ℓ-zero

-- Type⋆ with pointed relations is a native reflexive graph.
instance
  Type⋆HasNRG : ∀ {ℓ} → HasNRGraph (Type⋆ ℓ)
  Type⋆HasNRG {ℓ} = record { nedge = λ { (X0 , x0) (X1 , x1) →  Σ[ R ∈ (X0 → X1 → Type ℓ) ] (R x0 x1) }
                           ; nativ = λ where (X0 , x0) (X1 , x1) → flip compEquiv ΣvsBridgeP
                                                                    (Σ-cong-equiv
                                                                      (relativity)
                                                                      λ R →  invEquiv (pathToEquiv (funExt⁻ (funExt⁻ (rel-retract R) x0) x1))) }

-- the forgetful native relator Type⋆ → Type
forgPt : ∀ {ℓ} → NRelator (Type⋆ ℓ) (Type ℓ)
forgPt = record { nobjMap = λ { (X , pt) → X }
                ; nedgeMap =  λ { (R , ptd) → R }
                ; nativ-rel = λ where (X0 , x0) (X1 , x1) → refl }


-- the loop-space native relator Ω
-- bug: normalization does not seem to terminate!
-- + we need more computational rules to conclude (wip)
Ω : ∀ {ℓ} → NRelator (Type⋆ ℓ) (Type ℓ)
Ω = record { nobjMap = λ { (X , pt) → pt ≡ pt }
           ; nedgeMap = λ { (R , ptd) → λ loop0 loop1 →  PathP (λ i → R (loop0 i) (loop1 i)) ptd ptd  }
           -- ; nativ-rel = λ where (X0 , x0) (X1 , x1) → funExt λ q → funExt λ l0 → funExt λ l1 → {!!} }
           ; nativ-rel = λ where (X0 , x0) (X1 , x1) → funExt λ q → funExt λ l0 → funExt λ l1 →
                                   ua (isoToEquiv (iso
                                     (λ pth → {!λ x i → pth i x!}) -- λ x i → pth i x
                                     (λ bdg → {!λ i x → bdg x i!}) {!!} {!!})) } -- λ i x → bdg x i


-- below a trick to avoid weird instance resolution freezes. we define S¹NRelator
-- directly as an eta expansion
S¹NRelator : NRelator (Type⋆₀) Type
S¹NRelator = let ofc = compNRelator ⟨ Ω , forgPt ⟩nrel arrowNRelator
             in
               record { nobjMap =  ofc . nobjMap ; nedgeMap =  ofc .nedgeMap ; nativ-rel =  ofc .nativ-rel }

churchS¹ :  ( ∀ (X⋆ : Type⋆₀) → Ω .nobjMap X⋆ → forgPt .nobjMap X⋆ )   ≃    S¹
churchS¹ = isoToEquiv (iso
             (λ c → c (S¹ , base) loop)
             (λ { base → λ { ( X , x ) → λ _ → x } ; (loop j) → λ { (X , x) → λ p → p j } })
             (λ { base → refl ; (loop j) → refl })
             λ c → funExt λ where (A , a) → funExt λ h →
                                   {! !})
  where
  edgeChoice : ∀ {A : Type} {a : A} {h : a ≡ a} →  Σ (S¹ → A → Type) (λ R → R base a)
  edgeChoice {A} {a} {h}  = (λ { base → λ x → a ≡ x ; (loop j) → λ x → h j ≡ x }) , refl

  -- smth = (param S¹NRelator c (S¹ , base) (A , a) edgeChoice loop h refl)
