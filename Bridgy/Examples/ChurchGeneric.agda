------------------------------------------------------------------------
-- A proof that the (strict) initial algebra of a container functor F,
-- F X := Σ[ s ∈ S ] P s → X
-- can be church encoded, i.e.
-- μ F ≃ ∀ X. (F X → X) → X
-- 
-- warning: S, and P : S → Type must be bridge-discrete.
------------------------------------------------------------------------

{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.ChurchGeneric where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BDisc
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.Core.CubicalLemmas
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
open import Cubical.Functions.FunExtEquiv
-- open import Cubical.Foundations.Transport



module _ (S : Type) (Sbd : isBDisc S) (P : S → Set) (PbdP : isBDiscP S Sbd P) where


  ------------------------------------------------------------------------
  -- First, we must build X : Type ⊨ (FX → X) → X dNRG.

  F : ∀ {l} → Type l → Type l
  F X = Σ[ s ∈ S ] (P s → X)


  -- X:Type , s : S ⊨ P s dNRG
  PdNRG : ∀ {l} → DispNRG ℓ-zero (TypeNRG l # bDisc-asDNRG S Sbd)
  PdNRG = bDiscP-asDNRG (TypeNRG _) S Sbd P PbdP

  -- the container functor as a dNRG, i.e. (X:Type l) ⊨ F X dNRG, i.e. X ⊨ Σ[ s : S] P s → X dNRG
  FdNRG : ∀ {l} → DispNRG l (TypeNRG l)
  FdNRG {l} =
    ΣForm (bDisc-asDNRG S Sbd)
    (→Form ℓ-zero l
      PdNRG
    -- X:Type, s:S ⊨ ElX dNRG
    (X,stuff⊨ElX (bDisc-asDNRG S Sbd)))
    -- (X,stuff⊨ElX (bDisc-asDNRG S Sbd)))

  -- FdNRG is Σ[ s : S] P s → X decorated with a (dependent) relational extensionality principle
  Fcheck : ∀ {l} (X : Type l) →
    (FdNRG .dcr X) ≡ (Σ[ s ∈ S ] (P s → X))
  Fcheck X = refl

  -- X : Type l ⊨ (FX → X) → X dNRG.  
  ChurchF-dNRG : ∀ {l} → DispNRG l (TypeNRG l)
  ChurchF-dNRG {l} =
   flip (→Form l l) (X⊨ElX)
   (→Form l l (FdNRG) (X⊨ElX))

  ChurchF-check : ∀ (X : Type) →
    (ChurchF-dNRG .dcr X)
    ≡
    ( ((Σ[ s ∈ S ] (P s → X)) → X) → X )
  ChurchF-check X = refl

  ------------------------------------------------------------------------
  -- Second, we state the Church encoding
  -- We do everything at Type₀. It's possible to do it at Type l (see specific Church encodings in Church.agda e.g.)

  -- data type.
  data μF l : Type l where
    foldμF : F (μF l) → μF l

  recμF : {M : Set} → (F M → M) → (x : μF ℓ-zero) → M
  recμF foldM (foldμF (s , vs)) = foldM (s , λ pos → recμF foldM (vs pos))

  -- Church encoding.
  ChF : Type₁
  ChF = ∀ (X : Type) → (F X → X) → X

  fmapF : ∀ {lA lB} {A : Type lA} {B : Type lB} (f : A → B) → F A → F B
  fmapF f (s , vs) = s , λ pos → f (vs pos)

  ChFold : F ChF → ChF
  ChFold f X red = red (fmapF (λ fp → fp X red) f)

  -- equivalence.
  genericChurch :
    (∀ (X : Type) → ((F X → X) → X))
    ≃
    μF ℓ-zero
  genericChurch = isoToEquiv (iso
    ChFtoμF
    μFtoChF
    μF≤ChF
    λ ch → funExt λ A → funExt λ f →
      let auxparam = param (TypeNRG ℓ-zero) ChurchF-dNRG ch (μF ℓ-zero) A (λ x a → recμF f x ≡ a) foldμF f param-obl in
      (μFToChF-Vs-recμF (ChFtoμF ch) A f) ∙ auxparam) -- path-compose the μFToChF-Vs-recμF lemma with a param call.

    where

      ChFtoμF : ChF → μF ℓ-zero
      ChFtoμF c = c (μF ℓ-zero) foldμF

      μFtoChF : μF ℓ-zero → ChF
      μFtoChF (foldμF (s , vs)) X foldX = foldX (s , λ pos → μFtoChF (vs pos) X foldX)

      μF≤ChF : (x : μF ℓ-zero) → ChFtoμF (μFtoChF x) ≡ x
      μF≤ChF (foldμF (s , vs)) = cong foldμF (cong (s ,_) (funExt λ pos → μF≤ChF (vs pos)))

      param-obl : {A : Type ℓ-zero} {f : F A → A} → →Form ℓ-zero ℓ-zero FdNRG X⊨ElX ⦅ foldμF , f ⦆# (λ x a → recμF f x ≡ a)
      param-obl {f = f} (s0 , f0) (s1 , f1) (ss , ff) =
        cong f (ΣPathP (ss , funExtDep
        λ {p0} {p1} pp → ff p0 p1 pp))

      μFToChF-Vs-recμF : (x : μF ℓ-zero) (A : Type ℓ-zero) (f : F A → A) →
        μFtoChF x A f ≡ recμF f x
      μFToChF-Vs-recμF (foldμF (s , vs)) A f = cong f (ΣPathP (refl ,
        funExt λ pos → μFToChF-Vs-recμF (vs pos) A f))

  
