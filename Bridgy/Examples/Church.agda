{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Examples.Church where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.List


-- In this file: specific Church encodings.


-- X:Type ⊨ ElX → ElX dNRG
churchUnitDNRG : ∀ (l : Level) → DispNRG l (TypeNRG l)
churchUnitDNRG l = →Form l l X⊨ElX X⊨ElX

churchUnit : ∀ {l} → Unit ≃ ( ∀ (X : Type l) → X → X )
churchUnit {l} = isoToEquiv (iso
  (λ _ X x → x)
  (λ _ → tt)
  (λ ch → funExt λ X → funExt λ x →
    param (TypeNRG l) (churchUnitDNRG l) ch (Lift Unit) X (λ (lift tt) y → x ≡ y ) (lift tt) x refl)
  λ tt → refl)

-- X:Type ⊨ ElX → (ElX → ElX) dNRG
churchBoolDNRG : ∀ (l : Level) → DispNRG l (TypeNRG l)
churchBoolDNRG l = →Form l l (X⊨ElX) (→Form l l X⊨ElX X⊨ElX)

churchBool : ∀ {l} → Bool ≃ ( ∀ (X : Type l) → X → X → X )
churchBool {l} = isoToEquiv (iso
  boolToCh
  chToBool
  (λ ch → funExt λ A → funExt λ at → funExt λ af →
    param (TypeNRG l) (churchBoolDNRG l) ch (Lift Bool) A (λ lb a → boolToCh (lb .lower) A at af ≡ a) (lift true) at refl (lift false) af refl)
  λ { false → refl ;
       true → refl })
  where
    boolToCh : ∀ {l} → Bool → ( ∀ (X : Type l) → X → X → X )
    boolToCh true X xt xf = xt
    boolToCh false X xt xf = xf

    chToBool : ∀ {l} → ( ∀ (X : Type l) → X → X → X ) → Bool
    chToBool ch = ch (Lift Bool) (lift true) (lift false) .lower

-- X:Type ⊨ ElX → ((ElA → ElX→ ElX) → ElX)
-- where A is a bridge discrete type
churchListDNRG : ∀ (l : Level) → (A : Type l) → (isbA : isBDisc A) → DispNRG l (TypeNRG l)
churchListDNRG l A isbA =
  →Form l l (X⊨ElX)
  (flip (→Form l l) (X⊨ElX)
  (→Form l l
  (bDisc-asDNRG A isbA)
  (→Form l l (X⊨ElX) (X⊨ElX) )))

-- crucial hypothesis: isBDisc A. Else too many elements in the encoding.
-- E.g. for A = Type₀,
--   foo : ( (X : Type ℓ) → X → (Type₀ → X → X) → X )
--   foo = λ X niil coons → (coons X niil)
churchList : ∀ {ℓ} (A : Type ℓ) (bd : isBDisc A) →
  ( (X : Type ℓ) → X → (A → X → X) → X ) ≃ List A
churchList {ℓ} A bd =
  isoToEquiv (iso
  churchToList
  listToChurch
  sameList
  λ chl → funExt λ X → funExt λ niil → funExt λ coons →
    param (TypeNRG ℓ) (churchListDNRG ℓ A bd) chl (List A) X (λ as x → listToChurch as X niil coons ≡ x) [] niil refl _∷_ coons
      λ a0 a1 abdg as x hyp →
      λ i → coons (abdg i) (hyp i))

  where

    churchToList : ( (X : Type ℓ) → X → (A → X → X) → X ) → List A
    churchToList = (λ f → f (List A) [] _∷_)

    listToChurch : List A → ( (X : Type ℓ) → X → (A → X → X) → X )
    listToChurch [] = λ X d f → d
    listToChurch (a ∷ as) = λ X d f → f a (listToChurch as X d f)

    sameList : ∀ as → churchToList (listToChurch as) ≡ as
    sameList [] = refl
    sameList (a ∷ as) = ListPath.decode _ _
      (refl ,
      ListPath.encode (churchToList (listToChurch as)) as
      (sameList as))
