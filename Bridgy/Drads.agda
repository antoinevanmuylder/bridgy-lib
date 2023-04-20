{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module Bridgy.Drads where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Bridgy.NRGRelRecord
open import Bridgy.Param
open import Bridgy.List using ( churchListNRelator )
open import Bridgy.BDisc
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.List
open import Cubical.Data.Sigma using ( _×_ )


somethm : ∀ (A C : Type) →
            (A × Bool → C) ≃ (A → Bool → C)
somethm = λ A C → isoToEquiv (iso
            (λ k → λ a → λ b → k (a , b))
            (λ h → λ p → let ( a , b ) = p in h a b)
            (λ h → refl)
            λ k → refl)

-- Pi,
-- Sigma, ×, →, Type, inductives, nat, ≡, S1

-- (Bool , true)
-- (Nat , 36)

TypeOfPointedSets : Type₁
TypeOfPointedSets = Σ Type λ X → X


-- "data" lets us define the smallest type with a z and s function.
data N : Type where
  z : N
  s : N → N


threeElement : N
threeElement = s (s (s z))

-- addition
add : N → N → N
add n1 z = n1
add n1 (s n2) = s (add n1 n2)

zleft : ∀ n → add z n ≡ n
zleft z = refl -- refl
zleft (s n') = cong s (zleft n') -- cong s (zleft n')

-- the ≡ type

data S1 : Type where
  base : S1
  loop : base ≡ base


-- agda --bridges allows the following

churchUnit : ∀ {ℓ} → ( (X : Type ℓ) → X → X )  ≃  ⊤
churchUnit = isoToEquiv (iso
                        (λ _ → tt)
                        (λ where _ → λ X x → x)
                        (λ where _ → refl)
                        -- church encoding  is a retract of ⊤, by param
                        λ f → funExt λ A → funExt λ a → -- goal is ∀ (f : (X : Type ℓ) → X → X) A a, a ≡ f A a 
                          param churchUnitNRelator f (Lift ⊤) A (λ _ x → a ≡ x) _ a refl)


churchBool : ∀ {ℓ} → ( (X : Type ℓ) → X → X → X ) ≃ Bool
churchBool = isoToEquiv (iso
                        (λ f → (f (Lift Bool) (lift true) (lift false)) .lower)
                        bool→church
                        (λ where
                          true → refl
                          false → refl)
                        -- church encoding is a retract of Bool, by param
                        λ f → funExt λ A → funExt λ aTrue → funExt λ aFalse → -- goal is  bool→church (church→bool f) A aTrue aFalse ≡ f A aTrue aFalse
                          param churchBoolNRelator f (Lift Bool) A (λ where (lift b) a → bool→church b A aTrue aFalse ≡ a) (lift true) (aTrue) refl (lift false) aFalse refl)
  where
  bool→church = (λ where
                   true → λ X xtrue xfalse → xtrue
                   false → λ X xtrue xfalse → xfalse)


-- we need A to be bdg discr.
-- for instance List Type₀ does not have an encoding
-- because there are too many encodings compared to lists in List Type₀
-- consider foo : ( (X : Type ℓ) → X → (Type₀ → X → X) → X )
--          foo = λ X niil coons → (coons X niil)
-- this encoding uses a type var X in a comp. relevant position.
churchList : ∀ {ℓ} (A : Type ℓ) → (isBDisc A) → ( (X : Type ℓ) → X → (A → X → X) → X ) ≃ List A
churchList {ℓ} A bd =
  isoToEquiv (iso
  churchToList
  listToChurch
  sameList
  -- this retract proof must use param.
  λ chl → funExt λ X → funExt λ niil → funExt λ coons →
  param (churchListNRelator A) chl (List A) X
  (λ as x → listToChurch as X niil coons ≡ x)
  [] niil refl _∷_ coons
    λ a0 a1 abdg as x hyp →
    cong (coons a0) (hyp) ∙
    funExt⁻ (cong coons (invEq (isBDisc→equiv A bd a0 a1) abdg)) x )

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

    -- inpRel : (X : Type ℓ) → X → (A → X → X)

-- module Thing (A : Type) where

--   f : ∀ (X : Type) → X → X

--   g : ∀ (X : Type) → X → X → X -- g ℕ :  ℕ → ℕ → ℕ

--   h : ∀ (X : Type) → X → (A → X → X) → X



--   -- "Church encodings" of inductive data types

--   ChurchUnit : ( (X : Type ) → X → X )  ≃  ⊤

--   ChurchBool : ( (X : Type ) → X → X → X ) ≃ Bool

--   ChurchList : {A : Type} →
--     ( (X : Type ) → X → (A → X → X) → X ) ≃ List A

--   -- In agda --bridges, those bijections can be
--   -- proved from first principles (via parametricity theorem).



--   Bridge : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ  
--   Bridge A a0 a1 = BridgeP (λ _ → A) a0 a1



--   -- two functions are related
--   -- iff
--   -- related inputs map to related outputs.
--   BridgeVsFun : (A B : Type) (f0 f1 : A → B) →
--     Bridge (A → B) f0 f1
--     ≃
--     ( (a0 a1 : A) → Bridge A a0 a1 → Bridge B (f0 a0) (f1 a1) )

--   BridgeVsType : (A0 A1 : Type) →  
--     Bridge Type A0 A1
--     ≃
--     A0 → A1 → Type -- recover "just relations" in the Type case.

--   -- A bridge btw pairs is a pair of bridges.
--   BridgeVsProd : (A B : Type) (a0 a1 : A) (b0 b1 : B) →
--     Bridge (A × B) (a0 , b0) (a1 , b1)
--     ≃
--     (Bridge A a0 a1) × (Bridge B b0 b1)
    





--   BridgeVsFun = {!!}
--   BridgeVsType = {!!}
--   BridgeVsProd = {!!}


--   f = {!!}
--   g = {!!}
--   h = {!!}



--   ChurchUnit = {!!}
--   ChurchBool = {!!}
--   ChurchList = {!!}
