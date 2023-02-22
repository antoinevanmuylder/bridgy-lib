{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
-- -v tc.conv.term:40  -v tc.conv.pathbdg:20 -v tc.conv.atom:50 -v tc.conv.elim:25 -v tc.infer.internal:30 

module Misc where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma using ( ΣPath≃PathΣ ; _×_ ; ΣPathP )
open import Cubical.Data.List
open import Cubical.Foundations.Function


-- yay : ∀ {ℓ} (A  B : Type ℓ) (e : A ≃ B) (a : A) (b : B) →
--           isProp (equivFun e a ≡ b)
-- yay A B e a b p q =
--   let a',r = e .snd .equiv-proof b
--       ≡a,p = a',r .snd (a , p)
--       a,q≡ = sym (a',r .snd (a , q))
--   in
--   {!J (λ !}


-- invEq ΣPath≃PathΣ (a,q≡ ∙ ≡a,p)


-- e .snd .equiv-proof b



-- data myEq {ℓ} (A : Type ℓ) (a0 : A) : A → Set ℓ where
--   myrefl : myEq A a0 a0

-- data myEq' {ℓ} (A : Type ℓ) : A → A → Set ℓ where
--   myrefl' : (a0 : A) → myEq' A a0 a0


-- record myEd {ℓ} (A : Type ℓ) (a0 : A) : A → Type ℓ where
--   coinductive
--   field
--     myrfl : myEd A a0 a0



-- a coinduction pcpl for the Bdg type family?
-- bdg-coind : ∀ {ℓ} {A : Type ℓ}
--   (Ed : A → A → Type ℓ) (edrfl : (a0 : A) → Ed a0 a0) →
--   isContr( Σ (∀ a0 a1 → Ed a0 a1 → BridgeP (λ x → primGel A A Ed x) a0 a1)
--              (λ f → ∀ a0 → f a0 a0 (edrfl a0) ≡ (λ _ → a0)))
-- bdg-coind Ed edrfl =
--   ((λ a0 a1 e → {!λ x → prim^gel {R = Ed} a0 a1 e x!}) ,
--     {!!}) ,
--   {!!}


Type⋆ : ∀ ℓ → Type (ℓ-suc ℓ)
Type⋆ ℓ = Σ (Type ℓ) (λ A → A)

Boolf : (Type⋆ ℓ-zero)
Boolf = (Bool , false)

Boolt : (Type⋆ ℓ-zero)
Boolt = (Bool , true)

IdType⋆ : ∀ {ℓ : Level} (A0 A1 : Type⋆ ℓ) → Type ℓ
IdType⋆ A0 A1 = Σ (A0 .fst ≃ A1 .fst) (λ e → (equivFun e (A0 .snd) ≡ A1 .snd))

myrev : IdType⋆ Boolf Boolt
myrev =
  notEquiv , refl

myrevPth : Boolf ≡ Boolt
myrevPth =
  ΣPathP
  (ua (myrev .fst) , toPathP refl)


hasPtList : ∀ {ℓ} (A : Type⋆ ℓ) → Type ℓ
hasPtList A = List (A .fst)

-- hasPtList acts on structured isos
hasPtList1 : List (Boolf .fst) ≃ List (Boolt .fst)
hasPtList1 = pathToEquiv λ i → hasPtList (myrevPth i)

thing : Unit
thing = {!equivFun hasPtList1  (false ∷ true ∷ []) !}
