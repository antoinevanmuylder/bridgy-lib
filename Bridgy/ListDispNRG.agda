{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ListDispNRG where

open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma using ( _×_ )

{-

we define the displayed NRG  A:Type ⊢ List A dnrg
we first need a (displayed ) commutation principle Bridge vs Lists

-}

constNRelator : ∀ {ℓG ℓH} {G : NRGraph ℓG} {H : NRGraph ℓH} (h : H .nrg-cr) → NRelator G H
constNRelator {G = G} {H = H} h = record {
  nobjMap = λ _ → h ;
  nedgeMap = λ  _ → invEq (H .nativ h h) (λ _ → h) ;
  nativ-rel = λ g0 g1 → refl }

-- churchListNRelator A = λ X → X → (A → X → X) → X
churchListNRelator : ∀ {ℓ} (A : Type ℓ) → NRelator (TypeNRG ℓ) (TypeNRG ℓ)
churchListNRelator {ℓ} A =
  let XtoX→X = compNRelator {G = TypeNRG ℓ} {H = (TypeNRG ℓ) ×NRG (TypeNRG ℓ)} {K = TypeNRG ℓ}
                  diagNRelator arrowNRelator
      XtoA→X→X = compNRelator {G = TypeNRG ℓ} {H = (TypeNRG ℓ) ×NRG (TypeNRG ℓ)} {K = TypeNRG ℓ}
                         ⟨ constNRelator {G = TypeNRG ℓ} {H = TypeNRG ℓ} A , XtoX→X ⟩nrel arrowNRelator
      XtoA→X→X-→X = compNRelator {G = TypeNRG ℓ} {H = (TypeNRG ℓ) ×NRG (TypeNRG ℓ)} {K = TypeNRG ℓ}
                         ⟨ XtoA→X→X , idNRelator {G = TypeNRG ℓ}  ⟩nrel arrowNRelator
  in compNRelator {G = TypeNRG ℓ} {H = (TypeNRG ℓ) ×NRG (TypeNRG ℓ)} {K = TypeNRG ℓ}
       ⟨ idNRelator {G = TypeNRG ℓ} , XtoA→X→X-→X  ⟩nrel arrowNRelator


-- churchList : ∀ {ℓ} (A : Type ℓ) → ( (X : Type ℓ) → X → (A → X → X) → X ) ≃ List A
-- churchList {ℓ} A = isoToEquiv (iso
--                  churchToList
--                  listToChurch
--                  sameList
--                  -- this retract proof must use param.
--                  λ chl → funExt λ X → funExt λ d → funExt λ f → {!param!})

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

-- List { as0, as1 }# R
-- inspired from the encode-decode technique of List.Properties


-- ListRCover : ∀ {ℓ} (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) → List A0 → List A1 → Type ℓ
-- ListRCover A0 A1 R [] [] = Lift Unit
-- ListRCover A0 A1 R [] (_ ∷ _) = Lift ⊥
-- ListRCover A0 A1 R (_ ∷ _) [] = Lift ⊥
-- ListRCover A0 A1 R (a0 ∷ as0) (a1 ∷ as1) = R a0 a1 × ListRCover A0 A1 R as0 as1



-- ListDispNRG : ∀ {ℓ} → DispNRG ℓ (TypeNRG ℓ)
-- ListDispNRG = record {
--   dcr = List ;
--   dedge = λ A0 A1 R → ListRCover A0 A1 R ;
--   dnativ = λ A0 A1 Abdg as0 as1 → {!!} } -- het bridges of lists
