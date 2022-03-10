{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module NativeReflGraphRelator where

open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
-- open import Cubical.Functions.FunExtEquiv
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma using (_×_ ; ≃-×)
open import Cubical.Foundations.Function


-- By default, we use agda instance arguments (∼ haskell typeclasses) to 
-- handle algebraic strucures such as reflexive graphs.
-- We therefore adopt an external interfacing style: an algebraic object is not a point
-- in a record but rather a carrier with extra structure declared as instances.
--
-- if need be we can pack the carrier with its implementation in
-- a "smart" packed class. See the following example.
module ExampleStruc where

  record HasStuff {ℓ} (A : Type ℓ) : Type where
    field
      stuff : Bool
  open HasStuff ⦃...⦄ public

  record Stuff {ℓ} : Type (ℓ-suc ℓ) where
    constructor mkStuff
    field
      carrier : Type ℓ
      ⦃has-stuff⦄ : HasStuff carrier -- this means that mkStuff : (carrier : Type _) ⦃HasStuff carrier⦄ → Stuff !
  -- open Stuff public   no need for that! mkStuff is already exported


it : ∀ {ℓ} {A : Type ℓ} → {{A}} → A
it {{a}} = a


module NativeReflexiveGraph where

  -- typeclass for native reflexive graphs. we can omit refl edges.
  record HasNRGraph {ℓ} (A : Type ℓ) : Type (ℓ-suc ℓ) where
    field
      nedge : A → A → Type ℓ
      nativ : ∀ (a b : A) → nedge a b ≃ BridgeP (λ _ → A) a b
  open HasNRGraph ⦃...⦄ public

  -- smart packed class version
  record NRGraph ℓ : Type (ℓ-suc ℓ) where
    constructor mkNRGraph
    field
      nrg-carrier : Type ℓ
      ⦃ has-nativergraph ⦄ : HasNRGraph nrg-carrier
open NativeReflexiveGraph public

-- pretty field
_⟦_,_⟧ : ∀ {ℓ} (G : Type ℓ) ⦃ hnrgG : HasNRGraph G ⦄ (g0 g1 : G) → Type ℓ
_⟦_,_⟧ G g0 g1 = nedge g0 g1



module NativeRelator {ℓG ℓH} (G : Type ℓG) (H : Type ℓH) ⦃ hrgG : HasNRGraph G ⦄ ⦃ hrgH : HasNRGraph H ⦄ where

  -- TODO: g0 g1 as explicit arguments instead?
  record HasNRelator (F : G → H) : Type (ℓ-max ℓG ℓH) where
    field
      nrmap : ∀ {g0 g1 : G} → nedge g0 g1 → nedge (F g0) (F g1)
      -- stated as ∀ q : Bdg, .... easier to provide in that dir
      nativ-rel : ∀ {g0 g1 : G} (q : BridgeP (λ _ → G) g0 g1) →
              (nrmap ((invEq (nativ g0 g1) q))) ≡ (invEq (nativ (F g0) (F g1)) (λ x → F (q x)))
  open HasNRelator ⦃...⦄ public


  -- nativ-rel stated as ∀ r : G{g0,g1}, ... instead
  switchNativRelSqu : ∀ (F : G → H) ⦃ hnrF : HasNRelator F ⦄ (g0 g1 : G) →
    (r : nedge g0 g1) → (λ x → F (nativ g0 g1 .fst r x)) ≡ (nativ (F g0) (F g1) .fst (nrmap r))
  switchNativRelSqu F g0 g1 r = sym (cong (nativ (F g0) (F g1) .fst)
                                       (cong nrmap (sym (retEq (nativ g0 g1) r)) ∙
                                       nativ-rel (nativ g0 g1 .fst r))
                                     ∙ secEq (nativ (F g0) (F g1)) _)

  -- packed class for native relators
  record NRelator : Type (ℓ-max ℓG ℓH) where
    constructor mkNRelator
    field
      nr-carrier : G → H
      ⦃ has-nrelator ⦄ : HasNRelator nr-carrier
open NativeRelator public

-- pretty field
_⟦⟧ : ∀ {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hrgG : HasNRGraph G ⦄ ⦃ hrgH : HasNRGraph H ⦄
      (F : G → H) ⦃ hnrF : HasNRelator G H F ⦄ →
      ∀ {g0 g1 : G} → nedge g0 g1 → nedge (F g0) (F g1)
_⟦⟧ F = nrmap




{-
  Next we provide elementary native reflexive graphs and explain how to combine them

  the forward and *backward* maps of `nativ` for a native reflexive
  graph G should be as simple as possible.
  This way, proofs that F : G → _ or F : _ → G is native relator become simpler
-}


-- Type with -logical- relations is a native reflexive graph
-- this is proved using relativity
instance
  TypeHasNRG : ∀ {ℓ} → HasNRGraph (Type ℓ)
  TypeHasNRG = record { nedge = λ A B → (A → B → Type _)
                      ; nativ = λ A B → invEquiv relativity }
TypeNRG : (ℓ : Level) → NRGraph (ℓ-suc ℓ)
TypeNRG ℓ = mkNRGraph (Type ℓ)


-- nRG has binary products
instance
  prodHasNRG : ∀ {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ →
    HasNRGraph (G × H)
  prodHasNRG = record
    { nedge = λ where (g0 , h0) (g1 , h1) → (nedge g0 g1) × (nedge h0 h1)
    ; nativ = λ where (g0 , h0) (g1 , h1) → compEquiv (≃-× (nativ g0 g1) (nativ h0 h1)) ×vsBridgeP }

-- the arrow native relator
instance 
  arrowHasNRelator : ∀ {ℓ} → HasNRelator (Type ℓ × Type ℓ) (Type ℓ) (λ (X , Y) → X → Y)
  arrowHasNRelator = record
    { nrmap = λ (XX , YY) f0 f1 → ∀ x0 x1 → XX x0 x1 → YY (f0 x0) (f1 x1)
    ; nativ-rel = λ q → funExt λ f0 → funExt λ f1 →
        ua (compEquiv
             (equivΠCod λ x0 →
             equivΠCod λ x1 →
             equivΠCod λ xx →
             idEquiv _)
              ΠvsBridgeP) }


-- the diagonal native relator  Type → Type×Type
instance
  diagHasNRelator : ∀{ℓ} → HasNRelator (Type ℓ) (Type ℓ × Type ℓ) (λ X → (X , X))
  diagHasNRelator = record
    { nrmap = λ R → (R , R)
    ; nativ-rel = λ q → refl }


-- native relators do compose
-- starting to wonder if working with typeclasses is really worth it.
-- Those ⦃ r = hnrE ⦄ hints are bads as "r" could change and my code would break


-- compNRelator : ∀ {ℓG ℓH ℓK} (G : NRGraph ℓG) (H : NRGraph ℓH) (K : NRGraph ℓK)
--                (E : NRelator (G .nrg-carrier) (H .nrg-carrier))
--                (F : NRelator (H .nrg-carrier) (K .nrg-carrier)) →
--                NRelator (G .nrg-carrier) (K .nrg-carrier)
-- compNRelator (mkNRGraph G) (mkNRGraph H) (mkNRGraph K) (mkNRelator E hnrE) (mkNRelator F hnrF) =
--   mkNRelator (F ∘ E) (record
--     { nrmap = λ g01 → {!nrmap g01!} ; nativ-rel = {!!} })


-- not declared as instance. else `? : HasNRelator ( P )` wonders if P is a composite
-- this then result in a "too-many candidates" situation
-- compHasNRelator : ∀ {ℓG ℓH ℓK} {G : Type ℓG} {H : Type ℓH} {K : Type ℓK}
--                   {E : G → H} {F : H → K}
--                   ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ ⦃ hnrgK : HasNRGraph K ⦄
--                   ⦃ hnrE : HasNRelator G H E ⦄ ⦃ hnrF : HasNRelator H K F ⦄ →
--                   HasNRelator G K (F ∘ E)
-- compHasNRelator = record { nrmap = λ {g0} {g1} g01 → nrmap (nrmap {g0 = g0} {g1 = g1} g01) ; nativ-rel = {!!} }
-- compHasNRelator = record
--   { nrmap = λ g01 → nrmap (nrmap g01)
--   ; nativ-rel = λ q → cong nrmap (nativ-rel q) ∙ {!!} }
  
