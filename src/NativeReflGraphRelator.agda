{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module NativeReflGraphRelator where

open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (_×_ ; ≃-× ; ≡-×)
open import Cubical.Foundations.Function


-- cubical lemmas
module _ where
  
  equivInj : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (I : A ≃ B) →
    (a a' : A) → I .fst a ≡ I .fst a' → a ≡ a'
  equivInj I a a' prf = sym (retEq I a) ∙ cong (invEq I) prf ∙ (retEq I a')


  switchEquivSqu : ∀ {ℓ ℓ'} {Aleft Aright : Type ℓ} {Bleft Bright : Type ℓ'}
    (Aequiv : Aleft ≃ Aright) (Bequiv : Bleft ≃ Bright) (fleft : Aleft → Bleft) (fright : Aright → Bright) → 
    fleft ∘ (invEq Aequiv) ≡ (invEq Bequiv) ∘ fright → fright ∘ (Aequiv .fst) ≡ (Bequiv .fst) ∘ fleft
  switchEquivSqu Aequiv Bequiv fleft fright hyp =
    sym (equivInj (preCompEquiv (invEquiv Aequiv)) ((Bequiv .fst) ∘ fleft) (fright ∘ (Aequiv .fst))
        (funExt λ a →
        equivFun (equivAdjointEquiv Bequiv)
        (λ i → hyp i a) ∙
        cong fright (sym (secEq Aequiv a)))) 
  
-- functions F have a canonical action on bridges
bdg-action : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} {x0 x1 : X} →
             (F : X → Y) → BridgeP (λ _ → X) x0 x1 → BridgeP (λ _ → Y) (F x0) (F x1)
bdg-action F q = λ x → F (q x)


-- when possible we use instance arguments to infer native rgraph "implementation"
-- todo: isProp nativ ?
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


-- TODO: ℓ's implicit? endpoints implicit in nedgeMap? implicit fields? nativ-rel irrelevant?
-- isProp nativ-rel? (maybe necessary for a propositional η rule)
-- NRelator is just a record - no typeclasses are used
module NativeRelator {ℓG ℓH} (G : Type ℓG) (H : Type ℓH) ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ where

  record NRelator : Type (ℓ-max ℓG ℓH) where
    field
      nobjMap : G → H
      nedgeMap : ∀ {g0 g1 : G} → nedge g0 g1 → nedge (nobjMap g0) (nobjMap g1)
      -- nativeness square. Up to funext, equality says ∀ q : Bdg, bla
      nativ-rel : ∀ (g0 g1 : G) → nedgeMap ∘ invEq (nativ g0 g1) ≡ invEq (nativ (nobjMap g0) (nobjMap g1)) ∘ (bdg-action nobjMap)
  open NRelator public

  -- nativ-rel stated as ∀ r : G{g0,g1}, ... instead
  switchNativeRelSqu : ∀ (F : NRelator) →
    ∀ (g0 g1 : G) → bdg-action (F .nobjMap) ∘ (nativ g0 g1 .fst) ≡ nativ (F .nobjMap g0) (F .nobjMap g1) .fst ∘ F .nedgeMap
  switchNativeRelSqu F g0 g1 = switchEquivSqu (nativ g0 g1) (nativ (F .nobjMap g0) (F .nobjMap g1)) (F .nedgeMap) (bdg-action (F .nobjMap))
                               (F .nativ-rel g0 g1)

  pNativRel : ∀ (F : NRelator) →
    ∀ (g0 g1 : G) (q : BridgeP (λ _ → G) g0 g1) →
              (F .nedgeMap ((invEq (nativ g0 g1) q))) ≡ invEq (nativ (F .nobjMap g0) (F .nobjMap g1)) λ x → F .nobjMap (q x)
  pNativRel F g0 g1 q = cong (λ blank → blank q) (F .nativ-rel g0 g1)
open NativeRelator public

NRelator' : ∀ {ℓG ℓH} (G : NRGraph ℓG) (H : Type ℓH) ⦃ hnrgH : HasNRGraph H ⦄ → Type (ℓ-max ℓG ℓH)
NRelator' (mkNRGraph G) H = NRelator G H



-- {-
--   Next we provide elementary native reflexive graphs and explain how to combine them

--   the forward and *backward* maps of `nativ` for a native reflexive
--   graph G should be as simple as possible.
--   This way, proofs that F : G → _ or F : _ → G is native relator become simpler
-- -}


topBdgDiscrLemma : (q : BridgeP (λ _ → ⊤) tt tt) → (λ _ → tt) ≡ q
topBdgDiscrLemma q = λ i x → isContrUnit .snd (q x) i

topBdgDiscrEquiv : ⊤ ≃ BridgeP (λ _ → ⊤) tt tt
topBdgDiscrEquiv  = isoToEquiv (iso
                      (λ _ _ → tt)
                      (λ _ → tt)
                      (λ q → topBdgDiscrLemma q)
                      λ where tt → refl)

instance
  topHasNRG : HasNRGraph ⊤
  topHasNRG = record { nedge = λ _ _ → ⊤
                     ; nativ = λ where tt tt → topBdgDiscrEquiv}


-- Type with -logical- relations is a native reflexive graph
-- this is proved using relativity
instance
  TypeHasNRG : ∀ {ℓ} → HasNRGraph (Type ℓ)
  TypeHasNRG = record { nedge = λ A B → (A → B → Type _)
                      ; nativ = λ A B → relativity }


-- nRG has binary products
instance
  prodHasNRG : ∀ {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ →
    HasNRGraph (G × H)
  prodHasNRG = record
    { nedge = λ where (g0 , h0) (g1 , h1) → (nedge g0 g1) × (nedge h0 h1)
    ; nativ = λ where (g0 , h0) (g1 , h1) → compEquiv (≃-× (nativ g0 g1) (nativ h0 h1)) ×vsBridgeP }

-- nRG has exponentials. H^G = NRelator G H.
module Exponentials {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ where

  -- record NRelator-logrel {ℓ} (E F : NRelator G H)  : Type _ where
  --   field
  --     objrel : G → H → Type ℓ
  --     edgerel : ∀ (g g' : G) (h h' : H) (gh : objrel g h) (gh' : objrel g' h') → edge g g' → edge h h' → Type ℓ

  -- instance
  --   nrelHasNRGraph : HasNRGraph (NRelator G H)
  --   nrelHasNRGraph = record
  --     { nedge = {!!} ; nativ = {!!} }

-- the identity native relator
idNRelator : ∀ {ℓ} {G : Type ℓ} ⦃ hnrgG : HasNRGraph G ⦄ → NRelator G G
idNRelator = record
  { nobjMap = λ g → g
  ; nedgeMap = λ e → e
  ; nativ-rel = λ g0 g1 → refl }

-- universal pty of product in NRGraph (1 direction, the "useful" one)
⟨_,_⟩nrel :  ∀ {ℓG ℓH ℓK} {G : Type ℓG} {H : Type ℓH} {K : Type ℓK}
            ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ ⦃ hnrgK : HasNRGraph K ⦄ →
            NRelator G H → NRelator G K → NRelator G (H × K)
⟨_,_⟩nrel E F = record
  { nobjMap = λ g → (E .nobjMap g , F .nobjMap g)
  ; nedgeMap = λ e → ( E .nedgeMap e , F .nedgeMap e)
  ; nativ-rel = λ g0 g1 → funExt λ q → ≡-× (pNativRel _ _ E g0 g1 q) (pNativRel _ _ F g0 g1 q)  }


-- the arrow native relator
arrowNRelator : ∀ {ℓ} → NRelator (Type ℓ × Type ℓ) (Type ℓ)
arrowNRelator = record
  { nobjMap = λ where (X , Y) → (X → Y)
  ; nedgeMap = λ where (XX , YY) f0 f1 → ∀ x0 x1 → XX x0 x1 → YY (f0 x0) (f1 x1)
  ; nativ-rel = λ where
      (X0 , Y0) (X1 , Y1) → funExt λ q → funExt λ f0 → funExt λ f1 →
        ua (flip compEquiv ΠvsBridgeP
        (equivΠCod λ x0 →
        equivΠCod λ x1 →
        equivΠCod λ xx →
        idEquiv _))  }

-- the diagonal native relator  Type → Type×Type
diagNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ × Type ℓ)
diagNRelator = record
  { nobjMap = λ X → (X , X)
  ; nedgeMap = λ XX → (XX , XX)
  ; nativ-rel = λ X0 X1 → refl }


-- native relators do compose
compNRelator : ∀ {ℓG ℓH ℓK} {G : Type ℓG} {H : Type ℓH} {K : Type ℓK}
               ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ ⦃ hnrgK : HasNRGraph K ⦄
               (E : NRelator G H) (F : NRelator H K) → NRelator G K
compNRelator E F = record
  { nobjMap = F .nobjMap  ∘ E .nobjMap
  ; nedgeMap = λ g01 → F .nedgeMap (E .nedgeMap g01)
  -- diagram chasing!
  ; nativ-rel = λ g0 g1 → ∘-assoc (F .nedgeMap) (E .nedgeMap) (invEq (nativ g0 g1)) ∙
                          cong (λ blank → F .nedgeMap ∘ blank) (E .nativ-rel g0 g1) ∙
                          sym (∘-assoc (F .nedgeMap) (invEq (nativ (E .nobjMap g0) (E .nobjMap g1))) (bdg-action (E .nobjMap))) ∙
                          cong (λ blank → blank ∘ (bdg-action (E .nobjMap))) (F .nativ-rel (E .nobjMap g0) (E .nobjMap g1) ) ∙
                          funExt λ q →  refl}
  
-- example: X ↦ X → X relator
churchUnitNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ)
churchUnitNRelator = compNRelator diagNRelator arrowNRelator

-- example: X ↦ X → X → X relator
churchBoolNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ)
churchBoolNRelator = compNRelator ( ⟨ idNRelator , churchUnitNRelator ⟩nrel ) arrowNRelator
