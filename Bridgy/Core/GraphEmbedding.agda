{-# OPTIONS --cubical #-}


----------------------------------------------------------------------
-- - Equivalences are relations with contractible fibers and cofibers (eqsAsRels)
-- - Functions are relations with contractible cofibers (funsAsRels)
-- - Relations are relations
-- - Thus (A0 ≃ A1) ↪ (A0 → A1) and (A0 → A1) ↪ (A0 → A1 → Type l)
--   and hence (A0 ≃ A1) ↪ (A0 → A1 → Type l)

-- In fact there is an embedding Path A a0 a1 ↪ Bridge A a0 a1 (see BDisc.agda)
----------------------------------------------------------------------


module GraphEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
--open import Bridgy.Core.MyPathToEquiv

----------------------------------------------------------------
-- (A0 ≃ A1) ↪ (A0 → A1)
----------------------------------------------------------------

equivFun-embedding : ∀ {l} {A0 A1 : Type l} → (A0 ≃ A1) ↪ (A0 → A1)
equivFun-embedding = equivFun , isEmbd-equivFun

  where
    
    isEmbd-equivFun : ∀ {l} {A0 A1 : Type l} → isEmbedding (equivFun {l} {l} {A0} {A1})
    isEmbd-equivFun {l} {A0} {A1} = λ e0 e1 →
      isEmbeddingFstΣProp {A = A0 → A1} {B = isEquiv} isPropIsEquiv {u = e0} {v = e1}



----------------------------------------------------------------
-- And   (A0 → A1) ↪ (A0 → A1 → Type l)
----------------------------------------------------------------

Grfun : ∀ {l} {A0 A1 : Type l} → (A0 → A1) → A0 → A1 → Type l
Grfun f = λ a0 a1 → f a0 ≡ a1

hasContrCofibers : ∀ {l} {A0 A1 : Type l} (R : A0 → A1 → Type l) → Type l
hasContrCofibers R = ∀ a0 → isContr (Σ[ a1 ∈ _ ] (R a0 a1))

isPropHasContrCofibers : ∀ {l} {A0 A1 : Type l} (R : A0 → A1 → Type l) →
  isProp ( hasContrCofibers R )
isPropHasContrCofibers {l} {A0} {A1} R =
  isPropΠ λ a0 → isPropIsContr

funsAsRels : ∀ {l} {A0 A1 : Type l} →
  (Σ[ R ∈ (A0 → A1 → Type l) ] hasContrCofibers R)
  ≃ (A0 → A1)
funsAsRels {l} {A0} {A1} = isoToEquiv (iso
  rel2fun
  fun2rel
  (λ _ → refl)
  retPrf)

  where

    rel2fun : (Σ[ R ∈ (A0 → A1 → Type l) ] hasContrCofibers R) → A0 → A1
    rel2fun (R , ctr) a0 = ctr a0 .fst .fst

    fun2rel  : (A0 → A1) → (Σ[ R ∈ (A0 → A1 → Type l) ] hasContrCofibers R)
    fun2rel f = Grfun f , λ a0 → isContrSingl (f a0)

    retPrf : retract rel2fun fun2rel
    retPrf (R , ctr) = equivFun (Σ≡PropEquiv {A = A0 → A1 → Type l} {B = hasContrCofibers} (λ R → isPropHasContrCofibers R))
      (funExt λ a0 → funExt λ a1 → ua (recognizeId (R a0) (ctr a0 .fst .snd) (ctr a0) a1) )


relContrCofib-embedding : ∀ {l} {A0 A1 : Type l} → (Σ[ R ∈ (A0 → A1 → Type l) ] hasContrCofibers R) ↪ (A0 → A1 → Type l)
relContrCofib-embedding {l} {A0} {A1} = fst , λ u v → isEmbeddingFstΣProp {A = A0 → A1 → Type l} {B = hasContrCofibers} isPropHasContrCofibers


Grfun-embedding : ∀ {l} {A0 A1 : Type l} → (A0 → A1) ↪ (A0 → A1 → Type l)
Grfun-embedding {l} {A0} {A1} = compEmbedding (relContrCofib-embedding {l} {A0} {A1}) (Equiv→Embedding (invEquiv (funsAsRels {l} {A0} {A1})))

----------------------------------------------------------------
-- Thus   (A0 ≃ A1) ↪ (A0 → A1 → Type l)
----------------------------------------------------------------

GrEquiv-embedding : ∀ {l} {A0 A1 : Type l} → (A0 ≃ A1) ↪ (A0 → A1 → Type l)
GrEquiv-embedding {l} {A0} {A1} = compEmbedding (Grfun-embedding {l} {A0} {A1}) (equivFun-embedding {l} {A0} {A1})

----------------------------------------------------------------
-- (A0 ≃ A1) ≃ (R : A0 → A1 → Type l) × hasContrCofibers R × hasContrFibers R
----------------------------------------------------------------    

hasContrFibers : ∀ {l} {A0 A1 : Type l} → (R : A0 → A1 → Type l) → Type l
hasContrFibers {l} {A0} {A1} R = ∀ a1 → isContr( Σ[ a0 ∈ A0 ] R a0 a1)

isPropHasContrFibers : ∀ {l} {A0 A1 : Type l} → (R : A0 → A1 → Type l) →
  isProp (hasContrFibers R)
isPropHasContrFibers R = isPropΠ λ a1 → isPropIsContr

lemma1 : ∀ {l} {A0 A1 : Type l} →
  (Σ[ Rctr ∈ (Σ (A0 → A1 → Type l) hasContrCofibers) ] hasContrFibers (Rctr .fst))
  ≃
  (Σ[ R ∈ (A0 → A1 → Type l) ] (hasContrCofibers R) × (hasContrFibers R))
lemma1 {l} {A0} {A1} = (Σ-assoc-≃ {A = (A0 → A1 → Type l)} {B = hasContrCofibers} {C = λ R _ → hasContrFibers R})

lemma2 : ∀ {l} {A0 A1 : Type l} →
  (Σ[ Rctr ∈ (Σ (A0 → A1 → Type l) hasContrCofibers) ] hasContrFibers (Rctr .fst))
  ≃
  (Σ[ f ∈ (A0 → A1) ] hasContrFibers (Grfun f))
lemma2 {l} {A0} {A1} = Σ-cong-equiv funsAsRels eqProps -- eqProps

  where

    eqProps : (R : Σ (A0 → A1 → Type l) hasContrCofibers) → hasContrFibers (R .fst) ≃ hasContrFibers (Grfun (equivFun funsAsRels R))
    eqProps (R , ctr) =
      pathToEquiv (cong hasContrFibers λ i → (retEq funsAsRels (R , ctr)) (~ i) .fst)

lemma3 : ∀ {l} {A0 A1 : Type l} →
  (Σ[ R ∈ (A0 → A1 → Type l) ] (hasContrCofibers R) × (hasContrFibers R))
  ≃
  (Σ[ f ∈ (A0 → A1) ] hasContrFibers (Grfun f))
lemma3 {l} {A0} {A1} = compEquiv (invEquiv lemma1) lemma2



eqsAsRels : ∀ {l} {A0 A1 : Type l} →
  (Σ[ R ∈ (A0 → A1 → Type l) ] (hasContrCofibers R) × (hasContrFibers R))
  ≃
  (A0 ≃ A1)
eqsAsRels {l} {A0} {A1} = compEquiv lemma3 (Σ-cong-equiv-snd λ f →
  propBiimpl→Equiv (isPropHasContrFibers _) (isPropIsEquiv _)
  (λ lhs → record { equiv-proof = λ a1 → (lhs a1 .fst .fst , lhs a1 .fst .snd) , lhs a1 .snd })
  λ rhs → rhs .equiv-proof)

    

