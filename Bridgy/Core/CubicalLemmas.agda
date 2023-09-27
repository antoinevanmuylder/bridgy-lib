------------------------------------------------------------------------
-- When are 2 sigma/pi types equivalent?
------------------------------------------------------------------------
{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.CubicalLemmas where

open import Bridgy.Core.EquGraph
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit


module _ {lA lB : Level} (A A' : Type lA) (B : A → Type lB) (B' : A' → Type lB) where


  -- Σ-cong-equiv : (e : A ≃ A')
  --              → ((x : A) → B x ≃ B' (equivFun e x))
  --              → Σ A B ≃ Σ A' B'
  -- Σ-cong-equiv e e' = isoToEquiv (Σ-cong-iso (equivToIso e) (equivToIso ∘ e'))

  -- a 2-ary version of the above
  Σ-cong-equiv-2ary : (eA : A ≃ A') →
    ((a : A) (a' : A') (aprf : a [ eA ] a') → B a ≃ B' a') →
    Σ A B ≃ Σ A' B'
  Σ-cong-equiv-2ary eA ptEqu =
    Σ-cong-equiv eA λ a →
    ptEqu a (equivFun eA a) (inEquGr refl) 


module _ {ℓ} {A : I → Type ℓ} {new0 old0 : A i0} {new1 old1 : A i1} where

  change-pathp-endpoints : (p0 : new0 ≡ old0) (p1 : new1 ≡ old1) →
                     PathP A new0 new1 → PathP A old0 old1
  change-pathp-endpoints p0 p1 pth = transport (λ i → PathP A (p0 i) (p1 i)) pth

module _ {ℓA ℓB} (A : I → Type ℓA) (B : I → Type ℓB)
                      (a0 : A i0) (a1 : A i1) where

  change-line-pathp : ( nat : (i : I) → A i → B i ) → (PathP A a0 a1) →
              PathP B (nat i0 a0) (nat i1 a1)
  change-line-pathp nat p = λ x → nat x (p x)


still-equal : ∀ {l} {A : Type l} {a0 a1 : A} →
  (p : a0 ≡ a1) → (k : I) → a0 ≡ p k
still-equal p k = λ i → p ( i ∧ k)

-- module _ {l : Level} {A : I → Type l} {B : (i : I) → A i → Type l}
--   (f0 : (a : A i0) → B i0 a) (f1 : (a : A i1) → B i1 a) where

--   funExtP-2ary :
--     ( ∀ (a0 : A i0) (a1 : A i1) (aa : PathP (λ i → A i) a0 a1) → PathP (λ i → B i (aa i)) (f0 a0) (f1 a1) ) →
--     PathP (λ i → (a : A i) → B i a) f0 f1
--   funExtP-2ary hyp i a = {!!}
 

module ChangeLineEquiv {l : Level} (A A' : I → Type l) (AtoA' : (i : I) → A i ≡ A' i)
  {a0 : A i0} {a1 : A i1} {a0' : A' i0} {a1' : A' i1} (hyp0 : PathP (λ j → AtoA' i0 j) a0 a0') (hyp1 : PathP (λ j → AtoA' i1 j) a1 a1') where

  PathP≡PathP : PathP (λ i → A i) a0 a1 ≡ PathP (λ i → A' i) a0' a1'
  PathP≡PathP = λ k → PathP (λ i → AtoA' i k) (hyp0 k) (hyp1 k)

open ChangeLineEquiv public
