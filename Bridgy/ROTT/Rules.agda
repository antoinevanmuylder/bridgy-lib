{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.Rules where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma


------------------------------------------------------------------------
-- Some NRGs

topBdgDiscrLemma : (q : BridgeP (λ _ → Unit) tt tt) → (λ _ → tt) ≡ q
topBdgDiscrLemma q = λ i x → isContrUnit .snd (q x) i

topBdgDiscrEquiv : Unit ≃ BridgeP (λ _ → Unit) tt tt
topBdgDiscrEquiv  = isoToEquiv (iso
                      (λ _ _ → tt)
                      (λ _ → tt)
                      (λ q → topBdgDiscrLemma q)
                      λ where tt → refl)

topNRG : NRGraph ℓ-zero
topNRG .nrg-cr = Unit
topNRG .nedge  = (λ _ _ → Unit)
topNRG .nativ  = (λ where tt tt → topBdgDiscrEquiv)

-- -- Type with -logical- relations is a native reflexive graph
-- -- this is proved using relativity
TypeNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
TypeNRG ℓ .nrg-cr = Type ℓ
TypeNRG ℓ .nedge  = λ A0 A1 → (A0 → A1 → Type ℓ)
TypeNRG ℓ .nativ  = λ A0 A1 → relativity



-- -- nRG has binary products
_×NRG_ : ∀{ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) → NRGraph (ℓ-max ℓG ℓH)
_×NRG_ G H .nrg-cr = G .nrg-cr × H .nrg-cr
_×NRG_ G H .nedge (g0 , h0) (g1 , h1)  = G .nedge g0 g1 × H .nedge h0 h1
_×NRG_ G H .nativ  (g0 , h0) (g1 , h1) = flip compEquiv ×vsBridgeP (≃-× (G .nativ g0 g1) (H .nativ h0 h1))




------------------------------------------------------------------------
-- Some native relators




------------------------------------------------------------------------
-- Rules involving dNRGs


-- Ty subst
-- σ : Γ → Δ    Δ ⊢ A type
-- ------------------------
-- Γ ⊢ A type
tySubst : ∀ {ℓΓ ℓΔ ℓ} (Γ : NRGraph ℓΓ) (Δ : NRGraph ℓΔ) →
            (NRelator Γ Δ) → (DispNRG ℓ Δ) → 
            DispNRG ℓ Γ
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dcr g = A .dcr ( σ .nrel0 g )
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dedge g0 g1 gg = A .dedge (σ .nrel0 g0) (σ .nrel0 g1) (σ .nrel1 _ _ gg) 
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dnativ g0 g1 gg gbdg gprf a0 a1 =
  A .dnativ (σ .nrel0 g0) (σ .nrel0 g1) (σ .nrel1 _ _ gg) (λ x → σ .nrel0 (gbdg x))
  (σ .nativ-rel _ _ gg gbdg gprf)
  a0 a1

-- Γ ctx
-- Γ ⊢ A type
-- ----------
-- Γ.A ctx
_#_ : ∀ {ℓ ℓ'} (Γ : NRGraph ℓ) (A : DispNRG ℓ' Γ) → NRGraph (ℓ-max ℓ ℓ')
_#_ Γ A .nrg-cr = Σ (Γ .nrg-cr) (A .dcr)
_#_ Γ A .nedge (g0 , a0) (g1 , a1) = Σ (Γ ⦅ g0 , g1 ⦆) (λ gg → A ⦅ a0 , a1 ⦆# gg)
_#_ Γ A .nativ (g0 , a0) (g1 , a1) =
  flip compEquiv ΣvsBridgeP
  (Σ-cong-equiv (Γ .nativ g0 g1) λ gg →
  A .dnativ _ _ gg (equivFun (Γ .nativ g0 g1) gg) (inEquGr _ _ _ refl) a0 a1)


infixl 40 _#_

