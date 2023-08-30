{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.Rules where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma


------------------------------------------------------------------------
-- lemmas

funExt2⁻ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → A → I → Type ℓ'}
  {f : (x y : A) → B x y i0} {g : (x y : A) → B x y i1} →
  (x y : A) →
  PathP (λ i → (x y : A) → B x y i) f g →
  PathP (B x y) (f x y) (g x y)
funExt2⁻ x y eq = λ i → eq i x y


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

-- Γ ⊢ A type   Γ ⊢ B type
-- ------------------------
-- Γ ⊢ A → B type
→Form : ∀ {ℓ} {Γ : NRGraph ℓ}
  (lA : Level) (A : DispNRG lA Γ) (lB : Level) (B : DispNRG lB Γ) → 
  DispNRG (ℓ-max lA lB) Γ
→Form lA A lB B .dcr g = (A .dcr g) → (B .dcr g)
→Form lA A lB B .dedge g0 g1 gg f0 f1 = ∀ a0 a1 → A ⦅ a0 , a1 ⦆# gg → B ⦅ f0 a0 , f1 a1 ⦆# gg
→Form lA A lB B .dnativ g0 g1 gg gbdg gprf f0 f1 =
  flip compEquiv ΠvsBridgeP
  (equivΠCod λ a0 → equivΠCod λ a1 →
  equivΠ' (A .dnativ g0 g1 gg gbdg gprf a0 a1) λ {aa} {abdg} aprf →
  B .dnativ g0 g1 gg gbdg gprf (f0 a0) (f1 a1) )

-- -----------------
-- Γ ⊢ U(l) type(l+1)
UForm : ∀ {l} {Γ : NRGraph l} (lU : Level) → DispNRG (ℓ-suc lU) Γ
UForm lU .dcr _ = Type lU
UForm lU .dedge _ _ _ A0 A1 = A0 → A1 → Type lU
UForm lU .dnativ _ _ _ _ _ A0 A1 = relativity


-- Formation rule for the El type
--
-- Γ ⊢ C : U(lC)
-- -----------------
-- Γ ⊢ El C  type(lC)
El : ∀ {l} {Γ : NRGraph l} {lC} → TermDNRG Γ (UForm lC) → DispNRG lC Γ
El c .dcr g = c .tm0 g
El c .dedge g0 g1 gg c0 c1 = c .tm1 g0 g1 gg c0 c1
-- c .tm-nativ gives a ≡, displayed nativeness asks for a ≃.
El c .dnativ g0 g1 gg gbdg gprf c0 c1 =
  let z = (outEquGrInv _ _ _ (c .tm-nativ g0 g1 gg gbdg gprf)) in
  mypathToEquiv (funExt⁻ (funExt⁻ z c0) c1)
