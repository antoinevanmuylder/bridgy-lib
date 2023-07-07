{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --type-in-type #-}

module Bridgy.ChurchGenericFixpoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.HITs.S1

open import Bridgy.BridgePrims
open import Bridgy.BDisc
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Bridgy.NRGRelRecord
open import Bridgy.Param

-- Note: this file relies on type-in-type so we can apply the Church fixpoint to itself

postulate S : Set
          Sdiscr : isBDisc S
          P : S → Set
          Pdiscr : ∀ s1 s2 → (sbdg : BridgeP (λ _ → S) s1 s2) (p1 : P s1) (p2 : P s2) → (subst P (invEq (isBDisc→equiv S Sdiscr s1 s2) sbdg) p1 ≡ p2) ≃ BridgeP (λ i → P (sbdg i)) p1 p2

open ParamDNRG

SB : BDisc ℓ-zero
SB = S , Sdiscr

SNRG : NRGraph ℓ-zero
SNRG = discrNRG SB

SDispNRG : ∀ {ℓ} {Γ : NRGraph ℓ} → DispNRG ℓ-zero Γ
SDispNRG = constDispNRG SNRG

F : ∀ {ℓ} → Set ℓ → Set ℓ
F X = Σ[ s ∈ S ] (P s → X) 

FAlg : Set₁
FAlg = Σ[ X ∈ Set ] (F X → X)

fmapF : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → F A → F B
fmapF f (s , vs) = s , λ pos → f (vs pos)

ChF : Set₁
ChF = ∀ (X : Set) → (F X → X) → X -- Suggestion by Antoine: quantify over hSets?

ChFold : F ChF → ChF
ChFold f X red = red (fmapF (λ fp → fp X red) f)

varZero : DispNRG ℓ-zero (TypeNRG ℓ-zero)
varZero = Nrelator-DispNRG {ℓ-zero} {ℓ-zero} (idNRelator {ℓ-zero})

PDispNRG : ∀ {ℓ} (Γ : NRGraph ℓ) → DispNRG ℓ-zero (Γ # SDispNRG)
dcr (PDispNRG Γ) (γ , s) = P s 
dedge (PDispNRG Γ) (γ0 , s0) (γ1 , s1) (γR , eqs) pos0 pos1 = subst P eqs pos0 ≡ pos1
dnativ (PDispNRG Γ) (γ0 , s0) (γ1 , s1) γR = Pdiscr s0 s1 (λ i → snd (γR i))

FNrel : NRelator (TypeNRG ℓ-zero) (TypeNRG ℓ-zero)
FNrel = DispNRG-Nrelator {ℓ-zero} {ℓ-zero} {_} (ΣForm {ℓ-zero} {ℓ-zero} {_} {_} SDispNRG
            (→Form (PDispNRG (TypeNRG ℓ-zero)) (wkn-type-by (TypeNRG ℓ-zero) SDispNRG varZero)))

ChDNRG : DispNRG ℓ-zero (TypeNRG ℓ-zero)
ChDNRG = →Form (→Form (tySubst (TypeNRG ℓ-zero) (TypeNRG ℓ-zero) FNrel varZero) varZero) varZero

-- ChNRel : NRelator (TypeNRG ℓ-zero) (TypeNRG ℓ-zero)
-- ChNRel = DispNRG-Nrelator {ℓ-zero} {ℓ-zero} ChDNRG

-- ChNRGraph : NRGraph ℓ-zero
-- ChNRGraph = ΠNRG {ℓ-zero} {ℓ-zero} (TypeNRG ℓ-zero) ChNRel

paramChF : (f : ChF) (A B : Type) (R : A → B → Type)
             (foldA : F A → A) (foldB : F B → B) →
             ((fa : F A) (fb : F B) →
                (Σ (fst fa ≡ fst fb) (λ eqs →
                      (pa : P (fst fa)) (pb : P (fst fb)) → subst P eqs pa ≡ pb → R (snd fa pa) (snd fb pb))) →
                   R (foldA fa) (foldB fb)) →
             R (f A foldA) (f B foldB)
paramChF = param' {ℓ-zero} (TypeNRG ℓ-zero) ChDNRG

transport-domain : 
  ∀ {A : Set} {B : A → Set} {C : Set} {a1 a2 : A} (eq : a1 ≡ a2) (f : B a1 → C) (v : B a2) →
  transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v)
transport-domain {A} {B} {C} {a1} {a2} eq f v =
  J (λ a2 eq → (v : B a2) → transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v))
  (λ v → cong (λ f → f v) (transportRefl f) ∙ sym (cong f (substRefl {B = B} v))) 
  eq v 

subst-subst : {A : Set} (B : A → Set) {a1 a2 : A} (eq : a1 ≡ a2) (b : B a2) → subst B eq (subst B (sym eq) b) ≡ b
subst-subst B eq b i = transp (λ j → B (eq (j ∨ i))) i (transp (λ j → B (eq (~ j ∨ i))) i b)


ChFinit : (f : ChF) → (FA : FAlg) → f ChF ChFold (fst FA) (snd FA) ≡ f (fst FA) (snd FA)
ChFinit f (X , FX) = paramChF f ChF X (λ c x → c X FX ≡ x) ChFold FX help
  where help : (fa : F ChF) (fb : F X) → Σ[ eq ∈ fst fa ≡ fst fb ]
                   ((pa : P (fst fa)) (pb : P (fst fb)) →
                     subst P eq pa ≡ pb → snd fa pa X FX ≡ snd fb pb) → ChFold fa X FX ≡ FX fb
        help (sf , vsF) (sx , vsX) (eqs , eqvs) =
          cong FX (cong₂ _,_ eqs (toPathP (funExt λ pb → transport-domain eqs (λ pos → vsF pos X FX) pb ∙ eqvs (subst P (sym eqs) pb) pb (subst-subst P eqs pb))))

ChFalg : Set₁
ChFalg = Σ[ X ∈ Set ] (F X → X)

chFAlg : ChFalg
chFAlg = ChF , ChFold

FMorph : FAlg -> FAlg → Set
FMorph (X , foldX) (Y , foldY) = Σ[ f ∈ (X → Y) ] (f ∘ foldX ≡ foldY ∘ fmapF f)

initMorph : (XA : FAlg) → FMorph chFAlg XA
initMorph (X ,  foldX) = (λ ch → ch X foldX) , refl 

initMorphUnique : (XA : FAlg) → (f : FMorph chFAlg XA) → fst (initMorph XA) ≡ fst f 
initMorphUnique (X , foldX) (fm , fmcom) = {!!}

ChUnfold : ChF → F ChF
ChUnfold fp = fp (F ChF) (fmapF ChFold)

ChFold∘ChUnfold : ∀ fp → ChFold (ChUnfold fp) ≡ fp
ChFold∘ChUnfold fp = funExt (λ X → funExt help)
  where 
    help2 : {X : Set} (FX : F X → X) (fa : F (F ChF)) (fb : F X) →
            Σ[ eq ∈ fst fa ≡ fst fb ]
              ((pa : P (fst fa)) (pb : P (fst fb)) →
                subst P eq pa ≡ pb →
                FX (fmapF (λ ch → ch X FX) (snd fa pa)) ≡ snd fb pb) →
            FX (fmapF (λ ch → ch X FX) (fmapF ChFold fa)) ≡ FX fb
    help2 {X} FX (sa , vsa) (sb , vsb) (eqs , eqvs) =
      cong FX (cong₂ _,_ eqs (toPathP (funExt λ pb → 
      fromPathP (eqvs (subst P (sym eqs) pb) pb (subst-subst P eqs pb)))))
    help : {X : Set} (FX : F X → X) → FX (fmapF (λ ch → ch X FX) (fp (F ChF) (fmapF ChFold))) ≡ fp X FX
    help {X} foldX = paramChF fp (F ChF) X (λ c x → foldX (fmapF (λ ch → ch X foldX) c) ≡ x) (fmapF ChFold) foldX (help2 foldX)

ChUnfold∘ChFold : ∀ ffp → ChUnfold (ChFold ffp) ≡ ffp
ChUnfold∘ChFold (s , vs) = cong (s ,_) (funExt λ pos → ChFold∘ChUnfold (vs pos))

ChFFixpointIso : Iso (F ChF) ChF
Iso.fun ChFFixpointIso = ChFold
Iso.inv ChFFixpointIso = ChUnfold
Iso.rightInv ChFFixpointIso = ChFold∘ChUnfold
Iso.leftInv ChFFixpointIso = ChUnfold∘ChFold

ChFFixpoint : F ChF ≃ ChF
ChFFixpoint = isoToEquiv ChFFixpointIso
