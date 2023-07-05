{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --type-in-type #-}

module Bridgy.ChurchGeneric where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.HITs.S1

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Bridgy.NRGRelRecord
open import Bridgy.Param

postulate S : Set
          Sdiscr : ∀ s1 s2 → (s1 ≡ s2) ≃ BridgeP (λ _ → S) s1 s2
          P : S → Set
          Pdiscr : ∀ s1 s2 → (sbdg : BridgeP (λ _ → S) s1 s2) (p1 : P s1) (p2 : P s2) → (subst P (invEq (Sdiscr s1 s2) sbdg) p1 ≡ p2) ≃ BridgeP (λ i → P (sbdg i)) p1 p2

F : ∀ {ℓ} → Set ℓ → Set ℓ
F X = Σ[ s ∈ S ] (P s → X) 

FAlg : Set
FAlg = Σ[ X ∈ Set ] (F X → X)

fmapF : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → F A → F B
fmapF f (s , vs) = s , λ pos → f (vs pos)

ChF : Set
ChF = ∀ (X : Set) → (F X → X) → X

ChFold : F ChF → ChF
ChFold f X red = red (fmapF (λ fp → fp X red) f)

varZero : ∀ {ℓ} → DispNRG ℓ (TypeNRG ℓ)
varZero {ℓ} = Nrelator-DispNRG {ℓ} {ℓ} (idNRelator {ℓ} {TypeNRG ℓ})

PDispNRG : ∀ {ℓ} (Γ : NRGraph ℓ) → DispNRG ℓ-zero (Γ # constDispNRG (discrNRG S Sdiscr))
dcr (PDispNRG Γ) (γ , s) = P s 
dedge (PDispNRG Γ) (γ0 , s0) (γ1 , s1) (γR , eqs) pos0 pos1 = subst P eqs pos0 ≡ pos1
dnativ (PDispNRG Γ) (γ0 , s0) (γ1 , s1) γR = Pdiscr s0 s1 (λ i → snd (γR i))

FNrel : ∀ {ℓ} → NRelator (TypeNRG ℓ) (TypeNRG ℓ)
FNrel {ℓ} = DispNRG-Nrelator {ℓ} {ℓ} (ΣForm (constDispNRG (discrNRG S Sdiscr))
            (→Form (PDispNRG (TypeNRG ℓ)) (wkn-type-by (TypeNRG ℓ) (constDispNRG (discrNRG S Sdiscr)) (varZero {ℓ}))))

ChNRel : NRelator (TypeNRG ℓ-zero) (TypeNRG ℓ-zero)
ChNRel = DispNRG-Nrelator {ℓ-zero} {ℓ-zero} (→Form (→Form (tySubst (TypeNRG ℓ-zero) (TypeNRG ℓ-zero) (FNrel {ℓ-zero}) (varZero {ℓ-zero})) (varZero {ℓ-zero})) (varZero {ℓ-zero}))

ChNRGraph : NRGraph ℓ-zero
ChNRGraph = ΠNRG {ℓ-zero} {ℓ-zero} (TypeNRG ℓ-zero) ChNRel

paramChF : (f : ChF) (A B : Type) (R : A → B → Type)
             (foldA : F A → A) (foldB : F B → B) →
             ((fa : F A) (fb : F B) →
                (Σ (fst fa ≡ fst fb) (λ eqs →
                      (pa : P (fst fa)) (pb : P (fst fb)) → subst P eqs pa ≡ pb → R (snd fa pa) (snd fb pb))) →
                   R (foldA fa) (foldB fb)) →
             R (f A foldA) (f B foldB)
paramChF = param {ℓ-zero} {ℓ-zero} ChNRel

-- transport-domain : 
--   ∀ {A : Set} {B : A → Set} {C : Set} {a1 a2 : A} (eq : a1 ≡ a2) (f : B a1 → C) (v : B a2) →
--   transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v)
-- transport-domain {A} {B} {C} {a1} {a2} eq f v =
--   J (λ a2 eq → (v : B a2) → transport (λ i → B (eq i) → C) f v ≡ f (subst B (sym eq) v))
--   (λ v → cong (λ f → f v) (transportRefl f) ∙ sym (cong f (substRefl {B = B} v))) 
--   eq v 

subst-subst : {A : Set} (B : A → Set) {a1 a2 : A} (eq : a1 ≡ a2) (b : B a2) → subst B eq (subst B (sym eq) b) ≡ b
subst-subst B eq b i = transp (λ j → B (eq (j ∨ i))) i (transp (λ j → B (eq (~ j ∨ i))) i b)

-- ChFinit : (f : ChF) → (FA : FAlg) → f ChF ChFold (fst FA) (snd FA) ≡ f (fst FA) (snd FA)
-- ChFinit f (X , FX) = paramChF f ChF X (λ c x → c X FX ≡ x) ChFold FX help
--   where help : (fa : F ChF) (fb : F X) → Σ[ eq ∈ fst fa ≡ fst fb ]
--                    ((pa : P (fst fa)) (pb : P (fst fb)) →
--                      subst P eq pa ≡ pb → snd fa pa X FX ≡ snd fb pb) → ChFold fa X FX ≡ FX fb
--         help (sf , vsF) (sx , vsX) (eqs , eqvs) =
--           cong FX (cong₂ _,_ eqs (toPathP (funExt λ pb → transport-domain eqs (λ pos → vsF pos X FX) pb ∙ eqvs (subst P (sym eqs) pb) pb (subst-subst P eqs pb))))

ChFalg : Set
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

fold∘ChUnfold : ∀ fp → ChFold (ChUnfold fp) ≡ fp
fold∘ChUnfold fp = funExt (λ X → funExt help)
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

ChUnfold∘fold : ∀ ffp → ChUnfold (ChFold ffp) ≡ ffp
ChUnfold∘fold (s , vs) = cong (s ,_) (funExt λ pos → fold∘ChUnfold (vs pos))
