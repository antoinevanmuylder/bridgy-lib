{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.prim.extent:30 #-}
module Cubical.Bridges.GelExamplesAndreas where

open import Cubical.Bridges.BridgePrims
open import Cubical.Bridges.BridgeExamples
open import Cubical.Bridges.ExtentExamples
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Base using (idEquiv)
open import Cubical.Foundations.Equiv

-- ------------------------------------------------------------------------
-- -- Gel Types
-- ------------------------------------------------------------------------

_∋_ : ∀{ℓ} → (A : Type ℓ) → A → A
A ∋ a = a

module PlayGel {ℓ} {A0 A1 : Type ℓ} {R : A0 → A1 → Type ℓ} where

  -- BOUNDARY for Gel type
  boundary0-Gel : primGel A0 A1 R bi0 ≡ A0
  boundary0-Gel i = A0

  boundary1-Gel : primGel A0 A1 R bi1 ≡ A1
  boundary1-Gel i = A1


  -- BOUNDARY for gel
  boundary0-gel : (M0 : A0) (M1 : A1) (P : R M0 M1) → prim^gel {R = R} M0 M1 P bi0 ≡ M0
  boundary0-gel M0 M1 P i = M0

  boundary1-gel : (M0 : A0) (M1 : A1) (P : R M0 M1) → prim^gel {R = R} M0 M1 P bi1 ≡ M1
  boundary1-gel M0 M1 P i = M1


  -- BETA RULE for Gel
  ungel-gel : (M1 : A1) (M0 : A0) (P : R M0 M1) →
    prim^ungel {R = R} ( λ x → prim^gel {R = R} M0 M1 P x ) ≡ P
  ungel-gel M1 M0 P i = P


  -- ETA for Gel
  eta-Gel : (Q : (@tick x : BI) → primGel A0 A1 R x) (@tick r : BI )  → 
    Q r ≡ prim^gel {R = R} (Q bi0) (Q bi1) (prim^ungel {R = R} Q) r
  eta-Gel Q r i = Q r



-- pointwise equiv gives a bridge of equiv
module PequivBridgeP {ℓ} {A B : (@tick x : BI) → Type ℓ} (I0 : A bi0 ≃ B bi0) (I1 : A bi1 ≃ B bi1) where

  -- (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1)) →
  pathBridgeLemma : PathP (λ i → BridgeP (λ x → Type ℓ) (ua I0 i) (ua I1 i)) (λ x → A x) (λ x → B x) →
                    BridgeP (λ x → A x ≡ B x) (ua I0) (ua I1)
  pathBridgeLemma p = λ x i → p i x


  pequivBridgeP : ∀ (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1)) →
                  BridgeP (λ x → A x ≃ B x) I0 I1
  pequivBridgeP H = ΣBridgeP ((λ x → primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) x) ,
                              affineToBridgeP (λ x → isPropIsEquiv _) λ x →
                              isoToIsEquiv (iso
                                (primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) x)
                                (primExtent (invEq I0) (invEq I1 ) (λ (b0 : B bi0) (b1 : B bi1) (bb : BridgeP B b0 b1) →
                                  invEq ( H (invEq I0 b0) (invEq I1 b1) ) (subst2 (BridgeP B) (sym (secEq I0 b0)) (sym (secEq I1 b1)) bb) ) x)
                                {-(λ b → (primExtent (λ a0 → I0 .fst a0) (λ a1 → I1 .fst a1)
                                  (λ a0 a1 → H a0 a1 .fst) x
                                  (primExtent (λ a0 → invEq I0 a0) (λ a1 → invEq I1 a1)
                                  (λ b0 b1 bb →
                                  invEq (H (invEq I0 b0) (invEq I1 b1))
                                  (subst2 (BridgeP B) (λ i → secEq I0 b0 (~ i))
                                  (λ i → secEq I1 b1 (~ i)) bb))
                                  x b)
                                  ≡ b) ∋ {!!})-}
                                (λ b → (primExtent (λ a0 → I0 .fst a0) (λ a1 → I1 .fst a1)
                                  (λ a0 a1 → H a0 a1 .fst) x
                                  (primExtent (λ a0 → snd I0 .equiv-proof a0 .fst .fst)
                                  (λ a1 → snd I1 .equiv-proof a1 .fst .fst)
                                  (λ b0 b1 bb →
                                  snd
                                  (H (snd I0 .equiv-proof b0 .fst .fst)
                                  (snd I1 .equiv-proof b1 .fst .fst))
                                  .equiv-proof
                                  (transp
                                  (λ i →
                                  BridgeP B (snd I0 .equiv-proof b0 .fst .snd (~ i))
                                  (snd I1 .equiv-proof b1 .fst .snd (~ i)))
                                  i0 bb)
                                  .fst .fst)
                                  x b)
                                  ≡ b) ∋ {!!})
                                {-(λ b → (primExtent (λ a0 → invEq I0 a0) (λ a1 → invEq I1 a1)
                                  (λ b0 b1 bb →
                                  invEq (H (invEq I0 b0) (invEq I1 b1))
                                  (subst2 (BridgeP B) (λ i → secEq I0 b0 (~ i))
                                  (λ i → secEq I1 b1 (~ i)) bb))
                                  x
                                  (primExtent (λ a0 → I0 .fst a0) (λ a1 → I1 .fst a1)
                                  (λ a0 a1 → H a0 a1 .fst) x b)
                                  ≡ b) ∋ {!!})))-}
                                (λ b → (primExtent (λ a0 → snd I0 .equiv-proof a0 .fst .fst)
                                  (λ a1 → snd I1 .equiv-proof a1 .fst .fst)
                                  (λ b0 b1 bb →
                                  snd
                                  (H (snd I0 .equiv-proof b0 .fst .fst)
                                  (snd I1 .equiv-proof b1 .fst .fst))
                                  .equiv-proof
                                  (transp
                                  (λ i →
                                  BridgeP B (snd I0 .equiv-proof b0 .fst .snd (~ i))
                                  (snd I1 .equiv-proof b1 .fst .snd (~ i)))
                                  i0 bb)
                                  .fst .fst)
                                  x
                                  (primExtent (λ a0 → I0 .fst a0) (λ a1 → I1 .fst a1)
                                  (λ a0 a1 → H a0 a1 .fst) x b)
                                  ≡ b) ∋ {!!})))

  -- primExtent : ∀ {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
  --              (N0 : (a0 : A bi0) → B bi0 a0)
  --              (N1 : (a1 : A bi1) → B bi1 a1)
  --              (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1))
  --              (@tick r : BI) (M : A r) →
  --              B r M

  -- pequivBridgeP' : (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1))
  --                  (@tick x : BI) → A x ≃ B x
  -- pequivBridgeP' H = λ x → isoToEquiv (iso
  --                             (primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) x)
  --                             (primExtent (invEq I0) (invEq I1 ) (λ (b0 : B bi0) (b1 : B bi1) (bb : BridgeP (λ y → B y) b0 b1) →
  --                               invEq ( H (invEq I0 b0) (invEq I1 b1) )  (subst2 (λ bb0 bb1 → BridgeP B bb0 bb1) (sym (secEq I0 b0)) (sym (secEq I1 b1)) bb) ) x)
  --                             (λ b → {!!})
  --                             {!!})

  -- pequivBridgeP : ∀ (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1)) →
  --                 BridgeP (λ x → A x ≃ B x) I0 I1
  -- pequivBridgeP H = subst2 (λ e0 e1 → BridgeP (λ x → A x ≃ B x) e0 e1) (pathToEquiv-ua I0)  (pathToEquiv-ua I1)
  --                   (ChangeLine.change-line (λ x → A x ≡ B x) (λ x → A x ≃ B x) (ua I0) (ua I1)
  --                   (λ x p → pathToEquiv p)
  --                   (pathBridgeLemma {!!}) )




module Relativity {ℓ} {A0 A1 : Type ℓ} where

  to-rel : BridgeP (λ x → Type ℓ) A0 A1    →    (A0 → A1 → Type ℓ)
  to-rel C = λ a0 a1 → BridgeP (λ x → C x) a0 a1

  to-bridge : (A0 → A1 → Type ℓ)    →    BridgeP (λ x → Type ℓ) A0 A1
  to-bridge R = λ x → primGel A0 A1 R x

  rel-retract : ∀ (R : A0 → A1 → Type ℓ) → to-rel (to-bridge R) ≡ R
  rel-retract R = funExt λ a0 →
                  funExt λ a1 → isoToPath (iso
                    (λ q → prim^ungel (λ j → q j))
                    (λ p x → prim^gel {R = R} a0 a1 p x)
                    (λ p →  refl)
                    (λ q → refl))


  -- bdg-retract : ∀ (Q : BridgeP (λ x → Type ℓ) A0 A1) → to-bridge (to-rel Q) ≡ Q
  -- bdg-retract Q = BridgePPath.bridgePPath (subst2 (λ ra0 ra1 → BridgeP (λ x → to-bridge (to-rel Q) x ≡ Q x) ra0 ra1) uaIdEquiv uaIdEquiv
  --                   (ChangeLine.change-line (λ x → to-bridge (to-rel Q) x ≃ Q x) (λ x → to-bridge (to-rel Q) x ≡ Q x) (idEquiv A0) (idEquiv A1)
  --                     (λ x → λ e → ua e) ?)) --tc this leads to __IMPOSSIBLE__



