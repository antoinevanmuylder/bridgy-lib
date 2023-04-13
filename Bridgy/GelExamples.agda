{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module Bridgy.GelExamples where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Base using (idEquiv)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

-- ------------------------------------------------------------------------
-- -- some cubical lemmas
-- ------------------------------------------------------------------------

transit : ∀ {ℓ} {A : Type ℓ} {x z : A} (y : A) → x ≡ y → y ≡ z → x ≡ z
transit y p q = p ∙ q

subst2-filler : ∀ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A} {z w : B}
                (C : A → B → Type ℓ'') (p : x ≡ y) (q : z ≡ w)
                (thing : C x z)
                → PathP (λ i → C (p i) (q i)) thing (subst2 C p q thing)
subst2-filler C p q thing = transport-filler (λ i → C (p i) (q i)) thing

ua-inj : ∀ {ℓ} {A B  : Type ℓ} (f g : A ≃ B) →
         ua f ≡ ua g → f ≡ g
ua-inj f g p = sym (pathToEquiv-ua f) ∙
               cong pathToEquiv p ∙
               (pathToEquiv-ua g)

cancelInitPath : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p q : y ≡ z) (iPath : x ≡ y) →
                 iPath ∙ p ≡ iPath ∙ q → p ≡ q
cancelInitPath p q iPath hyp = lUnit p ∙
                                 (cong (λ blank → blank ∙ p) (sym (lCancel iPath)) ∙
                                   (sym (assoc _ _ _) ∙
                                   cong (λ blank → iPath ⁻¹ ∙ blank) hyp ∙
                                   assoc _ _ _ ∙
                                   refl) ∙
                                 cong (λ blank → blank ∙ q) (lCancel iPath)) ∙
                               sym (lUnit q)

switchInitInvPath : ∀ {ℓ} {A : Type ℓ} {top bot right : A} (up : top ≡ right) (down : bot ≡ right) (change : top ≡ bot) → 
                   up ≡ change ∙ down → change ⁻¹ ∙ up ≡ down
switchInitInvPath up down change hyp = cancelInitPath _ _ change
                                       (assoc _ _ _ ∙
                                       cong (λ blank → blank ∙ up) (rCancel change) ∙
                                       sym (lUnit up) ∙ hyp)

switchInitPath : ∀ {ℓ} {A : Type ℓ} {top bot right : A} (up : top ≡ right) (down : bot ≡ right) (change : bot ≡ top) →
                 up ≡ change ⁻¹ ∙ down → change ∙ up ≡ down
switchInitPath up down change = switchInitInvPath up down (change ⁻¹)

{-
      top -
       |   - up
change ∨     ->
      bot ---> right
          down
-}
switchInitInvEquiv : ∀ {ℓ} {top bot right : Type ℓ} (up : top ≃ right) (down : bot ≃ right) (change : top ≃ bot) →
                     up ≡ compEquiv change down → compEquiv (invEquiv change) up ≡ down
switchInitInvEquiv up down change hyp = ua-inj _ _ (uaCompEquiv _ _ ∙ cong (λ blank → blank ∙ (ua up)) (uaInvEquiv _) ∙
                   switchInitInvPath (ua up) (ua down) (ua change)
                   (cong ua hyp ∙ uaCompEquiv _ _))

revPathP≡doubleCompPathˡ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} (p : y ≡ w) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p (~ i) ≡ s i) q r) ≡ (p ∙∙ q ∙∙ s ≡ r)
revPathP≡doubleCompPathˡ p q r s = PathP≡doubleCompPathˡ (p ⁻¹) q r s ∙
                                   cong (λ blank → (blank ∙∙ q ∙∙ s ≡ r)) (sym (symInvo p))

PathPgivesCompEq : ∀ {ℓ} {A : Type ℓ} {x y z w : A} (top : x ≡ y) (bot : z ≡ w) (left : x ≡ z) (right : y ≡ w) →
                   PathP (λ i → left i ≡ right i) top bot → top ∙ right ≡ left ∙ bot
PathPgivesCompEq top bot left right hyp = switchInitPath right (left ∙ bot) top
                                          (sym (pathToEquiv (PathP≡doubleCompPathˡ top left right bot) .fst
                                          (λ j i → hyp i j))   ∙ 
                                          doubleCompPath≡compPath (top ⁻¹) left bot)

invEquiv-pathToEquiv : ∀ {ℓ} {X Y : Type ℓ} (f : X ≡ Y) → 
                       invEquiv (pathToEquiv f) ≡ pathToEquiv (sym f)
invEquiv-pathToEquiv f = ua-inj _ _ (
                         (uaInvEquiv (pathToEquiv f) ∙
                         cong sym (ua-pathToEquiv f)) ∙
                         sym ( ua-pathToEquiv (sym f) ))

some-reordering : ∀ {ℓ} {X Y Z : Type ℓ} (f : X ≃ Y) (g : Y ≃ Z) (h : X ≃ Z) →
                  compEquiv (invEquiv f) h ≡ g → compEquiv g (compEquiv (invEquiv h) f) ≡ idEquiv Y
some-reordering f g h hyp = sym (sym (invEquiv-is-linv f) ∙
                                cong (λ blank → compEquiv blank f)
                                (sym (compEquivEquivId (invEquiv f)) ∙
                                cong (compEquiv (invEquiv f)) (sym (invEquiv-is-rinv h)) ∙
                                compEquiv-assoc (invEquiv f) h (invEquiv h) ∙
                                cong (λ blank → compEquiv blank (invEquiv h))
                                hyp) ∙
                                (sym (compEquiv-assoc g (invEquiv h) f)))

transpVSpathToEquiv : ∀ {ℓ} {X Y : Type ℓ} (f : X ≡ Y) →
                      transportEquiv f ≡ pathToEquiv f
transpVSpathToEquiv f = λ i → (
                        transport f ,
                        isPropIsEquiv (transport f) (transportEquiv f .snd) (pathToEquiv f .snd) i  )

switchMixedCommutingTriangle : ∀ {ℓ} {X Y Z : Type ℓ} (f : X ≡ Y) (g : Y ≃ Z) (h : X ≃ Z) →
                               compEquiv (pathToEquiv (sym f)) h ≡ g →
                               (y : Y) → PathP (λ i → f i) (invEq h (g .fst y)) y
switchMixedCommutingTriangle f g h hyp = λ y → toPathP (cong (λ blank → blank .fst y) (some-reordering (transportEquiv f) g h
                                                  (cong (λ blank → compEquiv blank h)
                                                    (cong invEquiv
                                                    (transpVSpathToEquiv f) ∙
                                                    invEquiv-pathToEquiv f)
                                                  ∙ hyp)))


-- ------------------------------------------------------------------------
-- -- Gel Types
-- ------------------------------------------------------------------------


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
  ungel-gel : (M0 : A0) (M1 : A1)  (P : R M0 M1) →
    prim^ungel {R = R} ( λ x → prim^gel {R = R} M0 M1 P x ) ≡ P
  ungel-gel M0 M1 P = refl


  -- ETA for Gel
  eta-Gel : (Q : (@tick x : BI) → primGel A0 A1 R x) (@tick r : BI )  → 
    Q r ≡ prim^gel {R = R} (Q bi0) (Q bi1) (prim^ungel {R = R} Q) r
  eta-Gel Q r = refl



-- pointwise equiv gives a bridge of equiv
module PequivBridgeP {ℓ} {A B : (@tick x : BI) → Type ℓ} {I0 : A bi0 ≃ B bi0} {I1 : A bi1 ≃ B bi1} where

  {- PROOF IDEA

  1) we wish to prove the following principle  (pointwise equiv of bridge types --> Bridge between equiv)
  pequivBridgeP : ∀    (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1))     →
                  BridgeP (λ x → A x ≃ B x) I0 I1

  - To build the A x ≃ B x equivalence we use the extent primitive in both directions
    extent I0 I1 (H a0 a1 .fst) x : A x → B x
    extent I0^-1 I1^-1 (HforB H)^-1 : B x → A x

  -  Regarding retract proofs:
     extent ... (extent ... bla) ≠ bla computationally because semifreshness fails
     ⇒ use the "casing by extent" method, ie, the proof term is built with extent itself

  -  once the extent-casing step is done, it is sufficient to prove a symmetry lemma
     pointwiseAorB for pointwise equivalences.
     the retract proofs of the latter are what we need up to rearranging morphisms

  2) here is the principle
  pointwiseAorB : ( (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1) )
                  ≃
                  ( (b0 : B bi0) (b1 : B bi1) → BridgeP A (invEq I0 b0) (invEq I1 b1) ≃ BridgeP B b0 b1 )
  in practice we only prove that LHS is a retract of RHS

  - left retract proof says (all are isomorphisms)
https://q.uiver.app/?q=WzAsMTAsWzAsMSwiXFxtYXRocm17QmRnfV9BIFxcOyBJXzBeey0xfUlfMChhXzApICxcXDsgSV8xXnstMX1JXzEoYV8xKSJdLFswLDMsIlxcbWF0aHJte0JkZ31fQSBhXzAgXFw6IGFfMSJdLFs0LDEsIlxcbWF0aHJte0JkZ31fQiBcXDsgSV8wSV8wXnstMX1JXzAoYV8wKSAsXFw7IElfMUlfMV57LTF9SV8xKGFfMSkiXSxbNCwzLCJcXG1hdGhybXtCZGd9X0IgSV8wYV8wICxcXDogSV8xYV8xIl0sWzAsNCwiXFxtYXRocm17Ynl9XFw6SV57LTF9SSBcXHRvIGlkIl0sWzQsNCwiXFxtYXRocm17Ynl9XFw6SUleey0xfSBcXHRvIGlkIl0sWzIsMl0sWzEsMF0sWzIsMCwiXFxtYXRocm17VE9QfVxcLGlcXCxqXFwsPVxcLHVhIChIIChcXG1hdGhybXtyZXRFcX1cXCxJXFwsYVxcLChcXHNpbSBqXFxsYW5kIGkpKSAoalxcbGFuZCBpKSJdLFsyLDQsIlxcbWF0aHJte0JPVH1cXCxpXFwsalxcLD1cXCx1YSAoSCAoXFxtYXRocm17cmV0RXF9XFwsSVxcLGFcXCwoXFxzaW0galxcbG9yIGkpKSAoalxcbG9yIGkpIl0sWzAsMSwiXFxtYXRocm17YVN1YnN0fVxcLGFfMCBcXCwgYV8xIiwyXSxbMiwzLCJcXG1hdGhybXtiU3Vic3R9XFwsSV8wYl8wICxcXDogSV8xYl8xIiwwLHsiY3VydmUiOi0yfV0sWzEsMywiSCBhXzAgYV8xIiwyXSxbMCwyLCJIXFw6SV8wXnstMX1JXzAoYV8wKSAsXFw7IElfMV57LTF9SV8xKGFfMSkiXSxbMiwzLCJcXHRpbGRle1xcbWF0aHJte2JTdWJzdH19IiwyLHsiY3VydmUiOjJ9XSxbMSwyXSxbMTEsMTQsIiIsMCx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMTMsMTUsIlxcbWF0aHJte1RPUH0iLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzE1LDEyLCJcXG1hdGhybXtCT1R9IiwyLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==

  - the cell to the right in the above diagram (not TOP,BOT) is provided by half adjointness of equivalences

  3) half adjoint equivalences

  - the above diagram is going to commute (not straightforwardly) for adjoint equivalences Iε : A biε ≃ B biε
    "half adjoint" in the sense that either the retraction/section proofs seen as (co)units of an adjunction
    satisfy the zigzag laws
    retEq I a : I^-1 I a ≡ a
    secEq I b : I I^-1 b ≡ b
    zigzagA :   (λ i → secEq Ia  i) ≡ λ i → I (retEq a i)    :  I I^-1 Ia ≡ Ia

  - in cAgda, equivalences have by definition contractible fibers
    theorem: {map | contractible fibers} ≃ {map | half adjoint equivalence}

  - see hAdj-bSubst for a thm rewriting bSubst according to half adjointness of Iε

  4) the above diagram is obtained by pasting 3 different cells together,
     one of which uses the halfadjointness of the posited equivalences Iε.
     the two remaining cells TOP and BOT are built by hand
  
  -}

  bSubst : (b0 : B bi0) (b1 : B bi1) → BridgeP B (I0 .fst (invEq I0 b0)) (I1 .fst (invEq I1 b1)) ≃ BridgeP B b0 b1 
  bSubst b0 b1 = pathToEquiv λ i → BridgeP B (secEq I0 b0 i) (secEq I1 b1 i)

  aSubst : (a0 : A bi0) (a1 : A bi1) → BridgeP A (invEq I0 (I0 .fst a0)) (invEq I1 (I1 .fst a1)) ≃ BridgeP A a0 a1
  aSubst a0 a1 = pathToEquiv λ i → BridgeP A (retEq I0 a0 i) (retEq I1 a1 i)

  -- bSubst rewritten. under the hood: Iε half adjointness.
  hAdj-bSubst : (a0 : A bi0) (a1 : A bi1) →
    bSubst (I0 .fst a0) (I1 .fst a1) ≡
    pathToEquiv λ i → BridgeP B (I0 .fst (retEq I0 a0 i)) (I1 .fst (retEq I1 a1 i))
  hAdj-bSubst = λ a0 a1 → cong pathToEquiv λ j → cong₂ (BridgeP B) -- when j is zero we want secEq like prf. when j is 1 we want I(retEq) like prf
                (λ i → sym (isHAEquiv.com ((equiv→HAEquiv I0) .snd) a0) j i) 
                λ i → sym (isHAEquiv.com ((equiv→HAEquiv I1) .snd) a1) j i

  HforB : (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1))
           (b0 : B bi0) (b1 : B bi1) → BridgeP A (invEq I0 b0) (invEq I1 b1) ≃ BridgeP B b0 b1
  HforB H b0 b1 = compEquiv (H (invEq I0 b0) (invEq I1 b1)) (bSubst b0 b1)

  HforA : (H' : (b0 : B bi0) (b1 : B bi1) → BridgeP A (invEq I0 b0) (invEq I1 b1) ≃ BridgeP B b0 b1)
          (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1)
  HforA H' a0 a1 = compEquiv (invEquiv (aSubst a0 a1)) (H' (I0 .fst a0) (I1 .fst a1))


  -- in practice we only need this half of the symmetry lemma.
  -- Notice that the following proof could be made much more robust if we had some rewriting mechanism in cubical Agda
  halfA-pointwiseAorB : retract HforB HforA
  halfA-pointwiseAorB = λ H → funExt λ a0 → funExt λ a1 →
                  let aSubstinv = invEquiv (aSubst a0 a1)
                      HIIa = H (invEq I0 (I0 .fst a0)) (invEq I1 (I1 .fst a1))
                      bSubst' = pathToEquiv (λ i → BridgeP B (I0 .fst (retEq I0 a0 i)) (I1 .fst (retEq I1 a1 i)))
                      bSubst'path : BridgeP B (I0 .fst (invEq I0 (I0 .fst a0))) (I1 .fst (invEq I1 (I1 .fst a1))) ≡ BridgeP B (I0 .fst a0) (I1 .fst a1)
                      bSubst'path = λ i → BridgeP B (I0 .fst (retEq I0 a0 i)) (I1 .fst (retEq I1 a1 i))
                      bSubstIa = bSubst (I0 .fst a0) (I1 .fst a1)
                      intermPath : BridgeP A a0 a1 ≡ BridgeP B (I0 .fst (invEq I0 (I0 .fst a0))) (I1 .fst (invEq I1 (I1 .fst a1)))
                      intermPath = λ j → ua (H (retEq I0 a0 (~ j)) (retEq I1 a1 (~ j))) j
                      aPath : BridgeP A (invEq I0 (I0 .fst a0)) (invEq I1 (I1 .fst a1)) ≡ BridgeP A a0 a1
                      aPath = λ i → BridgeP A (retEq I0 a0 i) (retEq I1 a1 i)
                  in
                    -- we want goal to be a rectangle. we make it into a square
                    switchInitInvEquiv (compEquiv HIIa bSubstIa) (H a0 a1) (aSubst a0 a1)
                    (cong (compEquiv HIIa) (hAdj-bSubst a0 a1) ∙
                    cong (λ blank → compEquiv blank bSubst') (sym (compEquivIdEquiv HIIa)) ∙
                    cong (λ blank → compEquiv blank bSubst')
                      -- top part of the rectangle = square...
                      (ua-inj (compEquiv (idEquiv _) HIIa) (compEquiv (aSubst a0 a1) (pathToEquiv (λ j → ua (H (retEq I0 a0 (~ j)) (retEq I1 a1 (~ j))) j))) (uaCompEquiv (idEquiv _) HIIa ∙
                      cong (λ blank → blank ∙ (ua HIIa)) uaIdEquiv ∙
                      ((PathPgivesCompEq refl intermPath aPath (ua HIIa)
                        (λ i j → ua (H (retEq I0 a0 (~ j ∧ i)) (retEq I1 a1 (~ j ∧ i)) ) (j ∧ i))  ∙ -- core def of top square
                      cong (λ blank → blank ∙ intermPath) (sym (ua-pathToEquiv aPath ))) ∙
                      cong (λ blank → ua (aSubst a0 a1) ∙ blank) (sym (ua-pathToEquiv intermPath))) ∙
                      sym (uaCompEquiv (aSubst a0 a1) (pathToEquiv λ j → ua (H (retEq I0 a0 (~ j)) (retEq I1 a1 (~ j))) j)))) ∙
                    -- bottom part of the rectangle = 2nd square
                    sym (compEquiv-assoc (aSubst a0 a1) (pathToEquiv intermPath) bSubst') ∙
                    cong (compEquiv (aSubst a0 a1) )
                    (ua-inj (compEquiv (pathToEquiv intermPath) (bSubst')) (H a0 a1)
                    (uaCompEquiv (pathToEquiv intermPath) bSubst' ∙
                    cong (λ blank → blank ∙ (ua bSubst')) (ua-pathToEquiv intermPath) ∙
                    cong (λ blank → intermPath ∙ blank) (ua-pathToEquiv bSubst'path) ∙
                    PathPgivesCompEq intermPath refl (ua (H a0 a1)) bSubst'path
                      (λ i j → ua (H (retEq I0 a0 (~ j ∨ i)) (retEq I1 a1 (~ j ∨ i)) ) (j ∨ i))  ∙  -- core def of bottom square
                    sym (rUnit (ua (H a0 a1)))  )) )


  -- useless lemma kept for the sake of symmetry
  HforB-Bx-retract : (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1))
                     (b0 : B bi0) (b1 : B bi1) (bb : BridgeP B b0 b1) →
                     PathP (λ i → BridgeP B (secEq I0 b0 i) (secEq I1 b1 i))
                           ( H (invEq I0 b0) (invEq I1 b1) .fst (invEq (HforB H b0 b1) bb) )
                           bb
  HforB-Bx-retract H b0 b1 bb =  (_◁_)
                                 (secEq (H (invEq I0 b0) (invEq I1 b1)) (invEq (bSubst b0 b1) bb))
                                 (symP {A = λ i → BridgeP B (secEq I0 b0 (~ i)) (secEq I1 b1 (~ i))} (toPathP refl))

  -- the following lemma links the symmetry lemma to the proof obligation appearing in the equiv vs bdg princple
  HforB-Ax-retract : (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1))
                     (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) →
                     PathP (λ i → BridgeP A (retEq I0 a0 i) (retEq I1 a1 i)) 
                           ( invEq (HforB H (I0 .fst a0) (I1 .fst a1)) (H a0 a1 .fst aa) )
                           aa
  HforB-Ax-retract H a0 a1 =
          let aPath : BridgeP A (invEq I0 (I0 .fst a0)) (invEq I1 (I1 .fst a1)) ≡ BridgeP A a0 a1
              aPath = λ i → BridgeP A (retEq I0 a0 i) (retEq I1 a1 i)
          in
            switchMixedCommutingTriangle (λ i → BridgeP A (retEq I0 a0 i) (retEq I1 a1 i)) (H a0 a1) (HforB H (I0 .fst a0) (I1 .fst a1))
            (cong (λ blank → compEquiv blank (HforB H (I0 .fst a0) (I1 .fst a1)))
            (ua-inj _ _
            (ua-pathToEquiv (sym aPath) ∙ cong sym (sym (ua-pathToEquiv aPath)) ∙ sym (  uaInvEquiv (aSubst a0 a1) ))) 
            ∙ cong (λ blank → blank a0 a1) (halfA-pointwiseAorB H)) -- cong (λ blank → blank a0 a1) (halfA-pointwiseAorB H)

  -- PROOF of the Equiv Vs Bdg principle. The proof could be cleaner. For an overall idea see beginning of this module.
  --
  -- Notice the following proof tip regarding transport.
  -- extent is typically used as a bridge value provider. you can specify wildcards for
  -- boundaries and it wont complain: extent _ _ [specify H here] ... ...
  pequivBridgeP : ∀ (H : (a0 : A bi0) (a1 : A bi1) → BridgeP A a0 a1 ≃ BridgeP B (I0 .fst a0) (I1 .fst a1)) →
                  BridgeP (λ x → A x ≃ B x) I0 I1
  pequivBridgeP H = ΣBridgeP ((λ x → primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) x) ,
                              affineToBridgeP (λ x → isPropIsEquiv _) λ x →
                              isoToIsEquiv (iso
                                (primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) x)
                                (primExtent (invEq I0) (invEq I1) (λ (b0 : B bi0) (b1 : B bi1) (bb : BridgeP B b0 b1) →
                                   invEq (H (invEq I0 b0) (invEq I1 b1)) (subst2 (BridgeP B) (sym (secEq I0 b0)) (sym (secEq I1 b1)) bb) ) x)
                                (λ b → primExtent {B = λ xxxx bbbb → primExtent (I0 .fst) (I1 .fst) (λ a0 a1 → H a0 a1 .fst) xxxx
                                                                   (primExtent (invEq I0) (invEq I1) (λ b0 b1 bb →
                                                                   invEq (H (invEq I0 b0) (invEq I1 b1))
                                                                   (subst2 (BridgeP B) (λ i → secEq I0 b0 (~ i))
                                                                   (λ i → secEq I1 b1 (~ i)) bb)) xxxx
                                                                     bbbb) ≡ bbbb} -- xxxx, bbbb: shadowing works but who knows
                                        _ _ (λ b0 b1 bb → λ y → {- FST ∙ SND -} -- (λ b0 → refl ∙ (secEq I0 b0)) (λ b1 → refl ∙ (secEq I1 b1))
                                           (λ i → secEq (H (invEq I0 b0) (invEq I1 b1)) (λ r → subst2 (BridgeP B) (λ i → secEq I0 b0 (~ i)) (λ i → secEq I1 b1 (~ i)) bb r) i y) ∙
                                            (λ i →  subst2-filler (BridgeP B) (λ i → secEq I0 b0 (~ i)) (λ i → secEq I1 b1 (~ i)) bb  (~ i) y)
                                       ) x b)
                                λ a → primExtent {B = λ xxxx aaaa → primExtent (λ a0 → invEq I0 a0) (λ a1 → invEq I1 a1)
                                                                      (λ b0 b1 bb →
                                                                      invEq (H (invEq I0 b0) (invEq I1 b1))
                                                                      (subst2 (BridgeP B) (λ i → secEq I0 b0 (~ i))
                                                                      (λ i → secEq I1 b1 (~ i)) bb))  xxxx
                                                                        (primExtent (λ a0 → I0 .fst a0) (λ a1 → I1 .fst a1)
                                                                        (λ a0 a1 → H a0 a1 .fst) xxxx aaaa) ≡ aaaa}
                                       _ _ (λ a0 a1 aa y i → HforB-Ax-retract H a0 a1 aa i y ) x a))



module Relativity {ℓ} {A0 A1 : Type ℓ} where

  open PequivBridgeP using (pequivBridgeP)

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

  -- bridges over a (gel-ed) relation are proofs of this relation
  -- this is a pointwise reformulation of the retract proof above
  bdg-over-gel : ∀ (R : A0 → A1 → Type ℓ) (a0 : A0) (a1 : A1) →
                 BridgeP (λ x → primGel A0 A1 R x) a0 a1 ≃ R a0 a1
  bdg-over-gel R a0 a1 = pathToEquiv λ i → (rel-retract R) i a0 a1


  bdg-retract : ∀ (Q : BridgeP (λ x → Type ℓ) A0 A1) → to-bridge (to-rel Q) ≡ Q
  bdg-retract Q = bridgePPath (
                  change-endpoints (uaIdEquiv) (uaIdEquiv)
                  (change-line (λ x → to-bridge (to-rel Q) x ≃ Q x) (λ x → to-bridge (to-rel Q) x ≡ Q x) (idEquiv A0) (idEquiv A1)
                    (λ x → ua)
                  (pequivBridgeP
                  λ a0 a1 → bdg-over-gel (to-rel Q) a0 a1))) --interestingly we use the other retract proof for this one

  relativity :  (A0 → A1 → Type ℓ) ≃ BridgeP (λ x → Type ℓ) A0 A1
  relativity = isoToEquiv (iso to-bridge to-rel bdg-retract rel-retract)

open Relativity public
