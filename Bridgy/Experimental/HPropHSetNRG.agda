{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

-- relies on NRGRelRecord.
module Bridgy.HPropHSetNRG where

open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Bridgy.BDisc
open import Bridgy.GelExamples
open import Bridgy.MyPathToEquiv


module HProp where


  -- the context is explicit in our DSL
  -- this way we have syntactic equality
  -- else agda compares at record types with exponential time

  -- 1, A : Type ℓ, c c' : El A ⊢ c ≡ c' type(l)
  -- ------------------------------------------- ...
  -- 1, A : Type ℓ ⊢ isProp(A) type(l)
  isPropNRGFromOpenPath :
    ∀ (ℓ : Level) →
    DispNRG ℓ (topNRG # 
      TypeForm topNRG ℓ #
      El topNRG ℓ #
      wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)) →
    DispNRG (ℓ) (topNRG # TypeForm topNRG ℓ)
  isPropNRGFromOpenPath ℓ  openPath =
    -- 1, A : Type ℓ ⊢ isProp A
    (ΠForm (El topNRG ℓ) -- Π A $ λ c → 
    (ΠForm {ℓB = ℓ} (wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)) -- Π A $ λ c' → 
    openPath ))  -- c ≡ c'

  -- 1, A : Type ℓ, c c' : El A ⊢ c ≡ c' type(l)
  myOpenPath : ∀ (ℓ : Level) →
    DispNRG ℓ (
      topNRG # 
      TypeForm topNRG ℓ #
      El topNRG ℓ #
      wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)
    )
  myOpenPath ℓ =
    PathForm totalCtx
    -- 1, A : Type ℓ, c, c' ⊢ El A type(l)
    -- wkning the type = substituting by a 'forgetful' subst
    (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst (El topNRG ℓ))
    -- 1, A : Type ℓ, c : El A, c' : El A ⊢ c : El A
    lhs rhs

    where
      
      totalCtx : NRGraph (ℓ-suc ℓ)
      totalCtx = topNRG # 
        TypeForm topNRG ℓ #
        El topNRG ℓ #
        wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)  

      smlrCtx : NRGraph (ℓ-suc ℓ)
      smlrCtx = topNRG # TypeForm topNRG ℓ # El topNRG ℓ

      aWkSubst : NRelator totalCtx (topNRG # TypeForm topNRG ℓ)
      aWkSubst = record {
        nobjMap =  λ { ( ( ( tt , A ) , c ) , c' ) →  ( tt , A ) } ;
        nedgeMap =
          λ { {g0 = ( ( ( tt , A0 ) , c0 ) , c0' ) } {g1 = ( ( ( tt , A1 ) , c1 ) , c1' ) } ( ( ( tt , AA ) , cc ) , cc' ) → 
           (tt , AA)  } ;
        nativ-rel =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) → refl } 
        }

      lhs : SectNRG totalCtx
             (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst (El topNRG ℓ))
      lhs = record {
        ac0 = λ { ( ( ( tt , A ) , c ) , c' ) → c } ;
        ac1 =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) ( ( ( tt , AA ) , cc ) , cc' ) →
          cc  } ;
        tm-nativ =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) γbdg →
          sym ( transportRefl _ ∙ transportRefl (λ x → snd (fst (γbdg x))) )  } 
        }

      rhs : SectNRG totalCtx
             (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst
              (El topNRG ℓ))
      rhs = record {
        ac0 =  λ { ( ( ( tt , A ) , c ) , c' ) → c' } ;
        ac1 =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) ( ( ( tt , AA ) , cc ) , cc' ) →
          cc'  }  ;
        tm-nativ =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) γbdg →
           (sym (transportRefl (λ x → snd (γbdg x)))) ∙ sym (transportRefl _)  } } 

  -- 1, A : Type ℓ ⊢ isProp(A) type(l)
  isPropDispNRG0 : ∀ {ℓ : Level} → DispNRG ℓ (topNRG # TypeForm topNRG ℓ)
  isPropDispNRG0 {ℓ = ℓ} = isPropNRGFromOpenPath ℓ (myOpenPath ℓ)

  -- there's a simpler characterization of hProp { P0 , P1 }
  hPropNRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG0 ℓ =
    rem-top-ctx -- DispNRG ℓ+1 topNRG
      (ΣForm (TypeForm topNRG ℓ) (isPropDispNRG0))
      

  -- just rewriting nicely
  hPropNRG0rew : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG0rew ℓ = record {
    nrg-cr = hProp ℓ ;
    nedge =  λ { (P0 , isp0) (P1 , isp1) →
                  Σ (P0 → P1 → (Type ℓ)) (λ PP →
                  (p0 : P0) (p1 : P1) (pp : PP p0 p1) →
                  (p0' : P0) (p1' : P1) (pp' : PP p0' p1') →
                  PathP (λ i → PP (isp0 p0 p0' i) (isp1 p1 p1' i)) pp pp') } ;
    nativ = hPropNRG0 ℓ .nativ
    }

  -- hPropEdgeCharac : ∀ {ℓ} (P0 P1 : Type ℓ) (isp0 : isProp P0) (isp1 : isProp P1) →
  --   (P0 → P1 → (hProp ℓ))
  --   ≃
  --   Σ (P0 → P1 → Type ℓ) (λ PP →
  --       (p0 : P0) (p1 : P1) (pp : PP p0 p1) →
  --       (p0' : P0) (p1' : P1) (pp' : PP p0' p1') →
  --       PathP (λ i → PP (isp0 p0 p0' i) (isp1 p1 p1' i)) pp pp')
  -- hPropEdgeCharac P0 P1 isp0 isp1 =
  --   isoToEquiv (iso
  --     (λ mrel →  (  (λ p0 p1 → mrel p0 p1 .fst) ,
  --                    λ p0 p1 pp p0' p1' pp' →  toPathP (mrel p0' p1' .snd _ _) ))
  --     (λ { (PP , prf) →  λ p0 p1 →
  --              (PP p0 p1 ,
  --              λ aa aa' → {!congPathEquiv {A = λ i → PP (isp0 p0 p0 i) (isp1 p1 p1 i)} {B = λ i → PP p0 p1}
  --                          (λ i → pathToEquiv (λ j → PP (ispRefl P0 isp0 p0 i j) (ispRefl P1 isp1 p1 i j) ) )!} ) }) {!!} {!!}) -- prf p0 p1 aa p0 p1 aa'

  --   where

  --     ispRefl : ∀ {ℓ} (P : Type ℓ) (isp : isProp P) (p : P) (i : I) →
  --       isp p p i ≡ p
  --     ispRefl P isp p i = isp (isp p p i) p

  mereRelRew : ∀ {ℓ} (P0 P1 : Type ℓ) →
    (P0 → P1 → hProp ℓ)
    ≃ 
    Σ (P0 → P1 → Type ℓ) (λ R →
      ∀ p0 p1 → isProp (R p0 p1)) 
  mereRelRew P0 P1 = isoToEquiv (iso
    (λ R → (λ p0 p1 → R p0 p1 .fst) ,
            λ p0 p1 → R p0 p1 .snd)
    (λ { (R , Rprf) → λ p0 p1 → (R p0 p1 , Rprf p0 p1) } )
    (λ { (R , prf) → refl } )
    λ _ → refl)


  isPropDedgeCharac : ∀ {ℓ} (P0 P1 : Type ℓ) (isp0 : isProp P0) (isp1 : isProp P1)
                        (R : P0 → P1 → Type ℓ) →
                        (∀ (p0 : P0) (p1 : P1) → isProp (R p0 p1)) ≃ isPropDispNRG0 ⦅ isp0 , isp1 ⦆# ( (tt , R))
  isPropDedgeCharac P0 P1 isp0 isp1 R =
    isoToEquiv (iso
      mereRel→badDedge
      badDedge→mereRel
      (λ flr → funExt λ p0 → funExt λ p1 → funExt λ pp → funExt λ p0' → funExt λ p1' → funExt λ pp' →
      aux p0 p1 pp p0' p1' pp' flr .snd (flr p0 p1 pp p0' p1' pp') )
      λ ismrl → mereRelIsProp _ ismrl)


    where

      mereRel→badDedge : (∀ (p0 : P0) (p1 : P1) → isProp (R p0 p1)) → isPropDispNRG0 ⦅ isp0 , isp1 ⦆# ( (tt , R))
      mereRel→badDedge =
        (λ RPropFib → λ a0 a1 aa a0' a1' aa' →
          -- a path along a line of props always exist
          isProp→isContrPathP (λ i → RPropFib _ _) aa aa' .fst )

      ispRefl : ∀ {ℓ} (P : Type ℓ) (isp : isProp P) (p : P) (i : I) →
        isp p p i ≡ p
      ispRefl P isp p i = isp (isp p p i) p

      badDedge→mereRel : isPropDispNRG0 ⦅ isp0 , isp1 ⦆# ( (tt , R)) → (∀ (p0 : P0) (p1 : P1) → isProp (R p0 p1))
      badDedge→mereRel =
        (λ flr → λ b0 b1 → 
          λ bb bb' →
           let myflr = flr _ _ bb _ _ bb' in
              flip _∙_ (fromPathP {A = (λ i → R (isp0 b0 b0 i) (isp1 b1 b1 i))} myflr)
              (sym (fromPathP {A = (λ i → R (isp0 b0 b0 i) (isp1 b1 b1 i))}
              (invEq (congPathEquiv {A = λ i → R (isp0 b0 b0 i) (isp1 b1 b1 i)} {B = λ i → R b0 b1}
              (λ i → pathToEquiv (λ k → R (ispRefl P0 isp0 b0 i k) (ispRefl P1 isp1 b1 i k) )) {a₀ = bb} {a₁ = bb})
              refl))))

      aux : ∀ p0 p1 (pp : R p0 p1) p0' p1' pp' (flr : isPropDispNRG0 ⦅ isp0 , isp1 ⦆# ( (tt , R))) →
            isContr ( PathP (λ i → R (isp0 p0 p0' i) (isp1 p1 p1' i)) pp pp' )
      aux p0 p1 pp p0' p1' pp' flr =
        isProp→isContrPathP {A = λ i → R (isp0 p0 p0' i) (isp1 p1 p1' i)} (λ i → badDedge→mereRel flr _ _) pp pp'

      mereRelIsProp : isProp ( ∀ (p0 : P0) (p1 : P1) → isProp (R p0 p1) )
      mereRelIsProp =
        isPropΠ2 {C = λ a0 a1 → isProp (R a0 a1)}
        λ p0 p1 → isPropIsProp

  -- 1, A:Typeℓ ⊢ isProp(A) type(ℓ)
  isPropDispNRG : ∀ {ℓ} → DispNRG ℓ (topNRG # TypeForm topNRG ℓ)
  isPropDispNRG = record {
    dcr = isPropDispNRG0 .dcr ;
    -- we set isProp{ _ , _ }# R := (∀ a0 a1 → isProp (R .snd a0 a1))
    dedge = λ A0 A1 R → λ _ _ → (∀ a0 a1 → isProp (R .snd a0 a1)) ;
    dnativ = λ { (tt , A0) (tt , A1) Abdg  isp0 isp1 →
               flip compEquiv (isPropDispNRG0 .dnativ (tt , A0) (tt , A1) Abdg isp0 isp1)
               (isPropDedgeCharac A0 A1 isp0 isp1 _) }
    }



  hPropNRG1 : (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG1 ℓ = rem-top-ctx (ΣForm (TypeForm topNRG ℓ) isPropDispNRG)

  -- hProp with mere relations forms a NRG
  hPropNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG ℓ = record {
    nrg-cr = hProp ℓ ;
    nedge = λ hP0 hP1 → hP0 .fst → hP1 .fst → hProp ℓ ;
    nativ = λ hP0 hP1 → flip compEquiv (hPropNRG1 ℓ .nativ hP0 hP1)
              (mereRelRew (hP0 .fst) (hP1 .fst))
    }

open HProp public


module HSet where

  -- isPropDispNRG .dedge makes use of the  "hProp edges as mere relations" characterisation
  -- isPropDispNRG0 .dedge has 1 extra path dimension.
  -- Since we use the first one to define the current type,
  --   isSetDispNRG0 .dedge mentions 1 path dimension less that if we had used the second one.
  -- we still have to prove a same kind of lemma.
  isSetDispNRG0 : ∀ {ℓ} → DispNRG ℓ (topNRG # TypeForm topNRG ℓ)
  isSetDispNRG0 {ℓ = ℓ} =
    ΠForm (El topNRG ℓ)
    -- goal: 1, A:Typeℓ, x:ElA ⊢ (y : A) → isProp(x≡y)
    (ΠForm {ℓB = ℓ} {Γ = topNRG # TypeForm topNRG ℓ # El topNRG ℓ}
      -- 1, A:Typeℓ, x:ElA ⊢ ElA type
      (wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ))
    -- 1, A:Typeℓ, x:ElA, y:ElA ⊢ isProp(x ≡ y) type(ℓ)
    (flip (tySubst bigCtx (topNRG # TypeForm topNRG ℓ))
      isPropDispNRG
    -- 1, A:Typeℓ, x:ElA, y:ElA  --x≡y-->  1, C:Type ℓ
    (unEl bigCtx
    -- 1, A:Typeℓ, x:ElA, y:ElA ⊢ x≡y type(ℓ)
    (myOpenPath ℓ) )))

    where
      -- 1, A:Typeℓ, x:ElA, y:ElA
      bigCtx = (topNRG #
               TypeForm topNRG ℓ #
               El topNRG ℓ #
               wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ)
               (El topNRG ℓ))


  isSetDedgeCharac : ∀ {ℓ} (A0 A1 : Type ℓ) (ist0 : isSet A0) (ist1 : isSet A1)
                        (R : A0 → A1 → Type ℓ) →
                        (∀ (a0 : A0) (a1 : A1) → isSet (R a0 a1)) ≃ isSetDispNRG0 ⦅ ist0 , ist1 ⦆# ( (tt , R))
  isSetDedgeCharac A0 A1 ist0 ist1 R =
    isoToEquiv (iso
      setRel→badDedge
      badDedge→setRel
      (λ flr → funExt λ a0 → funExt λ a1 → funExt λ aa →
       funExt λ a0' → funExt λ a1' → funExt λ aa' →
       funExt λ p0 → funExt λ p1 → funExt λ u0 → funExt λ u1 →
         -- look at the goal (higher path) on paper, remember that R is a set relation
         let bar = isProp→isContrPathP {A = λ _ → u0 ≡ u1} (λ _ → tmp flr a0 a1 aa a0' a1' aa' p0 p1 u0 u1)
         in bar _ (flr a0 a1 aa a0' a1' aa' p0 p1 u0 u1) .fst )
      λ srel →
        isPropisSrel _ srel)

    where

      setRel→badDedge : (∀ (a0 : A0) (a1 : A1) → isSet (R a0 a1)) → isSetDispNRG0 ⦅ ist0 , ist1 ⦆# ( (tt , R))
      setRel→badDedge srel a0 a1 aa a0' a1' aa' p0 p1 =
        isOfHLevelPathP' {A = λ i → R (p0 i) (p1 i)} 1 (srel _ _) aa aa'

      badDedge→setRel : isSetDispNRG0 ⦅ ist0 , ist1 ⦆# ( (tt , R)) → (∀ (a0 : A0) (a1 : A1) → isSet (R a0 a1))
      badDedge→setRel flr a0 a1 aa aa' =
        flr a0 a1 aa a0 a1 aa' refl refl

      tmp : ∀ (flr : isSetDispNRG0 ⦅ ist0 , ist1 ⦆# ( (tt , R)))
              a0 a1 (aa : R a0 a1) a0' a1' (aa' : R a0' a1') (p0 : a0 ≡ a0') (p1 : a1 ≡ a1')
              (u0 u1 : PathP (λ i → R (p0 i) (p1 i)) aa aa') →
              isProp (u0 ≡ u1)
      tmp flr a0 a1 aa a0' a1' aa' p0 p1 u0 u1 =
        let foo = isOfHLevelPathP {A = λ _ → PathP (λ i → R (p0 i) (p1 i)) aa aa'} 1
        in flip (flip foo u0) u1
           (isOfHLevelPathP' {A = λ i → R (p0 i) (p1 i)} 1 (badDedge→setRel flr a0' a1') aa aa')

      isPropisSrel : isProp (∀ a0 a1 → isSet (R a0 a1))
      isPropisSrel = isPropΠ2 λ a0 a1 → isPropIsSet


  isSetDispNRG : ∀ {ℓ} → DispNRG ℓ (topNRG # TypeForm topNRG ℓ)
  isSetDispNRG {ℓ = ℓ} = record {
    dcr = λ ( _ , A ) → isSet A ;
    dedge = λ ( _ , A0) ( _ , A1) (_ , R) _ _ → ∀ (a0 : A0) (a1 : A1) → isSet (R a0 a1) ;
    dnativ = λ { (tt , A0) (tt , A1) Abdg ist0 ist1 →
               flip compEquiv (isSetDispNRG0 .dnativ (tt , A0) (tt , A1) Abdg ist0 ist1)
               (isSetDedgeCharac A0 A1 ist0 ist1 _) }
    }

  
  hSetNRG1 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hSetNRG1 ℓ = rem-top-ctx (ΣForm (TypeForm topNRG ℓ) isSetDispNRG)

  hSetNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hSetNRG ℓ = record {
    nrg-cr = hSet ℓ ;
    nedge = λ hA0 hA1 → (hA0 .fst → hA1 .fst → hSet ℓ) ;
    nativ = λ hA0 hA1 → flip compEquiv (hSetNRG1 ℓ .nativ hA0 hA1)
              (isoToEquiv (iso
              (λ R →  (λ a0 a1 → R a0 a1 .fst) , λ a0 a1 → R a0 a1 .snd)
              (λ { (R , Rprf) → λ a0 a1 → (R a0 a1 , Rprf a0 a1) })
              (λ _ → refl)
              λ _ → refl)) }

  setRelRew : ∀ {ℓ} (A0 A1 : Type ℓ) →
    (A0 → A1 → hSet ℓ)
    ≃ 
    Σ (A0 → A1 → Type ℓ) (λ R →
      ∀ a0 a1 → isSet (R a0 a1)) 
  setRelRew A0 A1 = isoToEquiv (iso
    (λ R → (λ a0 a1 → R a0 a1 .fst) ,
            λ a0 a1 → R a0 a1 .snd)
    (λ { (R , Rprf) → λ a0 a1 → (R a0 a1 , Rprf a0 a1) } )
    (λ { (R , prf) → refl } )
    λ _ → refl)

open HSet public

-- Γ  ⊢ hSet type(ℓ+1)
HSetForm : ∀ {ℓΓ}  (Γ : NRGraph ℓΓ) (ℓ : Level) → DispNRG (ℓ-suc ℓ) Γ
HSetForm Γ ℓ = record {
  dcr = λ _ → hSetNRG ℓ .nrg-cr ;
  dedge = λ _ _ _ → hSetNRG ℓ .nedge ;
  dnativ = λ _ _ _ → hSetNRG ℓ .nativ }


-- ----------------------------
-- Γ, A : HSet ℓ ⊢ El A.fst type(ℓ)
HSetEl : ∀ {ℓΓ} (Γ : NRGraph ℓΓ) (ℓ : Level) →
       DispNRG ℓ (Γ # HSetForm Γ ℓ)
HSetEl Γ ℓ = record {
  dcr = λ ghA → ghA .snd .fst ;
  dedge = λ ghA0 ghA1 → λ ghAA → λ a0 a1 → ghAA .snd a0 a1 .fst ;
  dnativ = λ { ( g0 , ( A0 , ist0 ) ) ( g1 , ( A1 , ist1 ) ) gbdg a0 a1 → idEquiv _  } }
-- record {
--   dcr = λ γA → γA .snd
--   ; dedge = λ γA0 γA1 γγAA → γγAA .snd 
--   ; dnativ = λ { (γ0 , A0) (γ1 , A1) γbdg a0 a1 → idEquiv _ } }

module MoreOnProp {l : Level} (P0 P1 : Type l) (isp0 : isProp P0) (isp1 : isProp P1) (Pbdg : BridgeP (λ _ → Type l) P0 P1) where

  coucou : (∀ p0 p1 → isProp (BridgeP (λ x → Pbdg x) p0 p1))
           ≃
           BridgeP (λ x → isProp (Pbdg x)) isp0 isp1
  coucou = 
    let ok1 = isPropDedgeCharac P0 P1 isp0 isp1 (BridgeP (λ x → Pbdg x)) in
    let ok2 = isPropDispNRG0 .dnativ (tt , P0) (tt , P1) (λ x → tt , Pbdg x) isp0 isp1 in
    let cmp = compEquiv ok1 ok2 in
    cmp

module HPropsAndBDisc {l : Level} (P : (@tick x : BI) → Type l) (isp : (@tick x : BI) → isProp (P x)) where

  PasBdg : BridgeP (λ _ → hProp l) (P bi0 , isp bi0) (P bi1 , isp bi1)
  PasBdg = λ x → (P x , isp x)

  isPropBridgePHProp : (p0 : P bi0) (p1 : P bi1) → isProp (BridgeP (λ x → P x) p0 p1)
  isPropBridgePHProp p0 p1 =
    invEq (hPropNRG _ .nativ (P bi0 , isp bi0) (P bi1 , isp bi1)) PasBdg p0 p1 .snd


inhBridgeHProp : ∀ {l : Level} (P : hProp l) (p0 p1 : P .fst) → BridgeP (λ _ → P .fst) p0 p1
inhBridgeHProp P p0 p1 = lsen (P .snd p0 p1)
-- the 2 above results entail isContr( BridgeP (λ _ → P .fst) p0 p1 ) if P : hProp.
-- It's not true that BridgeP (λ x → P x) p0 p1 is contractible though.
-- for instance:
--  BridgeP (λ x → Gel P0 P1 (λ _ _ → ⊥) x) p0 p1
--  ≃
--  ⊥
-- and I think x.Gel x is a line of props.


-- module Mooore {l} (Γ : Type (ℓ-suc l)) (isSmth : Γ → Type l) (props : ∀ γ → isProp (isSmth γ))
--                  (g0 g1 : Γ) (gbdg : BridgeP (λ _ → Γ) g0 g1) (ist0 : isSmth g0) (ist1 : isSmth g1) where

--   must : BridgeP (λ x → isSmth (gbdg x)) ist0 ist1
--   must = {!primExtent {A = λ _ → Unit} {B = λ x _ → isSmth (gbdg x)} (λ _ → ist0) (λ _ → ist1)!}






-- module Moore {l : Level} (P0 P1 : Type l) (isp0 : isProp P0) (isp1 : isProp P1) where

--   Pline : (@tick x : BI) → Type l
--   Pline x = primGel P0 P1 (λ _ _ → ⊥*) x

--   ofprops : (@tick x : BI) → isProp (Pline x)
--   ofprops x g0 g1 = {!primExtent !}





-- why P bi0 inhabited -> P x forall x?

-- isProp ( BridgeP (x.isMon(Abdg x)) A0 A1 )

-- module HPropsAreBDisc {l : Level} (P : hProp l)  where -- (P : (@tick x : BI) → Type l) (isp : (@tick x : BI) → isProp (P x))

--   hPropsAreBDisc : isBDisc (P .fst)
--   hPropsAreBDisc p0 p1 = isoToIsEquiv (iso
--     lsen
--     (λ _ → P .snd p0 p1)
--     (λ b → λ i x → {!P .snd (lsen (P .snd p0 p1) bi1) (b bi1) i!})
--     λ pp → {!!})
