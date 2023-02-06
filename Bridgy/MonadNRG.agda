{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-} -- -v tc.conv.term:15  -v tc.conv.atom.synrec:40

module Bridgy.MonadNRG where

  
open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Bridgy.HPropHSetNRG
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( flip )
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using ( ΣPath≃PathΣ )



module HSetEndo where

  -- 1 ⊢ hSet → hSet dnrg
  hSetEndoDispNRG : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
  hSetEndoDispNRG ℓ =
    ΠForm {ℓA = ℓ-suc ℓ} {ℓB = ℓ-suc ℓ} {Γ = topNRG}
      (ΣForm {Γ = topNRG} (TypeForm topNRG ℓ) isSetDispNRG)
    aux

    where

      aux : DispNRG {ℓ-suc ℓ} (ℓ-suc ℓ) (topNRG # ΣForm (TypeForm topNRG ℓ) isSetDispNRG)
      --  ℓ-zero - topNRG # (ℓ-suc ℓ) - ΣForm (TypeForm topNRG ℓ) isSetDispNRG )
      aux = wkn-type-by {ℓ = ℓ-zero} {ℓA = ℓ-suc ℓ} {ℓB = ℓ-suc ℓ} topNRG
              (ΣForm (TypeForm topNRG ℓ) isSetDispNRG)
              (ΣForm (TypeForm topNRG ℓ) isSetDispNRG)

  -- 1 ⊢ hSet → hSet dnrg
  hSetEndoDispNRG' : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
  hSetEndoDispNRG' ℓ =
    →Form {ℓA = ℓ-suc ℓ} {ℓB = ℓ-suc ℓ} {Γ = topNRG}
        ((ΣForm {Γ = topNRG} (TypeForm topNRG ℓ) isSetDispNRG))
    ((ΣForm {Γ = topNRG} (TypeForm topNRG ℓ) isSetDispNRG)) 

  hSetEndoNRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hSetEndoNRG0 ℓ = rem-top-ctx (hSetEndoDispNRG' ℓ)

  -- hSet → hSet NRG (ie ctx)
  hSetEndoNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hSetEndoNRG ℓ = record {
    nrg-cr = hSet ℓ → hSet ℓ ;
    nedge = λ hF0 hF1 → ∀ (hA0 hA1 : hSet ℓ) (hR : hA0 .fst → hA1 .fst → hSet ℓ) → (hF0 hA0 .fst → hF1 hA1 .fst → hSet ℓ) ;
    nativ = λ hF0 hF1 → flip compEquiv (hSetEndoNRG0 ℓ .nativ hF0 hF1)
              (isoToEquiv (iso
              (λ hset-relac (hA0 hA1 : hSet ℓ) →
                λ { (R , Rprf) →  (λ b0 b1 → (hset-relac hA0 hA1 λ a0 a1 → ( R a0 a1 , Rprf a0 a1 )) b0 b1 .fst) ,
                                   λ b0 b1 → (hset-relac hA0 hA1 λ a0 a1 → ( R a0 a1 , Rprf a0 a1 )) b0 b1 .snd  } )
              (λ thing (hA0 hA1 : hSet ℓ) hR b0 b1 →
                --  fromCompositeHrel (hF0 hA0) (hF1 hA1) (thing hA0 hA1 (toCompositeHrel (hA0) hA1 hR)) b0 b1
                thing hA0 hA1 ((λ a2 a3 → hR a2 a3 .fst) , (λ a2 a3 → hR a2 a3 .snd)) .fst b0 b1 ,
                thing hA0 hA1 ((λ a2 a3 → hR a2 a3 .fst) , (λ a2 a3 → hR a2 a3 .snd)) .snd b0 b1 ) 
              (λ thing → funExt λ hA0 → funExt λ hA1 → funExt λ { (R , Rprf) → refl } )
              λ hset-relac → refl))  } --

    -- where

      -- toCompositeHrel : ∀ (hA0 hA1 : hSet ℓ) (hR : hA0 .fst → hA1 .fst → hSet ℓ) →
      --                   (Σ (hA0 .fst → hA1 .fst → Type ℓ) λ R →
      --                     ∀ a0 a1 → isSet (R a0 a1))
      -- toCompositeHrel hA0 hA1 hR =
      --   ( (λ a0 a1 → hR a0 a1 .fst) , λ a0 a1 → hR a0 a1 .snd )

      -- fromCompositeHrel : ∀ {ℓ} (hA0 hA1 : hSet ℓ) (RR : Σ (hA0 .fst → hA1 .fst → Type ℓ) λ R → ∀ a0 a1 → isSet (R a0 a1)) →
      --                           ( hA0 .fst → hA1 .fst → hSet ℓ )
      -- fromCompositeHrel hA0 hA1 RR = λ a0 a1 →
      --   RR .fst a0 a1 , RR .snd a0 a1

open HSetEndo public



typeEndoNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
typeEndoNRG ℓ = rem-top-ctx (→Form {Γ = topNRG} (TypeForm topNRG ℓ) (TypeForm topNRG ℓ))



--   }

-- Γ ⊢ hA : hSet
-- -----------------
-- Γ ⊢ hA : Type
forgHSet : ∀ {ℓΓ ℓ} (Γ : NRGraph ℓΓ) (hA : SectNRG Γ (HSetForm Γ ℓ)) →
             SectNRG Γ (TypeForm Γ ℓ)
forgHSet Γ hA = record {
  ac0 = λ g → hA .ac0 g .fst ;
  ac1 = λ g0 g1 gg → λ a0 a1 → (hA .ac1 g0 g1 gg) a0 a1  .fst ; -- equivFun (setRelRew (hA .ac0 g0 .fst) (hA .ac0 g1 .fst))
  tm-nativ = λ g0 g1 gbdg → funExt λ a0 → funExt λ a1 →
    (λ i → hA .tm-nativ g0 g1 gbdg i a0 a1 .fst)
    
  }


-- 1, F : hSet → hSet  ⊢ ∀ A. A → F A  dnrg
hasRet : ∀ {ℓ} → DispNRG (ℓ-suc ℓ) (topNRG # hSetEndoDispNRG ℓ)
hasRet {ℓ} = ΠForm {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ} {Γ = 1,F}
                 -- 1,F ⊢ hSet ℓ dnrg(ℓ+1) 
                 (HSetForm {ℓ-suc ℓ} 1,F ℓ)
             -- 1,F,A  ⊢ A .fst → F A .fst dnrg
             (→Form {ℓ-suc ℓ} {ℓ} {ℓ} {1,F,A}
                 -- 1,F,A:hSet ⊢ A dnrg
                 (HSetEl {ℓ-suc ℓ} 1,F ℓ)
             -- F,A:hset ⊢ F A  dnrg
             (ElApply {ℓ-suc ℓ} {ℓ} 1,F,A
             -- F : hSet → hSet , A : hSet ⊢ F A : Type
             (forgHSet {ℓ-suc ℓ} {ℓ} 1,F,A
             -- F : hSet → hSet , A : hSet ⊢ F A : hSet
             (app {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ-suc ℓ} 1,F,A (HSetForm 1,F,A ℓ) (HSetForm 1,F,A ℓ)
                 -- 1,F,A:hSet ⊢ A:hSet
                 local-var-rule
             -- 1,F,A:hSet ⊢ F:hSet → hSet
             local-var-rule2))))

  where

    1,F = ℓ-zero - topNRG # (ℓ-suc ℓ) - (hSetEndoDispNRG ℓ)
    1,F,A = (ℓ-suc ℓ) - 1,F # ℓ-suc ℓ - (HSetForm {ℓ-suc ℓ} 1,F ℓ)


    isSet-isPropDep : isOfHLevelDep {ℓ' = ℓ} 1 isSet
    isSet-isPropDep = isOfHLevel→isOfHLevelDep 1 {B = isSet} (λ _ → isPropIsOfHLevel 2)

    hSet≡ : (hC0 hC1 : hSet ℓ) → (hC0 .fst ≡ hC1 .fst) → hC0 ≡ hC1
    hSet≡ hC0 hC1 prf = (equivFun ΣPath≃PathΣ) ( prf , isSet-isPropDep (hC0 .snd) (hC1 .snd) prf )    

    -- 1,F,A:hSet ⊢ A:hSet
    local-var-rule = record {
      ac0 = λ hFhA → hFhA .snd ;
      ac1 = λ hFhA0 hfhA1 hfhAA → hfhAA .snd ;
      tm-nativ = {!!} 
      }

    -- 1,F,A:hSet ⊢ F : hSet → hSet
    local-var-rule2 = record {
      ac0 = λ { ((tt , hF) , hA) → hF } ;
      ac1 = λ { ((tt , hF0) , hA0) ((tt , hF1) , hA1) ((ttt , hFF) , hAA) →
              λ hB0 hB1 hBB →  invEq (setRelRew _ _) (hFF hB0 hB1 (equivFun (setRelRew _ _ ) hBB)) } ;
      tm-nativ = {!!} }

-- 1, F : hSet → hSet  ⊢ ∀ A B. M A → (A → M B) → M B   dnrg
hasBind : ∀ {ℓ} → DispNRG (ℓ-suc ℓ) (topNRG # hSetEndoDispNRG ℓ)
hasBind {ℓ} = ΠForm {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ-suc ℓ} {Γ = 1,F}
                  -- 1,F ⊢ hSet ℓ dnrg(ℓ+1) 
                  (HSetForm {ℓ-suc ℓ} 1,F ℓ)
              (ΠForm {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ} {Γ = 1,F,A}
                  -- 1,F,A ⊢ hSet ℓ dnrg(ℓ+1)
                  (HSetForm {ℓ-suc ℓ} 1,F,A ℓ)
              -- 1,F,A,B ⊢ M A → (A → M B) → M B
              (flip (→Form {ℓ-suc ℓ} {ℓ} {ℓ} {Γ = 1,F,A,B})
                -- 1,F,A,B ⊢ F B type
                (ElApply {ℓ-suc ℓ} {ℓ} 1,F,A,B
                -- 1,F,A,B ⊢ F B : Type
                (forgHSet {ℓ-suc ℓ} {ℓ} 1,F,A,B
                -- 1,F,A,B ⊢ F B : hSet
                (app {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ-suc ℓ} 1,F,A,B (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ) (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ)
                    -- 1,F,A,B ⊢ B :hset
                    local-var-rule-B
                -- 1,F,A,B ⊢ F : hset → hSet
                local-var-rule-F)))
              -- 1,F,A,B ⊢ F A → (A → F B)
              (→Form {ℓ-suc ℓ} {ℓ} {ℓ} {Γ = 1,F,A,B}
                  -- 1,F,A,B ⊢ F A    dnrg
                  (ElApply {ℓ-suc ℓ} {ℓ} 1,F,A,B
                  -- 1,F,A,B ⊢ F A : Type
                  (forgHSet {ℓ-suc ℓ} {ℓ} 1,F,A,B
                  -- 1,F,A,B ⊢ F A : hSet
                  (app {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ-suc ℓ} 1,F,A,B (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ) (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ)
                      -- 1,F,A,B ⊢ A : hSet
                      local-var-rule-A
                  -- 1,F,A,B ⊢ F : hset → hSet
                  local-var-rule-F)))
              -- 1,F,A,B ⊢ A → F B
              (→Form {ℓ-suc ℓ} {ℓ} {ℓ} {Γ = 1,F,A,B}
                  (ElApply {ℓ-suc ℓ} {ℓ} 1,F,A,B
                  (forgHSet {ℓ-suc ℓ} {ℓ} 1,F,A,B
                  local-var-rule-A))
              -- 1,F,A,B ⊢ F B dnrg
              (ElApply {ℓ-suc ℓ} {ℓ} 1,F,A,B
              (forgHSet {ℓ-suc ℓ} {ℓ} 1,F,A,B
              (app {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ-suc ℓ} 1,F,A,B (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ) (HSetForm {ℓ-suc ℓ} 1,F,A,B ℓ)
                   local-var-rule-B
              local-var-rule-F)))))))


  where

    1,F = ℓ-zero - topNRG # (ℓ-suc ℓ) - (hSetEndoDispNRG ℓ)
    1,F,A = (ℓ-suc ℓ) - 1,F # ℓ-suc ℓ - (HSetForm {ℓ-suc ℓ} 1,F ℓ)
    1,F,A,B = (ℓ-suc ℓ) - 1,F,A # (ℓ-suc ℓ) - (HSetForm {ℓ-suc ℓ} 1,F,A ℓ)

    -- 1,F,A,B ⊢ B :hset
    local-var-rule-B = record {
      ac0 = λ { (((tt , hF) , hA) , hB ) → hB } ;
      ac1 = λ { (((tt , hF0) , hA0) , hB0 ) (((tt , hF1) , hA1) , hB1 ) (((tt , hFF) , hAA) , hBB ) → hBB } ;
      tm-nativ = {!!} }

    local-var-rule-F = record {
      ac0 = λ { (((tt , hF) , hA) , hB ) → hF } ;
      ac1 = λ { (((tt , hF0) , hA0) , hB0 ) (((tt , hF1) , hA1) , hB1 ) (((tt , hFF) , hAA) , hBB ) →
        λ hC0 hC1 hCC →  invEq (setRelRew _ _) (hFF hC0 hC1 (equivFun (setRelRew _ _ ) hCC)) } ;
      tm-nativ = {!!} }

    -- 1,F,A,B ⊢ A : hSet
    local-var-rule-A = record {
      ac0 = λ { (((tt , hF) , hA) , hB ) → hA } ;
      ac1 = λ { (((tt , hF0) , hA0) , hB0 ) (((tt , hF1) , hA1) , hB1 ) (((tt , hFF) , hAA) , hBB ) → hAA } ;
      tm-nativ = {!!} }


-- 1 , F : hSet → hSet ⊢ hasRet (F) × hasBind(F)    dnrg
PreMndDispNRG0 : ∀ {ℓ} → DispNRG (ℓ-suc ℓ) (topNRG # hSetEndoDispNRG ℓ)
PreMndDispNRG0 {ℓ} = ×Form (topNRG # hSetEndoDispNRG ℓ) hasRet hasBind

-- 1 ⊢ PreMnd-ℓ
-- the type of premonads on hSet ℓ 
PreMndDispNRG1 : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
PreMndDispNRG1 ℓ = ΣForm (hSetEndoDispNRG ℓ) PreMndDispNRG0


PreMndNRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
PreMndNRG0 ℓ = rem-top-ctx (PreMndDispNRG1 ℓ)


thing : (ℓ : Level) → Unit
thing ℓ = {!PreMndNRG0 ℓ .nrg-cr!}


-- next step: M:PreMnd ⊢ [M nat] → M nat
-- param of M :PreMnd ⊢ f : [M nat] → M nat will give use what we want.
