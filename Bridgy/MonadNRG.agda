{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.conv.term:15  -v tc.conv.atom.synrec:40 #-} -- -v tc.conv.atom:50

module Bridgy.MonadNRG where

  
open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Bridgy.HPropHSetNRG
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using ( flip )
open import Cubical.Data.Unit



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


  hSetEndoNRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hSetEndoNRG0 ℓ = rem-top-ctx (hSetEndoDispNRG ℓ)

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
              (λ thing (hA0 hA1 : hSet ℓ) hR →
                fromCompositeHrel (hF0 hA0) (hF1 hA1) (thing hA0 hA1 (toCompositeHrel (hA0) hA1 hR)))
              (λ thing → funExt λ hA0 → funExt λ hA1 → funExt λ { (R , Rprf) → refl } )
              λ hset-relac → refl))  } --

    where

      toCompositeHrel : ∀ {ℓ} (hA0 hA1 : hSet ℓ) (hR : hA0 .fst → hA1 .fst → hSet ℓ) →
                        (Σ (hA0 .fst → hA1 .fst → Type ℓ) λ R →
                          ∀ a0 a1 → isSet (R a0 a1))
      toCompositeHrel hA0 hA1 hR =
        ( (λ a0 a1 → hR a0 a1 .fst) , λ a0 a1 → hR a0 a1 .snd )

      fromCompositeHrel : ∀ {ℓ} (hA0 hA1 : hSet ℓ) (RR : Σ (hA0 .fst → hA1 .fst → Type ℓ) λ R → ∀ a0 a1 → isSet (R a0 a1)) →
                                ( hA0 .fst → hA1 .fst → hSet ℓ )
      fromCompositeHrel hA0 hA1 RR = λ a0 a1 →
        RR .fst a0 a1 , RR .snd a0 a1

open HSetEndo public


-- F : hSet → hSet , A :hset  ⊢ F A type
applyHSetF : ∀ {ℓ} → DispNRG ℓ (hSetEndoNRG ℓ #  HSetForm {ℓ-suc ℓ} (hSetEndoNRG ℓ) ℓ)
applyHSetF {ℓ} = record {
  dcr = λ hFhA → hFhA .fst (hFhA .snd) .fst ;
  dedge = λ hFhA0 hFhA1 hFhAA → λ b0 b1 → (hFhAA .fst) (hFhA0 .snd) (hFhA1 .snd) (hFhAA .snd) b0 b1 .fst ;
  dnativ = λ { (hF0 , hA0) (hF1 , hA1) hFhABdg b0 b1 →
    let hAA = invEq (hSetNRG ℓ .nativ hA0 hA1) (λ x → hFhABdg x .snd)
        hFF = invEq (hSetEndoNRG ℓ .nativ hF0 hF1) (λ x → hFhABdg x .fst)
    in {!!} } -- 


  }
  -- dedge = λ { (hF0 , hA0) (hF1 , hA1) (hFF , hAA ) →
  --             λ b0 b1 → hFF hA0 hA1 hAA b0 b1 .fst } ;
  -- dnativ = λ { (hF0 , hA0) (hF1 , hA1) hFbdg b0 b1 → {!!} } }

  --   dnativ = λ hFhA0 hFhA1 hFhAA b0 b1 →

-- hSetNRG ℓ .nativ hA0 hA1 : (hA0 .fst → hA1 .fst → hSet ℓ) ≃ BridgeP (λ _ → hSet ℓ) hA0 hA1
-- hSetEndoNRG ℓ .nativ hF0 hF1 :
  -- ((hA2 hA3 : hSet ℓ) →
  --  (hA2 .fst → hA3 .fst → hSet ℓ) →
  --  hF0 hA2 .fst → hF1 hA3 .fst → hSet ℓ)
  -- ≃ BridgeP (λ _ → hSet ℓ → hSet ℓ) hF0 hF1 

-- F : hSet → hSet  ⊢ ∀ A. A → F A  dnrg
hasRet : ∀ {ℓ} → DispNRG (ℓ-suc ℓ) (hSetEndoNRG ℓ)
hasRet {ℓ} = ΠForm {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ} {hSetEndoNRG ℓ}
                 -- F : .. ⊢ Type type
                 (HSetForm {ℓ-suc ℓ} (hSetEndoNRG ℓ) ℓ)
             -- F, A:Type ⊢ A → F A  dnrg
             (→Form {ℓ-suc ℓ} {ℓ} {ℓ} {F,A}
                 -- F, A:hset ⊢ A type
                 (HSetEl (hSetEndoNRG ℓ) ℓ )
             -- F,A:hset ⊢ F A type
             {!!})

  where

    F,A : NRGraph (ℓ-suc ℓ)
    F,A = (ℓ-suc ℓ - hSetEndoNRG ℓ # ℓ-suc ℓ - HSetForm {ℓ-suc ℓ} (hSetEndoNRG ℓ) ℓ)
