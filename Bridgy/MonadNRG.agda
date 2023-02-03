{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.conv.term:15 #-}

module Bridgy.MonadNRG where

  
open import Bridgy.BridgePrims
open import Bridgy.NRGRelRecord
open import Bridgy.HPropHSetNRG
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit



module HSetEndo where

  -- 1 ⊢ hSet → hSet dnrg
  hSetEndoDispNRG : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
  hSetEndoDispNRG ℓ =
    ΠForm {ℓA = ℓ-suc ℓ} {ℓB = ℓ-suc ℓ} {Γ = topNRG}
      (ΣForm {Γ = topNRG} (TypeForm topNRG ℓ) isSetDispNRG)
    ?

    where

      ctx = topNRG # ΣForm (TypeForm topNRG ℓ) isSetDispNRG

      aux : DispNRG (ℓ-suc ℓ) ctx
      aux = {!!}
    -- ((wkn-type-by topNRG (ΣForm (TypeForm topNRG ℓ) isSetDispNRG) (ΣForm (TypeForm topNRG ℓ) isSetDispNRG)))
    -- (wkn-type-by topNRG (ΣForm (TypeForm topNRG ℓ) isSetDispNRG) (ΣForm (TypeForm topNRG ℓ) isSetDispNRG))


