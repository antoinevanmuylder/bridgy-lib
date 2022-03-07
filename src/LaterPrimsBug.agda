{-# OPTIONS --cubical --guarded #-}
open import Agda.Builtin.Cubical.Path

module LaterPrimsBug where

primitive
  primLockUniv : Set₁

postulate
  Tick : primLockUniv

module tickTest {ℓ} {S : Set ℓ} where
 
  -- no-diag : ( (@tick α β : Tick) → S ) → (@tick x : Tick) → S
  -- no-diag p x = p x x

  toAff : (Tick → S) → (@tick x : Tick) → S
  toAff f x = f x

  yes-diag : ( (@tick α β : Tick) → S ) → (@tick x : Tick) → S
  yes-diag p = toAff ( λ x → p x x )

  -- the above normalizes to λ p x → p x x   which is equal to no-diag

  toCart : ( (@tick x : Tick) → S ) → Tick → S
  toCart f x = f x

  cart-retract : ∀ (f : Tick → S) → toCart (toAff f) ≡ f
  cart-retract = λ f i → f

  aff-retract : ∀ (f : (@tick x : Tick) → S) → toAff (toCart f) ≡ f
  aff-retract = λ f i → f
