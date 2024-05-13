{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Experimental.VecChurch where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules

module _ {l : Level} (A : Type l) (isbA : isBDisc A) where

  -- a presentation of the theory of vectors, written as a dNRG
  -- V : ℕ → Type l ⊨ V 0 ×   ∀ n. A → V n → V (suc n)
  VecpDNRG : DispNRG l (topNRG # (→Form _ _ (NatForm) (UForm l)))
  VecpDNRG = 
    ×Form l l
      (El (app _ (NatForm) (UForm l)
        (let v = var0 topNRG (→Form _ _ (NatForm) (UForm l)) in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
        zeroTerm) )
      (ΠForm (NatForm) (→Form l l (bDisc-asDNRG A isbA) (→Form l l
        --Vn
        (El (app _ (NatForm) (UForm l)
          (let v = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
          let v = var0 (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
        --V (suc n)
        (El (app _ (NatForm) (UForm l)
          (let v = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
          (app (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l) # NatForm) (NatForm) (NatForm)
            sucTerm
            let v = var0 (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))))


  -- The native graph consisting of models of the theory of vectors
  -- Or more precisely, models of VecpDNRG above.
  -- note: 
  --   This has shape (topNRG # ℕ → Type) # <...>
  --   This means that when writing displayed NRGs over it, one can use the var1 rule to obtain the ℕ → Type.
  ModTVecNRG : NRGraph (ℓ-suc l)
  ModTVecNRG = topNRG # (→Form _ _ (NatForm) (UForm l)) # VecpDNRG



  -- for each n of Agda bridges, the dNRG
  -- tt:1, V : ℕ → Type, V0 ×  ∀ n. A → V n → V (suc n)    ⊨    V n
  idxCarrier : ℕ → DispNRG l ModTVecNRG
  idxCarrier n = El (app ModTVecNRG (NatForm) (UForm l)
    (let v = var1 {Γ = topNRG} (→Form _ _ (NatForm) (UForm l)) VecpDNRG in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    (cstNatTerm n))


  

  -- -- being a model of the theory of vectors.
  -- -- see signature of Vec.
  -- Vecp : (ℕ → Type l) → Type l
  -- Vecp V = V 0 × (∀ n → A → V n → V (suc n))

  -- ModTVec = Σ (ℕ → Type l) Vecp

  -- nilOf : (M : ModTVec) → M .fst 0
  -- nilOf M = M .snd .fst

  -- consOf : (M : ModTVec) → (∀ n → A → M .fst n → M .fst (suc n))
  -- consOf M = M .snd .snd

  -- -- from syntax to semantics. Note the indexing.
  -- toSem : ∀ n → Vec A n → ((M : ModTVec) → M .fst n)
  -- toSem 0 nil M = nilOf M
  -- toSem (suc n) (a ∷ as)  M = consOf M n a (toSem n as M)

  -- -- from semantics to syntax. need to register Vec as a model
  -- VecAsMod : ModTVec
  -- VecAsMod = Vec A , [] , λ n → _∷_  

  -- toSyn : ∀ n → ((M : ModTVec) → M .fst n) → Vec A n
  -- toSyn n op = op VecAsMod

  -- -- syntax <= semantics
  -- syn<=sem : ∀ n (v : Vec A n) → toSyn n (toSem n v) ≡ v
  -- syn<=sem 0 [] = refl
  -- syn<=sem (suc n) (a ∷ as) = cong (_∷_ a) (syn<=sem n as)

  -- -- sem <= syntax. need parametricity.
  -- sem<=syn : ∀ n (op : (M : ModTVec) → M .fst n) → toSem n (toSyn n op) ≡ op
  -- sem<=syn 0 op = funExt λ M → {!!}
  

  

  -- Kepp this
  -- Since this is of shape topNRG # <...>, writing displayed NRGs over this is not practical
  ModTVecNRGBad : NRGraph (ℓ-suc l)
  ModTVecNRGBad = topNRG # ΣForm
    -- ℕ → Type l
    (→Form _ _ (NatForm) (UForm l))
    -- V : ℕ → Type l ⊨ V 0 ×   ∀ n. A → V n → V (suc n)
    (×Form l l
      (El (app _ (NatForm) (UForm l)
        (let v = var0 topNRG (→Form _ _ (NatForm) (UForm l)) in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
        zeroTerm) )
      (ΠForm (NatForm) (→Form l l (bDisc-asDNRG A isbA) (→Form l l
        --Vn
        (El (app _ (NatForm) (UForm l)
          (let v = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
          let v = var0 (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
        --V (suc n)
        (El (app _ (NatForm) (UForm l)
          (let v = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
          (app (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l) # NatForm) (NatForm) (NatForm)
            sucTerm
            let v = var0 (topNRG # →Form ℓ-zero (ℓ-suc l) NatForm (UForm l)) NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))))))
