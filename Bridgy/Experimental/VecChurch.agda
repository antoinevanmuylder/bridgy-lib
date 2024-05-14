{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Experimental.VecChurch where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Empty

open import Bridgy.Core.Nat
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param


-- see VecChurch


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

  famOf : (M : ModTVecNRG .nrg-cr) → ℕ → Type l
  famOf M = M .fst .snd

  nilOf : (M : ModTVecNRG .nrg-cr) → famOf M 0
  nilOf M = M .snd .fst

  consOf : (M : ModTVecNRG .nrg-cr) → ∀ n → A → famOf M n → famOf M (suc n)
  consOf M = M .snd .snd



  -- for each n of Agda bridges, the dNRG
  -- tt:1, V : ℕ → Type, V0 ×  ∀ n. A → V n → V (suc n)    ⊨    V n
  idxCarrier : ℕ → DispNRG l ModTVecNRG
  idxCarrier n = El (app ModTVecNRG (NatForm) (UForm l)
    (let v = var1 {Γ = topNRG} (→Form _ _ (NatForm) (UForm l)) VecpDNRG in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    (cstNatTerm n))


  --registering Vec A as a model
  VecAsMod : ModTVecNRG .nrg-cr
  VecAsMod = (tt , (λ n → Lift {j = ℓ-zero} (Vec A n) )) ,
             lift [] ,
             λ n a as → lift (a ∷ (as .lower))

  -- recursion principle with heterogeneous indices (n0, n1)
  VecRec : (M : ModTVecNRG .nrg-cr) (n0 n1 : ℕ) → codeℕ n0 n1 → Lift {j = ℓ-zero} (Vec A n0) → snd (fst M) n1
  VecRec M 0 (suc n1) ctr = rec ctr
  VecRec M (suc n0) 0 ctr = rec ctr
  VecRec M 0 0 _ (lift []) = nilOf M
  VecRec M (suc n0) (suc n1) prf (lift (a ∷ as)) = consOf M n1 a (VecRec M n0 n1 prf (lift as))

  -- how does VecRec relates to idxCarrier?

  --registering the graph of the above recursor as a logical relation of models
  grRecLrel : ∀ (M : ModTVecNRG .nrg-cr) → ModTVecNRG ⦅  VecAsMod , M ⦆
  grRecLrel M =
    (tt , λ n0 n1 prf as asm → VecRec _ _ _ prf as ≡ asm ) ,
    refl ,
    rec-cons

    where

      rec-cons : (n0 n1 : ℕ) (nn : codeℕ n0 n1) (a0 a1 : A) (aa : a0 ≡ a1)
        (v0 : Lift (Vec A n0)) (m1 : famOf M n1) (ingr : VecRec M n0 n1 nn v0 ≡ m1) →
        consOf M n1 a0 (VecRec M n0 n1 nn v0) ≡ consOf M n1 a1 m1
      rec-cons n0 n1 nn a0 a1 aa v0 m1 ingr =
        λ i → consOf M n1 (aa i) (ingr i)

  -- simplified recursor
  VecSimpleRec : (M : ModTVecNRG .nrg-cr) (n : ℕ) → Vec A n → famOf M n
  VecSimpleRec M n v = VecRec M n n (codeℕrefl n) (lift v)

  toChurch : ∀ n → Vec A n → (M : ModTVecNRG .nrg-cr) → famOf M n
  toChurch n v M = VecSimpleRec M n v

  fromChurch : ∀ n → ((M : ModTVecNRG .nrg-cr) → famOf M n) → Vec A n
  fromChurch n op = (op VecAsMod) .lower

  --note the indexed induction in syn<=sem
  VecChurch : ∀ n → Vec A n ≃ ((M : ModTVecNRG .nrg-cr) → famOf M n)
  VecChurch n = isoToEquiv (iso
    (toChurch n)
    (fromChurch n)
    (λ op → funExt λ M → (param ModTVecNRG (idxCarrier n) op _ _ (grRecLrel M)))
    (syn<=sem n))

    where
      syn<=sem : ∀ n v → fromChurch n (toChurch n v) ≡ v
      syn<=sem 0 [] = refl
      syn<=sem (suc n) (a ∷ as) = cong (_∷_ a) (syn<=sem n as)

  

  

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
