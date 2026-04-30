{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.PhoasUnfoldedEncVsHoenc where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Vec
open import Cubical.Data.FinData renaming (rec to frec)
open import Cubical.Functions.FunExtEquiv

open import Bridgy.Core.EquGraph
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.WknPresTypeFormers
open import Bridgy.ROTT.Param
open import Bridgy.Examples.LamChurch

open import Bridgy.Examples.HoasPhoasAdequacy.LambdaDefs
open import Bridgy.Examples.HoasPhoasAdequacy.VecLemmas



------------------------------------------------------------------------
-- lemmas

asFin : ∀ n i → (i my< n ≡ true) → Fin n
asFin 0 i ctr = rec (not<0 i ctr)
asFin (suc n) 0 _ = zero
asFin (suc n) (suc i) hyp = suc (asFin n i hyp)



my<AND∸' : ∀ j → j my< (suc j) ≡ true
my<AND∸' zero = refl
my<AND∸' (suc j) = my<AND∸' j

my<Trans : ∀ i j k → (i my< j) ≡ true → (j my< k) ≡ true → (i my< k) ≡ true
my<Trans zero zero zero ctr = rec (false≢true ctr)
my<Trans zero zero (suc k) ctr = rec (false≢true ctr)
my<Trans zero (suc j) zero _ ctr = rec (false≢true ctr)
my<Trans zero (suc j) (suc k) = λ _ _ → refl
my<Trans (suc i) zero zero ctr = rec (false≢true ctr)
my<Trans (suc i) zero (suc k) ctr = rec (false≢true ctr)
my<Trans (suc i) (suc j) zero _ ctr = rec (false≢true ctr)
my<Trans (suc i) (suc j) (suc k) = my<Trans i j k

asMy< : ∀ n → Fin n → Σ ℕ (λ i → (i my< n) ≡ true)
asMy< zero ()
asMy< (suc n) zero = 0 , refl
asMy< (suc n) (suc i) = asMy< n i .fst , my<Trans (asMy< n i .fst) n (suc n) (asMy< n i .snd) (my<AND∸' n)


my<AND∸ : ∀ k j → ((j ∸ k) my< (suc j) ≡ true)
my<AND∸ 0 0 = refl
my<AND∸ (suc k) 0 = refl
my<AND∸ 0 (suc j) = my<AND∸' j
my<AND∸ (suc k) (suc j) = my<Trans (j ∸ k) (suc j) (suc (suc j)) (my<AND∸ k j) (my<AND∸' j)







    
------------------------------------------------------------------------


module PhoasUnfEncEnc≃HoEnc where

  PhoasModLam→HoasMod : ∀ {j : ℕ} → PhoasModLam j → HoasMod j
  PhoasModLam→HoasMod VN =
    (tt , ncrOf VN), -- H := N
    map (vvarOf VN) (nenvOf VN) , -- env := map vvar env
    -- (f : N → N) → N
    (λ f → vlamOf VN λ v → f (vvarOf VN v)) , -- see [Atkey] syntax for free, theorem 2
    vappOf VN


  HoasMod→PhoasModLam : {j : ℕ} → HoasMod j  → PhoasModLam j
  HoasMod→PhoasModLam H =
    ((tt , hcr H) , hcr H) , -- V and N := H
    henvOf H ,
    idfun _ , -- vvar := id
    hlamOf H ,
    happOf H


  PhoasUnfEnc→Hoenc : ∀ {j : ℕ} → ((VN : PhoasModLam j) → ncrOf VN) → ((H : HoasMod j) → hcr H)
  PhoasUnfEnc→Hoenc nch H = nch (HoasMod→PhoasModLam H)

  Hoenc→PhoasUnfEnc : ∀ {j : ℕ} → ((H : HoasMod j) → hcr H) → ((VN : PhoasModLam j) → ncrOf VN)
  Hoenc→PhoasUnfEnc hoch VN = hoch (PhoasModLam→HoasMod VN)

  -- Andreas: This can be proven already for the NRelators between the contexts.
  Hoenc<=PhoasUnfEnc : ∀ {j : ℕ} (hoch : ((H : HoasMod j) → hcr H)) →
    hoch ≡ PhoasUnfEnc→Hoenc (Hoenc→PhoasUnfEnc hoch)
  --funExt λ H → refl
  Hoenc<=PhoasUnfEnc hoch = funExt λ H →
    funExtDep⁻ {A = λ _ → HoasMod _} {B = λ i → hcr} {f = hoch} {g = hoch} refl
    (ΣPathP (refl ,
    ΣPathP (sym (mapvec-id (henvOf H)) ,
    refl)))


  PhoasUnfEnc<=Hoenc : ∀ {j : ℕ} → (nch : ((VN : PhoasModLam j) → ncrOf VN)) →
    nch ≡ Hoenc→PhoasUnfEnc (PhoasUnfEnc→Hoenc nch)
  PhoasUnfEnc<=Hoenc nch = funExt λ VN →
    param (PhoasModLamNRG _) Ncarrier nch VN (HoasMod→PhoasModLam (PhoasModLam→HoasMod VN)) (edge _ VN)
    where

      edge : ∀ j VN → PhoasModLamNRG j ⦅ VN , HoasMod→PhoasModLam (PhoasModLam→HoasMod VN) ⦆
      edge j VN =
        ((tt , λ v n → vvarOf VN v ≡ n) , λ n1 n2 → n1 ≡ n2) ,
        invEq (VecHetRel1AsLookup j _ _) (λ k →
          sym (lookupVec-map {k = k} (vvarOf VN) (nenvOf VN))) ,
        (λ v n hyp → hyp) ,
        (λ vvar0 fun1 varfun → cong (vlamOf VN) (funExt λ v → varfun v (vvarOf VN v) refl)) ,
        λ n0 n1 nn m0 m1 mm → cong₂ (vappOf VN) nn mm


  Hoenc≃Phoasenc : ∀ {j : ℕ} → ((H : HoasMod j) → hcr H) ≃ ((VN : PhoasModLam j) → ncrOf VN)
  Hoenc≃Phoasenc = isoToEquiv
    (iso
    Hoenc→PhoasUnfEnc
    PhoasUnfEnc→Hoenc
    (λ nch → sym (PhoasUnfEnc<=Hoenc nch))
    λ hoch → sym (Hoenc<=PhoasUnfEnc hoch))


open PhoasUnfEncEnc≃HoEnc public
