{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.PhoasDataChurch where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param

open import Bridgy.Examples.HoasPhoasAdequacy.LambdaDefs


-- N : Type ⊨ (V → N) → (N → N → N) → (V → N) → N
NomSig-dNRG' : (V : Type) → DispNRG ℓ-zero (TypeNRG ℓ-zero)
NomSig-dNRG' V =
  let VdNRG = (todNRG (TypeNRG ℓ-zero) (trivNRG V)) in
  →Form _ _ (→Form _ _ VdNRG X⊨ElX) --vvar → 
  (→Form _ _ (→Form _ _ X⊨ElX (→Form _ _ X⊨ElX X⊨ElX)) --vapp → 
  (→Form _ _ (→Form _ _ ((→Form _ _ VdNRG X⊨ElX )) X⊨ElX) --vlam → 
  X⊨ElX))


toNomChurch : ∀ {V : Type} → PhoasD V → ∀ (N : Type) → NomSig-dNRG' V .dcr N
toNomChurch (vvar v) = λ N vvarN vappN vlamN → vvarN v
toNomChurch (vapp u w) = λ N vvarN vappN vlamN →
  vappN (toNomChurch u N vvarN vappN vlamN) (toNomChurch w N vvarN vappN vlamN)
toNomChurch (vlam f) = λ N vvarN vappN vlamN →
  vlamN λ v → toNomChurch (f v) N vvarN vappN vlamN


toPhoasD : ∀ {V : Type} → (∀ (N : Type) → NomSig-dNRG' V .dcr N) → PhoasD V
toPhoasD {V} nch = nch (PhoasD V) vvar vapp vlam

PhoasD<=Church : ∀ {V : Type} (tv : PhoasD V) → toPhoasD (toNomChurch tv) ≡ tv
PhoasD<=Church (vvar v) = refl
PhoasD<=Church (vapp u w) = cong₂ vapp (PhoasD<=Church u) (PhoasD<=Church w)
PhoasD<=Church (vlam f) = cong vlam (funExt λ v → PhoasD<=Church (f v))


Church<=PhoasD : ∀ {V : Type} {isbV : isBDisc V} → ∀ nch →
  toNomChurch {V = V} (toPhoasD nch) ≡ nch
Church<=PhoasD {V} {isbV} nch = funExt λ N → funExt λ vvarN → funExt λ vappN → funExt λ vlamN →
  let aux = param (TypeNRG ℓ-zero) (NomSig-dNRG' V) nch
            (PhoasD V) N λ tv n → toNomChurch tv N vvarN vappN vlamN ≡ n
  in
  aux
  vvar vvarN
    (λ v0 v1 vbdg → cong vvarN (invEq (isBDisc→equiv V isbV _ _) vbdg))
  vapp vappN
    (λ u0 u1 uu w0 w1 ww → cong₂ vappN uu ww)
  vlam vlamN
    λ f0 f1 ff → cong vlamN (funExt λ v →
      ff v v (λ _ → v))


PhoasD≃Church : ∀ (V : Type) (isbV : isBDisc V) →
  PhoasD V ≃ ( (∀ (N : Type) → NomSig-dNRG' V .dcr N) )
PhoasD≃Church V isbV =
  isoToEquiv (iso
  toNomChurch
  toPhoasD
  (Church<=PhoasD {V = V} {isbV = isbV})
  PhoasD<=Church)
