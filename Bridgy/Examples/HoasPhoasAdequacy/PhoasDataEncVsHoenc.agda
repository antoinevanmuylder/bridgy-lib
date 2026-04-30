{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.PhoasDataEncVsHoenc where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param


open import Bridgy.Examples.HoasPhoasAdequacy.LambdaDefs
open import Bridgy.Examples.HoasPhoasAdequacy.VecLemmas

toHoenc' : ∀ {j : ℕ} (H : HoasMod j) → PhoasD (hcr H) → hcr H
toHoenc' H (vvar h) = h
toHoenc' H (vapp u w) = happOf H (toHoenc' H u) (toHoenc' H w)
toHoenc' H (vlam f) =
  hlamOf H λ h → toHoenc' H (f h)

--toHoenc'OGph : ∀ {j : ℕ} (H : HoasMod j) → PhoasD (hcr H) → hcr H → Type


toHoenc : ∀ {j : ℕ} → (∀ V → Vec V j → PhoasD V) → (∀ (H : HoasMod j) → hcr H)
toHoenc nch H = toHoenc' H (nch (hcr H) (henvOf H))

toPhoasDenc : ∀ {j : ℕ} → (∀ (H : HoasMod j) → hcr H) → ∀ V → Vec V j → PhoasD V
toPhoasDenc hoch V env =
  hoch
    ((tt , PhoasD V) ,
    map vvar env ,
    (λ f → vlam λ v → f (vvar v)) ,
    vapp)


V⊨VecVj→PhoasDV : (j : ℕ) → DispNRG ℓ-zero (TypeNRG ℓ-zero)
V⊨VecVj→PhoasDV j = →Form _ _ (Vecn-dNRG' j) PhoasD-dNRG'


PhoasDenc<=Hoenc' : ∀ {j : ℕ} {N : Type} (env : Vec N j) (t0 : PhoasD (PhoasD N)) (t1 : PhoasD N)
  (trel : PhoasD-dNRG' ⦅ t0 , t1 ⦆# (λ nh h → nh ≡ vvar h)) →
  (toHoenc' ((tt , PhoasD N) , map vvar env , (λ f → vlam (λ v → f (vvar v))) , vapp) t0) ≡ t1
PhoasDenc<=Hoenc' env (vvar v0) (vvar v1) trel = trel
PhoasDenc<=Hoenc' env (vapp u0 w0) (vapp u1 w1) trel = cong₂ vapp (PhoasDenc<=Hoenc' env u0 u1 (trel .fst)) (PhoasDenc<=Hoenc' env w0 w1 (trel .snd))
PhoasDenc<=Hoenc' env (vlam f0) (vlam f1) trel =
  λ i → vlam (λ v → PhoasDenc<=Hoenc' env (f0 (vvar v)) (f1 v) (trel (vvar v) v refl ) i)



-- should use induction
PhoasDenc<=Hoenc : ∀ {j : ℕ} → ∀ nch → toPhoasDenc (toHoenc {j = j} nch) ≡ nch
PhoasDenc<=Hoenc {j} nch = funExt λ N → funExt λ env →
  --let aux = param (TypeNRG _) (V⊨VecVj→PhoasDV j) nch N (PhoasD N) (λ v t → vvar v ≡ t) env (map vvar env) in
  PhoasDenc<=Hoenc' env (nch (PhoasD N) (map vvar env)) (nch N env)
  (param (TypeNRG _) (V⊨VecVj→PhoasDV j) nch (PhoasD N) N (λ nh h → nh ≡ vvar h) (map vvar env) env
  (invEq (VecHetRel1AsLookup _ _ _) λ k → lookupVec-map {k = k} vvar env ))


-- ~have
-- [PhoasD]₂ N (PhoasD N) (λ v t → vvar v ≡ t) (nch N env)
-- (nch (PhoasD N) (map vvar env))


-- toHoenc'
-- ((tt , PhoasD N) ,
--  map vvar env , (λ f → vlam (λ v → f (vvar v))) , vapp)
-- (nch (PhoasD N) (map vvar env))
-- ≡ nch N env


Hoenc<=PhoasDenc : ∀ {j : ℕ} → ∀ hoch → toHoenc (toPhoasDenc {j = j} hoch) ≡ hoch
Hoenc<=PhoasDenc {j} hoch = funExt λ H →
  let 
      hmod = ((tt , PhoasD (hcr H)) , map vvar (henvOf H) , (λ f → vlam (λ v → f (vvar v))) , vapp)


      edge : HoasModNRG j ⦅ hmod , H ⦆
      edge = (tt , λ nh h → toHoenc' H nh ≡ h) ,
             invEq (VecHetRel1AsLookup _ _ _) (λ k →
               (cong (toHoenc' H) (lookupVec-map {k = k} vvar (henvOf H)))) ,
             (λ f0 f1 ff → cong (hlamOf H) (funExt λ h → ff (vvar h) h refl)) ,
             λ u0 u1 uu w0 w1 ww → cong₂ (happOf H) uu ww
  in
    param (HoasModNRG j) Hcarrier hoch hmod H edge


PhoasDenc≃Hoenc : ∀ {j : ℕ} → (∀ V → Vec V j → PhoasD V) ≃ (∀ (H : HoasMod j) → hcr H)
PhoasDenc≃Hoenc =
  isoToEquiv (iso
  toHoenc
  toPhoasDenc
  Hoenc<=PhoasDenc
  PhoasDenc<=Hoenc)






-- z y ⊢ (λ x. z (λ t. y x))
progPhoasD : (∀ V → Vec V 2 → PhoasD V)
progPhoasD = λ V env →
  vlam (λ x → vapp (vvar (lookup one env)) (vlam (λ t → vapp (vvar (lookup zero env)) (vvar x))))

progHoLam : ∀ (H : HoasMod 2) → hcr H
progHoLam = λ H →
  hlamOf H λ x → happOf H (lookup one (henvOf H)) (hlamOf H λ t → happOf H (lookup zero (henvOf H)) x)

progPhoasDTest : toHoenc progPhoasD ≡ progHoLam
progPhoasDTest = refl
