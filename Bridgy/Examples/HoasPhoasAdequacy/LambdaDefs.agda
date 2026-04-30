{-
- This file defines, in Agda or in comments, several representations of the syntax of untyped lambda calculus,
  and some auxiliary things about them.
- Search for "DEF" strings.
- Some representations may be unused by the other files of this library.
-}

{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.LambdaDefs where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Maybe renaming (rec to mbrec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData renaming (rec to frec)
open import Cubical.Data.Vec


open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.EquGraph
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules renaming (app to appROTT)
open import Bridgy.ROTT.WknPresTypeFormers


open import Bridgy.Examples.HoasPhoasAdequacy.VecLemmas



------------------------------------------------------------------------
-- DEF
-- 1st order, data type representation
-- indexed by number of free vars (i.e. untyped contexts)
data Lam (n : ℕ) : Type where
  var : Fin n → Lam n
  app : Lam n → Lam n → Lam n
  lam : Lam (suc n) → Lam n


-- DEF
-- unscoped De Bruijn lambda terms.
data PLam : Type where
  pvar : ℕ → PLam
  plam : PLam → PLam
  papp : PLam → PLam → PLam


------------------------------------------------------------------------
-- DEF
-- 2nd ORDER presentation. ill defined like so because of positivity
-- data L : Type
--   lam : (L → L) → L
--   app L → L → L



------------------------------------------------------------------------
-- DEF
-- the data type for Phoas.
data PhoasD (V : Type) : Type where
  vvar : V → PhoasD V
  vapp : PhoasD V → PhoasD V → PhoasD V
  vlam : (V → PhoasD V) → PhoasD V

------------------------------------------------------------------------
-- DEF
-- Phoas encoding. using data type.
-- ∀ V → Vec V j → PhoasD V
PhoasEnc : ℕ → Type₁
PhoasEnc j = ∀ (V : Type) → Vec V j → PhoasD V



[PhoasD]₂ : (V0 V1 : Type) (VV : V0 → V1 → Type) (n0 : PhoasD V0) (n1 : PhoasD V1) → Type
[PhoasD]₂ V0 V1 VV (vvar x0) (vvar x1) = VV x0 x1
[PhoasD]₂ V0 V1 VV (vapp u0 v0) (vapp u1 v1) = ([PhoasD]₂ V0 V1 VV u0 u1) × ([PhoasD]₂ V0 V1 VV v0 v1)
[PhoasD]₂ V0 V1 VV (vlam f0) (vlam f1) =
  ∀ x0 x1 → VV x0 x1 → [PhoasD]₂ V0 V1 VV (f0 x0) (f1 x1)
[PhoasD]₂ V0 V1 Vbdg _ _ = ⊥

module BridgeVsPhoasD-Aux (V0 V1 : Type) (Vbdg : Bridge _ V0 V1) where



  PhoasDOfBridge : PhoasD V0 → PhoasD V1 → Type
  PhoasDOfBridge = [PhoasD]₂ V0 V1 (BridgeP (λ z → Vbdg z))

  loosenPhoasDOfBridge : ∀ n0 n1 → PhoasDOfBridge n0 n1 → BridgeP (λ x → PhoasD (Vbdg x)) n0 n1
  loosenPhoasDOfBridge (vvar _) (vapp _ _) ctr = rec ctr
  loosenPhoasDOfBridge (vvar _) (vlam _) ctr = rec ctr
  loosenPhoasDOfBridge (vapp _ _) (vvar _) ctr = rec ctr
  loosenPhoasDOfBridge (vapp _ _) (vlam _) ctr = rec ctr
  loosenPhoasDOfBridge (vlam _) (vvar _) ctr = rec ctr
  loosenPhoasDOfBridge (vlam _) (vapp _ _) ctr = rec ctr
  loosenPhoasDOfBridge (vvar x0) (vvar x1) xbdg = λ y → vvar (xbdg y)
  loosenPhoasDOfBridge (vapp u0 v0) (vapp u1 v1) uvv =
    λ x → vapp (loosenPhoasDOfBridge u0 u1 (uvv .fst) x) (loosenPhoasDOfBridge v0 v1 (uvv .snd) x)
  loosenPhoasDOfBridge (vlam f0) (vlam f1) ff =
    -- a bit convoluted because the type signature of vlam is 2nd order, recursive
    -- ≈ λ z → vlam (extent (self) z)
    let mkBdgf01 = ΠvsBridgeP {A = λ z → Vbdg z} {B = λ z _ → PhoasD (Vbdg z)} {N0 = f0} {N1 = f1} in
    λ z → vlam (equivFun mkBdgf01
             (λ v0 v1 vv → loosenPhoasDOfBridge (f0 v0) (f1 v1) (ff v0 v1 vv))
             z)

  vvarz : BridgeP (λ z → Vbdg z → (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z)) vvar vvar
  vvarz =
    equivFun ΠvsBridgeP λ v0 v1 vbdg →
    λ z → prim^gel {R = PhoasDOfBridge} (vvar v0) (vvar v1) vbdg z

  vappz : BridgeP (λ z →
            (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z) →
            (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z) →
            (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z))
            vapp vapp
  vappz =
    equivFun ΠvsBridgeP λ u0 u1 ubdg →
    equivFun ΠvsBridgeP λ v0 v1 vbdg →
    λ z → prim^gel {R = PhoasDOfBridge} (vapp u0 v0) (vapp u1 v1)
             (prim^ungel {R = PhoasDOfBridge} (λ y → ubdg y) , prim^ungel {R = PhoasDOfBridge} (λ y → vbdg y)) z

  vlamz : BridgeP (λ z → (Vbdg z → (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z)) → (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z)) vlam vlam
  vlamz =
    equivFun ΠvsBridgeP λ f0 f1 fbdg →
    λ z → prim^gel {R = PhoasDOfBridge} (vlam f0) (vlam f1)
           (λ v0 v1 vv → prim^ungel {R = PhoasDOfBridge} (λ y → invEq ΠvsBridgeP fbdg v0 v1 vv y))
           z


  --unused
  PhoasDOfBridge' : PhoasD V0 → PhoasD V1 → Type
  PhoasDOfBridge' (vvar v0) (vvar v1) = BridgeP (λ z → Vbdg z) v0 v1
  PhoasDOfBridge' (vapp u0 v0) (vapp u1 v1) = (PhoasDOfBridge' u0 u1) × (PhoasDOfBridge' v0 v1)
  PhoasDOfBridge' (vlam f0) (vlam f1) = BridgeP (λ z → Vbdg z → PhoasD (Vbdg z)) f0 f1 --difference here
  PhoasDOfBridge' _ _ = ⊥

  -- vlamz' : BridgeP (λ z → (Vbdg z → (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge' z)) → (primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge' z)) vlam vlam
  -- vlamz' =
  --   equivFun ΠvsBridgeP λ f0 f1 fbdg →
  --   λ z → prim^gel {R = PhoasDOfBridge'} (vlam f0) (vlam f1)
  --         {!equivFun ΠvsBridge!}
  --         z


  tightenBdgPhoasD0 : BridgeP (λ z → (PhoasD (Vbdg z)) → primGel (PhoasD V0) (PhoasD V1) PhoasDOfBridge z) (idfun (PhoasD V0)) (idfun (PhoasD V1))
  tightenBdgPhoasD0 z (vvar v) = vvarz z v
  tightenBdgPhoasD0 z (vapp u v) = vappz z (tightenBdgPhoasD0 z u) (tightenBdgPhoasD0 z v)
  tightenBdgPhoasD0 z (vlam f) = vlamz z (λ v → tightenBdgPhoasD0 z (f v))

  tightenBdgPhoasD : ∀ n0 n1 → BridgeP (λ z → PhoasD (Vbdg z)) n0 n1 → PhoasDOfBridge n0 n1
  tightenBdgPhoasD n0 n1 nbdg = prim^ungel (λ z → tightenBdgPhoasD0 z (nbdg z))

  auxpredPhoasD : (@tick z : BI) (n : PhoasD (Vbdg z)) → Type
  auxpredPhoasD z n =
    (primExtent (idfun _) (idfun _) (λ n0 n1 → loosenPhoasDOfBridge n0 n1 ∘ tightenBdgPhoasD n0 n1) z n) ≡ n

  vvar-auxpredPhoasD : BridgeP (λ z → (v : Vbdg z) → auxpredPhoasD z (vvar v)) (λ v → refl) (λ v → refl)
  vvar-auxpredPhoasD =
    equivFun ΠvsBridgeP λ v0 v1 vv →
    λ z → refl

  vapp-auxpredPhoasD :
    BridgeP (λ z →
      (u : PhoasD (Vbdg z)) (v : PhoasD (Vbdg z)) →
      (udot : auxpredPhoasD z u) (vdot : auxpredPhoasD z v) → auxpredPhoasD z (vapp u v))
      (λ u v udot vdot → cong₂ vapp udot vdot) (λ u v udot vdot → cong₂ vapp udot vdot)
  vapp-auxpredPhoasD =
    equivFun ΠvsBridgeP λ u0 u1 ubdg →
    equivFun ΠvsBridgeP λ v0 v1 vbdg →
    λ z udot vdot →
      cong₂ vapp udot vdot


  vlam-auxpredPhoasD :
    BridgeP (λ z →
      (f : Vbdg z → PhoasD (Vbdg z))
      (fdot : ∀ (v : Vbdg z) → auxpredPhoasD z (f v)) →
      auxpredPhoasD z (vlam f))
      (λ f fdot → cong vlam (funExt fdot)) (λ f fdot → cong vlam (funExt fdot))
  vlam-auxpredPhoasD =
    equivFun ΠvsBridgeP λ f0 f1 fbdg →
    equivFun ΠvsBridgeP λ fdot0 fdot1 fdotBdg → --  <- not seen before. 2ary of 1ary param.
    λ z → cong vlam (funExt λ vz →
      let
        A : (@tick y : BI) → Type
        A y = Vbdg y
        B : (@tick y : BI) → Vbdg y → Type
        B y vy = primExtent f0 f1 (λ v0 v1 vv → loosenPhoasDOfBridge (f0 v0) (f1 v1) (tightenBdgPhoasD (vlam f0) (vlam f1) (λ r → vlam (fbdg r)) v0 v1 vv)) y vy ≡ fbdg y vy
      in
      primExtent {A = A} {B = B} fdot0 fdot1
      (λ v0 v1 vv → λ y → fdotBdg y (vv y))
      z vz)

  all-auxpredPhoasD : BridgeP (λ z →  (n : PhoasD (Vbdg z)) → auxpredPhoasD z n) (λ _ → refl) (λ _ → refl)
  all-auxpredPhoasD z (vvar v) = vvar-auxpredPhoasD z v
  all-auxpredPhoasD z (vapp u v) = vapp-auxpredPhoasD z u v (all-auxpredPhoasD z u) (all-auxpredPhoasD z v)
  all-auxpredPhoasD z (vlam f) = vlam-auxpredPhoasD z f λ v → all-auxpredPhoasD z (f v)

  aux-PhoasDOfBridge<= : ∀ n0 n1 → (nn : PhoasDOfBridge n0 n1) → tightenBdgPhoasD n0 n1 (loosenPhoasDOfBridge n0 n1 nn) ≡ nn
  aux-PhoasDOfBridge<= (vvar _) (vapp _ _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vvar _) (vlam _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vapp _ _) (vvar _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vapp _ _) (vlam _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vlam _) (vvar _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vlam _) (vapp _ _) ctr = rec ctr
  aux-PhoasDOfBridge<= (vvar v0) (vvar v1) vbdg = refl
  aux-PhoasDOfBridge<= (vapp u0 v0) (vapp u1 v1) uvv  = ΣPathP (aux-PhoasDOfBridge<= u0 u1 (uvv .fst) , aux-PhoasDOfBridge<= v0 v1 (uvv .snd))
  aux-PhoasDOfBridge<= (vlam f0) (vlam f1) ff =
    funExt λ v0 → funExt λ v1 → funExt λ vv →
    aux-PhoasDOfBridge<= (f0 v0) (f1 v1) (ff v0 v1 vv)


PhoasDVsBridgeP : (V0 V1 : Type) (Vbdg : Bridge Type V0 V1)
                (n0 : PhoasD V0) (n1 : PhoasD V1) →
                  [PhoasD]₂ V0 V1 (BridgeP (λ z → Vbdg z)) n0 n1
                  ≃
                  BridgeP (λ z → PhoasD (Vbdg z)) n0 n1
PhoasDVsBridgeP V0 V1 Vbdg n0 n1 =
  isoToEquiv (iso
  (λ nn → BridgeVsPhoasD-Aux.loosenPhoasDOfBridge V0 V1 Vbdg n0 n1 nn)
  (λ nbdg → BridgeVsPhoasD-Aux.tightenBdgPhoasD  V0 V1 Vbdg n0 n1 nbdg)
  (λ nbdg → λ i z → BridgeVsPhoasD-Aux.all-auxpredPhoasD V0 V1 Vbdg z (nbdg z) i)
  (BridgeVsPhoasD-Aux.aux-PhoasDOfBridge<= V0 V1 Vbdg n0 n1))


--unsafe, because TypeNRG unsafe
PhoasD-dNRG' : DispNRG ℓ-zero (TypeNRG (ℓ-zero))
PhoasD-dNRG' =
  record {
  dcr = PhoasD ;
  dedge = [PhoasD]₂ ;
  dnativ = λ V0 V1 VV Vbdg Vprf n0 n1 →
    flip compEquiv (PhoasDVsBridgeP V0 V1 Vbdg n0 n1)
    (mypathToEquiv
    λ i → [PhoasD]₂ V0 V1 (outEquGrInv Vprf i) n0 n1)
  }



-- unary translation of V ⊢ PhoasD V
[PhoasD]₁ : (V : Type) (Vdot : V → Type) → PhoasD V → Type
[PhoasD]₁ V Vdot (vvar v) = Vdot v
[PhoasD]₁ V Vdot (vapp u w) = [PhoasD]₁ V Vdot u × [PhoasD]₁ V Vdot w
[PhoasD]₁ V Vdot (vlam f) = ∀ v → Vdot v → [PhoasD]₁ V Vdot (f v)



[PhoasD]₁PresProp : (V : Type) (Vdot : V → Type) (ispVdot : ∀ v → isProp (Vdot v)) (tv : PhoasD V) →
  isProp ([PhoasD]₁ V Vdot tv)
[PhoasD]₁PresProp V Vdot ispVdot (vvar v) = ispVdot v
[PhoasD]₁PresProp V Vdot ispVdot (vapp u w) =
  isProp× ([PhoasD]₁PresProp V Vdot ispVdot u) ([PhoasD]₁PresProp V Vdot ispVdot w)
[PhoasD]₁PresProp V Vdot ispVdot (vlam f) =
  isOfHLevelΠ 1 λ v → isOfHLevelΠ 1 λ vdot → [PhoasD]₁PresProp V Vdot ispVdot (f v)


------------------------------------------------------------------------
-- DEF
-- higher order encoding, curried
-- ∀ H → Vec H j → (H → H → H) → ((H → H) → H) → H


------------------------------------------------------------------------
-- DEF
-- higher order encoding, uncurried
-- ∀ (H : HoasMod j) → hcr H
-- see ROTT types HoasModNRG and HCarrier below

hasHoEnv : (j : ℕ) → DispNRG (ℓ-zero) (topNRG # (UForm ℓ-zero))
hasHoEnv j = Vecn-dNRG j

hasHoLam : DispNRG ℓ-zero (topNRG # (UForm ℓ-zero))
hasHoLam =
  let
    v = var0 topNRG (UForm ℓ-zero)
  in
  →Form _ _ (→Form _ _ (El (wknVsU v)) (El (wknVsU v))) (El (wknVsU v))

hasHoApp : DispNRG ℓ-zero (topNRG # (UForm ℓ-zero))
hasHoApp =
  let
    v = var0 topNRG (UForm ℓ-zero)
  in
  →Form _ _ (El (wknVsU v)) (→Form _ _ (El (wknVsU v)) (El (wknVsU v)))

{- The context
       (
       t: top , H : U , (env , (holam , hoapp)) : Vec H j × (((H → H) → H) × (H → H → H))
       )
   in ROTT -}
HoasModNRG : (j : ℕ) → NRGraph (ℓ-suc ℓ-zero)
HoasModNRG j = topNRG # (UForm ℓ-zero) # ×Form _ _ (hasHoEnv j) (×Form _ _ hasHoLam hasHoApp)

HoasMod : (j : ℕ) → Type₁
HoasMod j = (HoasModNRG j) .nrg-cr

hcr : ∀ {j : ℕ} (H : HoasMod j) → Type
hcr H = H .fst .snd

henvOf : ∀ {j : ℕ} (H : HoasMod j) → Vec (hcr H) j
henvOf H = H .snd .fst

hlamOf : ∀ {j : ℕ} (H : HoasMod j) → ((hcr H) → (hcr H)) → (hcr H)
hlamOf H = H .snd .snd .fst

happOf : ∀ {j : ℕ} (H : HoasMod j) → (hcr H) → (hcr H) → (hcr H)
happOf H = H .snd .snd .snd

mkHoasMod : ∀ j → (H : Type) → Vec H j → (H → H → H) → ((H → H) → H) → HoasMod j
mkHoasMod j H henv happ hlam = (tt , H) , (henv , hlam , happ)

-- this type in ROTT (M:HoasMod j ⊢ M .fst)
Hcarrier : ∀ {j : ℕ} → DispNRG ℓ-zero (HoasModNRG j)
Hcarrier {j} =
  let v1 = var1 {Γ = topNRG} (UForm ℓ-zero) (×Form _ _ (hasHoEnv j) (×Form _ _ hasHoLam hasHoApp)) in
  El (record { tm0 = v1 .tm0 ; tm1 = v1 .tm1 ; tm-nativ = v1 .tm-nativ })



------------------------------------------------------------------------
-- DEF
-- unfolded phoas encoding, curried
-- ∀ V → Vec V j → ∀ N → (V → N) → (N → N → N) → ((V → N) → N) → N





------------------------------------------------------------------------
-- DEF
-- unfolded phoas encoding, uncurried
-- ((VN : PhoasModLam j) → ncrOf VN)
-- see ROTT types PhoasModLamNRG and NCarrier


vvarDNRG : DispNRG ℓ-zero  (topNRG # UForm ℓ-zero # UForm ℓ-zero)
vvarDNRG =
  →Form _ _
    (let v1 = var1 {Γ = topNRG} (UForm ℓ-zero) (UForm ℓ-zero) in
    El (wknWknVsU v1))
    let v0 = (var0 (topNRG # UForm ℓ-zero) (UForm ℓ-zero)) in
    El (wknVsU v0)

vappDNRG : DispNRG ℓ-zero  (topNRG # UForm ℓ-zero # UForm ℓ-zero)
vappDNRG =
  let v0 = (var0 (topNRG # UForm ℓ-zero) (UForm ℓ-zero)) in
  →Form _ _ (El (wknVsU v0)) (→Form _ _ (El (wknVsU v0)) (El (wknVsU v0)))

vlamDNRG : DispNRG ℓ-zero  (topNRG # UForm ℓ-zero # UForm ℓ-zero)
vlamDNRG = 
  let
    v0 = (var0 (topNRG # UForm ℓ-zero) (UForm ℓ-zero))
    v1 = var1 {Γ = topNRG} (UForm ℓ-zero) (UForm ℓ-zero)
  in
    →Form _ _ (→Form _ _ (El (wknWknVsU v1)) (El (wknVsU v0))) (El (wknVsU v0))

henvDNRG : (j : ℕ) → DispNRG ℓ-zero  (topNRG # UForm ℓ-zero # UForm ℓ-zero)
henvDNRG j =
  flip (tySubst (topNRG # UForm ℓ-zero # UForm ℓ-zero) (TypeNRG ℓ-zero)) (Vecn-dNRG' j)
  (record {
    nrel0 = λ tt,V,,N → tt,V,,N .fst .snd ;
    nrel1 = λ tt,V,,N0 tt,V,,N1 tt,V,,NN → tt,V,,NN .fst .snd ;
    nativ-rel =
      λ tt,V,,N0 tt,V,,N1 tt,V,,NN tt,V,N-bdg tt,V,,N-prf →
      inEquGr λ i x → outEquGr tt,V,,N-prf i x .fst .snd
    })



-- PhoasModLam j = ( (( tt : Unit )) × (V N : U) )×
--             Vec V j
--             (V → N) ×
--             (N → N → N) ×
--             ((V → N) → N) ×
PhoasModLamNRG : (j : ℕ) → NRGraph (ℓ-suc ℓ-zero)
PhoasModLamNRG j = topNRG # (UForm ℓ-zero) # (UForm ℓ-zero) #
  ×Form _ _ (henvDNRG j) (×Form _ _ vvarDNRG (×Form _ _ vlamDNRG vappDNRG))

PhoasModLam : (j : ℕ) → Type₁
PhoasModLam j = PhoasModLamNRG j .nrg-cr

mkPhoasModLam : (j : ℕ)
            (V N : Type₀) (env : Vec V j) (nvvar : V → N) (nvapp : N → N → N) (nvlam : (V → N) → N)
            → PhoasModLam j
mkPhoasModLam j V N env nvvar nvapp nvlam = ((tt , V) , N) , (env , (nvvar , (nvlam , nvapp)))


  

nvcrOf : {j : ℕ} (VN : PhoasModLam j) → Type
nvcrOf VN = VN .fst .fst .snd

ncrOf : {j : ℕ} (VN : PhoasModLam j) → Type
ncrOf VN = VN .fst .snd

vlamOf : {j : ℕ} (VN : PhoasModLam j) → ((nvcrOf VN) → (ncrOf VN)) → (ncrOf VN)
vlamOf VN = VN .snd .snd .snd .fst

vappOf : {j : ℕ} (VN : PhoasModLam j) → (ncrOf VN) → (ncrOf VN) → (ncrOf VN)
vappOf VN = VN .snd .snd .snd .snd

vvarOf : {j : ℕ} (VN : PhoasModLam j) → (nvcrOf VN) → ncrOf VN
vvarOf VN = VN .snd .snd .fst

nenvOf : {j : ℕ} (VN : PhoasModLam j) → Vec (nvcrOf VN) j
nenvOf VN = VN .snd .fst


mkPhoasModEdge : {j : ℕ} {VN0 VN1 : PhoasModLam j} →
  (VV : (nvcrOf VN0) → (nvcrOf VN1) → Type)
  (NN : (ncrOf VN0) → (ncrOf VN1) → Type)
  (envRel : VecHetRel1 (nvcrOf VN0) (nvcrOf VN1) VV j (nenvOf VN0) (nenvOf VN1))
  (vvarRel : ∀ v0 v1 → VV v0 v1 → NN (vvarOf VN0 v0) (vvarOf VN1 v1))
  (vappRel : ∀ u0 u1 → NN u0 u1 → ∀ w0 w1 → NN w0 w1 → NN (vappOf VN0 u0 w0) (vappOf VN1 u1 w1))
  (vlamRel : ∀ (f0 : (nvcrOf VN0) → (ncrOf VN0)) (f1 : (nvcrOf VN1) → (ncrOf VN1)) (ff : ∀ v0 v1 → VV v0 v1 → NN (f0 v0) (f1 v1)) → NN (vlamOf VN0 f0) (vlamOf VN1 f1)) →
  (PhoasModLamNRG j) ⦅ VN0 , VN1 ⦆
mkPhoasModEdge VV NN envRel vvarRel vappRel vlamRel =
  ((tt , VV) , NN) , (envRel , vvarRel , (vlamRel , vappRel))

-- V N : U, (env : Vec V j) vvar, vapp, vlam ⊨ N dNRG
Ncarrier : {j : ℕ} → DispNRG (ℓ-zero) (PhoasModLamNRG j)
Ncarrier {j} =
  let v1 = var1 {Γ = topNRG # (UForm ℓ-zero)} (UForm ℓ-zero) (×Form _ _ (henvDNRG j) (×Form _ _ vvarDNRG (×Form _ _ vlamDNRG vappDNRG))) in
  El (wknWknVsU v1)



------------------------------------------------------------------------
-- DEF
-- wider def than debruijn
data Lamn (N : Type) : Type where
  varn : N → Lamn N
  appn : (Lamn N) → (Lamn N) → Lamn N
  lamn : Lamn (Maybe N) → Lamn N


