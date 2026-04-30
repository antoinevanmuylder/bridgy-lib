{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}



open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum renaming (map to smap) --todo remove
open import Cubical.Data.FinData --todo remove

open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments

open import LambdaDefs
open import VecLemmas


open import FirstOrderVsPhoasDataEnc
open import PhoasDataEncVsHoenc
open import PhoasUnfoldedEncVsHoenc
open import PhoasDataChurch

{-
- See main results below
- see LambdaDefs for definitions



Unintersting remarks:
- "unsafe" in this dev is refferring to a technical ROTT notion related
  to CwF democracy.
- an earlier version of this library was wrongly referring to the PHOAS encoding
  as a "nominal" encoding, and there may be remnants of that
-}





-- First order vs phoas encoding
-- the map into first-order does use parametricity (unary, emulated by binary)
-- FWIW I think that is the reason why the roundtrip at Lam only use induction, and not param.
result1 : ∀ {j : ℕ} → Lam j ≃ (∀ V → Vec V j → PhoasD V)
result1 = Lam≃Phoasenc _

-- phoas encoding vs hoas encoding.
-- Note that the latter is uncurried here (see docstring above for curried form)
result2 : ∀ {j : ℕ} → (∀ V → Vec V j → PhoasD V) ≃ (∀ (H : HoasMod j) → hcr H)
result2 = PhoasDenc≃Hoenc


--hoas encoding vs unfolded phoas encoding. both are in uncurried form.
result3 : ∀ {j : ℕ} → (∀ (H : HoasMod j) → hcr H) ≃ ((VN : PhoasModLam j) → ncrOf VN)
result3 = Hoenc≃Phoasenc





-- the original idea was to go
--   (Lam j) ⟶ (∀V.VecVj→PhoasDV) ⟶(*) (∀V env N vvar vapp vlam. N) ⟶ (∀H env happ hlam. H)
-- But (*) PhoasD V is equivalent to its encoding only (?) when V is bridge discrete
--
-- To salvage this proof idea one could perhaps systematically replace U from ROTT (under the hood: Type) with
-- BDisc, the type of bridge discrete types. Then the above righmost type is, e.g., ∀ H : BDIsc. ...
-- which is maybe not exactly what we want. 
sidenote : ∀ (V : Type) (isd : isBDisc V) →
  PhoasD V ≃ ∀ (N : Type) → (V → N) → (N → N → N) → ((V → N) → N) → N
sidenote V isd = PhoasD≃Church V isd




































module Junk (j : ℕ) where

  

  phoasEnc→UnfPhoasEnc' : ∀ V (env : Vec V j) → PhoasD V → ∀ (N : Type) → (V → N) → (N → N → N) → ((V → N) → N) → N
  phoasEnc→UnfPhoasEnc' V env (vvar v) N vvarN vappN vlamN = vvarN v
  phoasEnc→UnfPhoasEnc' V env (vapp u w) N vvarN vappN vlamN = vappN (phoasEnc→UnfPhoasEnc' V env u N vvarN vappN vlamN) (phoasEnc→UnfPhoasEnc' V env w N vvarN vappN vlamN)
  phoasEnc→UnfPhoasEnc' V env (vlam f) N vvarN vappN vlamN =
    vlamN λ v → phoasEnc→UnfPhoasEnc' V env (f v) N vvarN vappN vlamN


  phoasEnc→UnfPhoasEnc : (∀ V → Vec V j → PhoasD V) → ((VN : PhoasModLam j) → ncrOf VN)
  phoasEnc→UnfPhoasEnc t VN =
    phoasEnc→UnfPhoasEnc' (nvcrOf VN) (nenvOf VN) (t (nvcrOf VN) (nenvOf VN)) (ncrOf VN) (vvarOf VN) (vappOf VN) (vlamOf VN)


  phoasEnc→UnfPhoasEnc2 : (∀ V → Vec V j → PhoasD V) → ((VN : PhoasModLam j) → ncrOf VN)
  phoasEnc→UnfPhoasEnc2 = Hoenc→Nenc ∘ toHoenc

  phoasEnc→UnfPhoasEnc≡' : ∀ V (env : Vec V j) (tve : PhoasD V) (tnm : PhoasD (PhoasD V))
    (trel : PhoasD-dNRG' ⦅ tve , tnm ⦆# (λ lhs rhs → vvar lhs ≡ rhs) ) →
    phoasEnc→UnfPhoasEnc' V env tve (PhoasD V) vvar vapp vlam ≡
    toHoenc'
      (((tt , PhoasD V) ,
      map vvar env ,
      (λ f → vlam (λ v → f (vvar v))) ,
      vapp))
    tnm
  phoasEnc→UnfPhoasEnc≡' V env (vvar v0) (vvar v1) trel =
    trel
  phoasEnc→UnfPhoasEnc≡' V env (vapp u0 w0) (vapp u1 w1) trel =
    cong₂ vapp
      (phoasEnc→UnfPhoasEnc≡' V env u0 u1 (trel .fst))
      (phoasEnc→UnfPhoasEnc≡' V env w0 w1 (trel .snd))
  phoasEnc→UnfPhoasEnc≡' V env (vlam f0) (vlam f1) trel =
    cong vlam (funExt λ v →
      phoasEnc→UnfPhoasEnc≡' V env (f0 v) (f1 (vvar v))
      (trel  v (vvar v) refl))

  -- phoasEnc→UnfPhoasEnc≡ : ∀ (V : Type) (t : (∀ V → Vec V j → PhoasD V)) →
  --   phoasEnc→UnfPhoasEnc t ≡ phoasEnc→UnfPhoasEnc2 t
  -- phoasEnc→UnfPhoasEnc≡ V t = funExt λ VN →
  --   let aux = phoasEnc→UnfPhoasEnc≡' (nvcrOf VN) (nenvOf VN) (t (nvcrOf VN) (nenvOf VN)) (t (PhoasD (nvcrOf VN)) (map vvar (nenvOf VN))) in
  --   {!!}
  --   -- phoasEnc→UnfPhoasEnc≡' (nvcrOf VN) (nenvOf VN) (t (nvcrOf VN) (nenvOf VN)) (t (PhoasD (nvcrOf VN)) (map vvar (nenvOf VN))) ?


  -- test : Unit
  -- test = {!progPhoasenc!}
  



module Junk2 where

  data Lam' (A : Type) : Type where
    var' : A → Lam' A
    app' : Lam' A → Lam' A → Lam' A
    lam' : Lam' (A ⊎ Unit) → Lam' A

  Lam'map : {A B : Type} (f : A → B) → Lam' A → Lam' B
  Lam'map f (var' a) = var' (f a)
  Lam'map f (app' u w) = app' (Lam'map f u) (Lam'map f w)
  Lam'map f (lam' c) = lam' (Lam'map (smap f (λ _ → tt)) c)

  --z y ⊢ λ x. z x
  progLam' : Lam' (Fin 2)
  progLam' = lam' (app' (var' (inl one)) (var' (inr tt)))
