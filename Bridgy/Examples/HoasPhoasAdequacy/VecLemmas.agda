{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.VecLemmas where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.FinData renaming (rec to frec)

open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.EquGraph
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules

open import Bridgy.Examples.HoasPhoasAdequacy.RecursiveStrictOrder



mapvec-id : ∀ {A : Type} {n : ℕ} (v : Vec A n) →
  map (λ a → a) v ≡ v
mapvec-id {n = 0} [] = refl
mapvec-id {n = suc n} (a ∷ v) = cong (_∷_ a) (mapvec-id v)

lookupVec-map' : ∀ {l : Level} {A B : Type l} (g : A → B) (j : ℕ) (v : Vec A j) (k : Fin j) →
  lookup k (map g v) ≡ g (lookup k v)
lookupVec-map' g zero [] ()
lookupVec-map' g (suc j) (a ∷ v) zero = refl
lookupVec-map' g (suc j) (a ∷ v) (suc k) = lookupVec-map' g j v k

lookupVec-map : ∀ {l : Level} {A B : Type l} {j : ℕ} {k : Fin j} (g : A → B) (v : Vec A j) →
  lookup k (map g v) ≡ g (lookup k v)
lookupVec-map {j = j} {k = k} g v = lookupVec-map' g j v k



-- 1 because we quantify once on n:ℕ
VecHetRel1 : (A0 A1 : Type) (AA : A0 → A1 → Type) →
  ∀ n → Vec A0 n → Vec A1 n → Type
VecHetRel1 A0 A1 AA .zero [] [] = Unit
VecHetRel1 A0 A1 AA (suc n) (a0 ∷ v0) (a1 ∷ v1) = AA a0 a1 × VecHetRel1 A0 A1 AA n v0 v1

diagVecHetRel1 : ∀ A j vec → VecHetRel1 A A (λ a0 a1 → a0 ≡ a1) j vec vec
diagVecHetRel1 A zero [] = tt
diagVecHetRel1 A (suc j) (x ∷ vec) = refl , diagVecHetRel1 A j vec




module _ (A0 A1 : Type) (Abdg : Bridge _ A0 A1) where

  VecOfBridge : ∀ n → Vec A0 n → Vec A1 n → Type
  VecOfBridge = VecHetRel1 A0 A1 (BridgeP (λ z → Abdg z))

  loosenVecOfBridge : ∀ n v0 v1 → VecOfBridge n v0 v1 → BridgeP (λ z → Vec (Abdg z) n) v0 v1
  loosenVecOfBridge zero [] [] _ = λ z → []
  loosenVecOfBridge (suc n) (x ∷ v0) (x₁ ∷ v1) abdg,vv = λ z → (abdg,vv .fst z ∷ loosenVecOfBridge n v0 v1 (abdg,vv .snd) z) 

  nilvecz : BridgeP (λ z → primGel (Vec A0 0) (Vec A1 0) (VecOfBridge 0) z) [] []
  nilvecz = λ z → prim^gel {R = VecOfBridge 0} [] [] tt z

  consvecz : ∀ n →
    BridgeP (λ z →
      Abdg z →
      (primGel (Vec A0 n) (Vec A1 n) (VecOfBridge n) z) →
      (primGel (Vec A0 (suc n)) (Vec A1 (suc n)) (VecOfBridge (suc n)) z))
    _∷_ _∷_
  consvecz n =
    equivFun ΠvsBridgeP λ a0 a1 abdg →
    equivFun ΠvsBridgeP λ v0 v1 vbdg →
    λ z → prim^gel {R = VecOfBridge (suc n)} (a0 ∷ v0) (a1 ∷ v1) (abdg , prim^ungel (λ y → vbdg y)) z

  --eta expansion of id : Vec A n → Vec A n
  idVecByInd : ∀ (A : Type) n → Vec A n → Vec A n
  idVecByInd A 0 [] = []
  idVecByInd A (suc n) (a ∷ v) = a ∷ (idVecByInd A n v)

  -- note: due to a limitation of indexed types, this thing is not a bdg btw idfun, idfun but rather their "eta expansion" defined by pm. (or not even?)
  --       the Bridge type would be
  --       ∀ n → BridgeP (λ z → Vec (Abdg z) n → primGel (Vec A0 n) (Vec A1 n) (VecOfBridge n) z) (idfun (Vec A0 n)) (idfun (Vec A1 n))
  -- tightenBdgVec0 : ∀ n → BridgeP (λ z → Vec (Abdg z) n → primGel (Vec A0 n) (Vec A1 n) (VecOfBridge n) z) (idVecByInd A0 n) (idVecByInd A1 n)
  tightenBdgVec0 : (n : ℕ) (@tick z : BI) → Vec (Abdg z) n → primGel (Vec A0 n) (Vec A1 n) (VecOfBridge n) z
  tightenBdgVec0 0 z [] = nilvecz z
  tightenBdgVec0 (suc n) z (a ∷ v) = consvecz n z a (tightenBdgVec0 n z v)

  isIdByIndPtwLhs : ∀ n (v : Vec A0 n) → tightenBdgVec0 n bi0 v ≡ v
  isIdByIndPtwLhs zero [] = refl
  isIdByIndPtwLhs (suc n) (a ∷ v) = cong (_∷_ a) (isIdByIndPtwLhs n v)

  isIdByIndLhs : ∀ n → tightenBdgVec0 n bi0 ≡ idfun (Vec A0 n)
  isIdByIndLhs n = funExt (isIdByIndPtwLhs n)

  isIdByIndPtwRhs : ∀ n (v : Vec A1 n) → tightenBdgVec0 n bi1 v ≡  v
  isIdByIndPtwRhs zero [] = refl
  isIdByIndPtwRhs (suc n) (a ∷ v) = cong (_∷_ a) (isIdByIndPtwRhs n v)

  isIdByIndRhs : ∀ n → tightenBdgVec0 n bi1 ≡ idfun (Vec A1 n)
  isIdByIndRhs n = funExt (isIdByIndPtwRhs n)

  tightenBdgVec1 : ∀ n v0 v1 → BridgeP (λ z → Vec (Abdg z) n) v0 v1 → VecOfBridge n (tightenBdgVec0 n bi0 v0) (tightenBdgVec0 n bi1 v1)
  tightenBdgVec1 n v0 v1 vbdg = prim^ungel (λ z → tightenBdgVec0 n z (vbdg z))


  adj-tighten : ∀ n v0 v1 → VecOfBridge n (tightenBdgVec0 n bi0 v0) (tightenBdgVec0 n bi1 v1) → VecOfBridge n v0 v1
  adj-tighten n v0 v1 vv = transport (λ i → VecOfBridge n (isIdByIndPtwLhs n v0 i) (isIdByIndPtwRhs n v1 i)) vv

  tightenBdgVec : ∀ n v0 v1 → BridgeP (λ z → Vec (Abdg z) n) v0 v1 → VecOfBridge n v0 v1
  tightenBdgVec n v0 v1 = (adj-tighten n v0 v1) ∘ (tightenBdgVec1 n v0 v1)

  -- tightenBdgVec1-lemma : ∀ n a0 v0 a1 v1 (abdg : BridgeP (λ z → Abdg z) a0 a1) (vbdg : BridgeP (λ z → Vec (Abdg z) n) v0 v1) →
  --   tightenBdgVec1 (suc n) (a0 ∷ v0) (a1 ∷ v1) (λ z → abdg z ∷ vbdg z) .fst ≡ abdg
  -- tightenBdgVec1-lemma n a0 v0 a1 v1 abdg vbdg = refl

  adj-tighten-lemma : ∀ n a0 v0 a1 v1 (abdg : BridgeP (λ z → Abdg z) a0 a1) (vv : VecOfBridge n (tightenBdgVec0 n bi0 v0) (tightenBdgVec0 n bi1 v1)) →
    adj-tighten (suc n) (a0 ∷ v0) (a1 ∷ v1) (abdg , vv) .fst ≡ abdg
  adj-tighten-lemma n a0 v0 a1 v1 abdg vv = transportRefl abdg

  extpredVec : (n : ℕ) (@tick z : BI) (v : Vec (Abdg z) n) → Type
  extpredVec n z v =
    primExtent (idfun _) (idfun _) (λ v0 v1 → loosenVecOfBridge n v0 v1 ∘ tightenBdgVec n v0 v1) z v ≡ v

  extpredVec-nilvec : BridgeP (λ z → extpredVec 0 z []) refl refl
  extpredVec-nilvec z = refl

  extpredVec-consvec : ∀ n →
    BridgeP (λ z →
      (a : Abdg z) (v : Vec (Abdg z) n) (vdot : extpredVec n z v) →
      extpredVec (suc n) z (a ∷ v))
    (λ a v → λ vdot → cong₂ _∷_ (refl) vdot) (λ a v → λ vdot → cong₂ _∷_ (refl) vdot)
  extpredVec-consvec n =
    equivFun ΠvsBridgeP λ a0 a1 abdg →
    equivFun ΠvsBridgeP λ v0 v1 vbdg →
    λ z hyp → cong₂ _∷_ (λ i → adj-tighten-lemma n a0 v0 a1 v1 abdg (tightenBdgVec1 (suc n) (a0 ∷ v0) (a1 ∷ v1) (λ z → abdg z ∷  vbdg z) .snd) i z) hyp

  -- Due to a limitation of indexed types this thing is not a bdg btw (λ _ → refl), (λ _ → refl).
  -- The mentioned bdg type would be
  --   ∀ n → BridgeP (λ z → (v : Vec (Abdg z) n) → extpredVec n z v) (λ _ → refl) (λ _ → refl)
  extpredVec-all : (n : ℕ) (@tick z : BI) (v : Vec (Abdg z) n) → extpredVec n z v
  extpredVec-all 0 z [] = extpredVec-nilvec z
  extpredVec-all (suc n) z (a ∷ v) = extpredVec-consvec n z a v (extpredVec-all n z v)

  adj-extpredVec-all : ∀ n → BridgeP (λ z → (v : Vec (Abdg z) n) → extpredVec n z v) (λ _ → refl) (λ _ → refl)
  adj-extpredVec-all n =
    transport (λ i → BridgeP (λ z → (v : Vec (Abdg z) n) → extpredVec n z v) (λ v → adjlhs n v i) (λ v → adjrhs n v i))
      λ z → extpredVec-all n z
    where
      adjlhs : ∀ n (v : Vec A0 n) → extpredVec-all n bi0 v ≡ refl
      adjlhs 0 [] = refl
      adjlhs (suc n) (a ∷ v) = λ j i → a ∷ (adjlhs n v j i)

      adjrhs : ∀ n (v : Vec A1 n) → extpredVec-all n bi1 v ≡ refl
      adjrhs 0 [] = refl
      adjrhs (suc n) (a ∷ v) = λ j i → a ∷ (adjrhs n v j i)
      

  VecOfBridge<= : ∀ n v0 v1 (vv : VecOfBridge n v0 v1) → tightenBdgVec n v0 v1 (loosenVecOfBridge n v0 v1 vv) ≡ vv
  VecOfBridge<= 0 [] [] tt = refl
  VecOfBridge<= (suc n) (a0 ∷ v0) (a1 ∷ v1) avv =
    let
      indhyp = VecOfBridge<= n v0 v1 (avv .snd)
    in
    ΣPathP (
      adj-tighten-lemma n a0 v0 a1 v1 (avv .fst) (tightenBdgVec1 n v0 v1 (loosenVecOfBridge n v0 v1 (avv .snd))) ,
      indhyp)

VecVsBridgeP : (A0 A1 : Type) (Abdg : Bridge Type A0 A1) (n : ℕ) (v0 : Vec A0 n) (v1 : Vec A1 n) →
  VecHetRel1 A0 A1 (BridgeP (λ z → Abdg z)) n v0 v1
  ≃
  BridgeP (λ z → Vec (Abdg z) n) v0 v1
VecVsBridgeP A0 A1 Abdg n v0 v1 =
  isoToEquiv (iso
  (loosenVecOfBridge A0 A1 Abdg n v0 v1)
  (tightenBdgVec A0 A1 Abdg n v0 v1)
  (λ vbdg → λ i z → adj-extpredVec-all A0 A1 Abdg n z (vbdg z) i)
  (VecOfBridge<= A0 A1 Abdg n v0 v1))
  
--unsafe because TypeNRG unsafe
-- n external to ROTT in this version
-- A : U ⊨ Vec A n  dNRG
Vecn-dNRG' : ∀ (n : ℕ) → DispNRG ℓ-zero (TypeNRG (ℓ-zero))
Vecn-dNRG' n =
  record {
  dcr = λ A → Vec A n ;
  dedge = λ A0 A1 AA → VecHetRel1 A0 A1 AA n ;
  dnativ = λ A0 A1 AA Abdg Aprf v0 v1 →
    flip compEquiv (VecVsBridgeP A0 A1 Abdg n v0 v1)
    (mypathToEquiv
    λ i → VecHetRel1 A0 A1 (outEquGrInv Aprf i) n v0 v1)
  }

-- _,A:U ⊨ Vec A n dNRG
Vecn-dNRG : ∀ (j : ℕ) → DispNRG (ℓ-zero) (topNRG # (UForm ℓ-zero))
Vecn-dNRG j =
  record {
    dcr = λ tt,A → Vec (tt,A .snd) j;
    dedge = λ tt,A0 tt,A1 tt,AA → VecHetRel1 (tt,A0 .snd) (tt,A1 .snd) (tt,AA .snd) j ;
    dnativ = λ tt,A0 tt,A1 tt,AA tt,A-bdg tt,A-prf v0 v1 →
      flip compEquiv (VecVsBridgeP (tt,A0 .snd) (tt,A1 .snd) (λ x → tt,A-bdg x .snd) j v0 v1)
      (mypathToEquiv (cong (λ blk → VecHetRel1 (tt,A0 .snd) (tt,A1 .snd) blk j v0 v1)
      (funExt λ a0 → funExt λ a1 →
      let
        hav = change-line-path (λ z → primGel (snd tt,A0) (snd tt,A1) (snd tt,AA) z) (λ z → tt,A-bdg z .snd) a0 a1 a0 a1
        nat : (@tick z : BI) → primGel (snd tt,A0) (snd tt,A1) (snd tt,AA) z ≡ tt,A-bdg z .snd
        nat = λ z i → outEquGr (tt,A-prf) i z .snd
      in
      flip _∙_ (hav nat (transportRefl _) (transportRefl _))
      (funExt⁻ (funExt⁻ (sym (retEq relativity (tt,AA .snd))) a0) a1))))
  }

-- outEquGr tt,A-prf :
-- (λ x → tt , primGel (snd tt,A0) (snd tt,A1) (snd tt,AA) x) ≡
-- tt,A-bdg


module AsLookup {A0 A1 : Type} {AA : A0 → A1 → Type} where

  tolookup : ∀ j v0 v1 (vv : VecHetRel1 A0 A1 AA j v0 v1) (k : Fin j) → AA (lookup k v0) (lookup k v1)
  tolookup zero [] [] tt ()
  tolookup (suc j) (a0 ∷ v0) (a1 ∷ v1) aa,vv zero = aa,vv .fst
  tolookup (suc j) (a0 ∷ v0) (a1 ∷ v1) aa,vv (suc k) = tolookup j v0 v1 (aa,vv .snd) k

  toHetrel : ∀ j v0 v1 → ( (k : Fin j) → AA (lookup k v0) (lookup k v1) ) → VecHetRel1 A0 A1 AA j v0 v1
  toHetrel zero [] [] hyp = tt
  toHetrel (suc j) (a0 ∷ v0) (a1 ∷ v1) hyp = hyp zero , toHetrel j v0 v1 λ k → hyp (suc k)

  VecHetRel<=Lookup : ∀ j v0 v1 vv → toHetrel j v0 v1 (tolookup j v0 v1 vv) ≡ vv
  VecHetRel<=Lookup zero [] [] tt = refl
  VecHetRel<=Lookup (suc j) (a0 ∷ v0) (a1 ∷ v1) aa,vv =
    ΣPathP (refl , VecHetRel<=Lookup j v0 v1 (aa,vv .snd))

  Lookup<=VecHetRel : ∀ j v0 v1 (lkpHyp : (k : Fin j) → AA (lookup k v0) (lookup k v1)) (k : Fin j) →
    tolookup j v0 v1 (toHetrel j v0 v1 lkpHyp) k ≡ lkpHyp k
  Lookup<=VecHetRel zero [] [] lkpHyp ()
  Lookup<=VecHetRel (suc j) (a0 ∷ v0) (a1 ∷ v1) lkpHyp zero = refl
  Lookup<=VecHetRel (suc j) (a0 ∷ v0) (a1 ∷ v1) lkpHyp (suc k) =
    Lookup<=VecHetRel j v0 v1 (λ m → lkpHyp (suc m)) k

  VecHetRel1AsLookup : ∀ j v0 v1 →
    (VecHetRel1 A0 A1 AA j v0 v1) ≃ ( (k : Fin j) → AA (lookup k v0) (lookup k v1) )
  VecHetRel1AsLookup j v0 v1 =
    isoToEquiv (iso
    (λ vv → tolookup j v0 v1 vv)
    (λ lkpHyp → toHetrel j v0 v1 lkpHyp)
    (λ lkpHyp → funExt (Lookup<=VecHetRel j v0 v1 lkpHyp))
    λ vv → VecHetRel<=Lookup j v0 v1 vv)
open AsLookup public

-- VecHetRel-lookup : (A0 A1 : Type) (AA : A0 → A1 → Type) (j : ℕ) (v0 : Vec A0 j) (v1 : Vec A1 j) →
--   ( VecHetRel1 A0 A1 AA j v0 v1 ≃ ( (k : Fin j) → AA (lookup k v0) (lookup k v1) ) )
-- VecHetRel-lookup A0 A1 AA 0 [] [] =
--   isoToEquiv (iso
--   (λ _ k → rec (¬Fin0 k)) (λ _ → tt)
--   (λ _ → funExt λ k → rec (¬Fin0 k)) λ _ → refl)
-- VecHetRel-lookup A0 A1 AA (suc j) (a0 ∷ v0) (a1 ∷ v1) =
--   isoToEquiv (iso
--   {!λ aa,vv!} {!!} {!!} {!!})
--   where
--     toLookup : AA a0 a1 → VecHetRel1 A0 A1 AA j v0 v1 → (k : Fin (suc j)) → AA (lookup k (a0 ∷ v0)) (lookup k (a1 ∷ v1))
--     toLookup aa vv zero = aa
--     toLookup aa vv (suc k) = {!toLookup!}




-- δℕ j = [0 , 1 , ... , j - 1]
δℕ : ∀ j → Vec ℕ j
-- δℕ = {!!}
δℕ 0 = []
δℕ (suc j) = 0 ∷ (map suc (δℕ j))



lookups-δℕ : ∀ j k → lookup k (δℕ j) ≡ toℕ k
lookups-δℕ zero ()
lookups-δℕ (suc j) zero = refl
lookups-δℕ (suc j) (suc k) = lookupVec-map {k = k} ℕ.suc (δℕ j) ∙ cong suc (lookups-δℕ j k)

δFin : ∀ j → Vec (Fin j) j
--δFin = {!!}
δFin 0 = []
δFin (suc j) = zero ∷ map {B = Fin (suc j)} suc (δFin j)

-- δFinUpTo : ∀ j n → Vec (Fin (n + j)) j
-- δFinUpTo 0 n = []
-- δFinUpTo (suc j) n = {!!}

sameLookupsδ : ∀ j k → toℕ (lookup k (δFin j)) ≡ lookup k (δℕ j)
sameLookupsδ zero ()
sameLookupsδ (suc j) zero = refl
sameLookupsδ (suc j) (suc k) =
  cong toℕ (lookupVec-map {B = Fin (suc j)} {k = k} suc (δFin j)) ∙
  cong ℕ.suc (sameLookupsδ j k) ∙
  sym (lookupVec-map {B = ℕ} {k = k} suc (δℕ j))



-- [j-1, ... , 1, 0] : Vec (Fin (n + j)) j
revδF' : ∀ n j → Vec (Fin (n +' j)) j
revδF' n 0 = []
revδF' n (suc j) =
  <''ToFin (suc (n + j)) (j , j<''sucn+j j n) ∷
  subst (λ blk → Vec (Fin blk) j) (+'≡+ (suc n) j)
  (revδF' (suc n) j)

revδℕ : ∀ j → Vec ℕ j
revδℕ 0 = []
revδℕ (suc j) = j ∷ revδℕ j

sameLookupsRev' : ∀ n j k → toℕ (lookup k (revδF' n j)) ≡ lookup k (revδℕ j)
sameLookupsRev' n zero ()
sameLookupsRev' n (suc j) zero = toℕ-<''ToFin (suc (n + j)) j (j<''sucn+j j n)
sameLookupsRev' n (suc j) (suc k) =
  flip _∙_ (sameLookupsRev' (suc n) j k)
  λ i → toℕ (lookup k (subst-filler (λ blk → Vec (Fin blk) j) (+'≡+ (suc n) j) (revδF' (suc n) j) (~ i)))

revδF : ∀ n j → Vec (Fin (n + j)) j
revδF n j = subst (λ blk → Vec (Fin blk) j) (+'≡+ n j) (revδF' n j)

sameLookupsRev : ∀ n j k → toℕ (lookup k (revδF n j)) ≡ lookup k (revδℕ j)
sameLookupsRev n j k =
  flip _∙_ (sameLookupsRev' n j k)
  λ i → toℕ (lookup k (subst-filler (λ blk → Vec (Fin blk) j) (+'≡+ n j) (revδF' n j) (~ i)))

lookups-revδℕ : ∀ j (k : Fin j) → lookup k (revδℕ j) ≡ j ∸ (suc (toℕ k))
lookups-revδℕ zero ()
lookups-revδℕ (suc j) zero = refl
lookups-revδℕ (suc j) (suc k) = lookups-revδℕ j k






------------------------------------------------------------------------

-- a v ↦ v1,..vj, a
vecsnoc : ∀ {A : Type} {j : ℕ} → A → Vec A j → Vec A (suc j)
vecsnoc {j = 0} a [] = a ∷ []
vecsnoc {j = suc j} a (x ∷ v) = x ∷ vecsnoc a v

vecrev : {A : Type} {j : ℕ} → Vec A j → Vec A j
vecrev {j = 0} [] = []
vecrev {j = suc j} (a ∷ v) = vecsnoc a (vecrev v)


mylookup : ∀ {A : Type} {j} k (hypk : k <'' j) (v : Vec A j) → A
mylookup {j = 0} k ctr = rec ctr
mylookup {j = suc j} 0 _ (a ∷ v) = a
mylookup {j = suc j} (suc k) hypk (a ∷ v) = mylookup {j = j} k hypk v


my-lookup : ∀ {A : Type} j k (k<j : k <'' j) (v : Vec A j) →
  lookup (<''ToFin j (k , k<j)) v ≡ mylookup k k<j v
my-lookup (suc j) zero k<j (x ∷ v) = refl
my-lookup (suc j) (suc k) k<j (x ∷ v) = my-lookup j k k<j v


snoc-lemma : ∀ {V : Type} (n j : ℕ) (env' : Vec V n) (env : Vec V j) (v : V) →
  PathP (λ i → Vec V (+-suc n j i)) (env' ++ v ∷ env) (vecsnoc v env' ++ env)
snoc-lemma zero j [] env v = refl
snoc-lemma (suc n) j (x ∷ env') env v = λ i → x ∷ (snoc-lemma n j env' env v i)


mylookup-propirr : ∀ {V : Type} (j k0 k1 : ℕ) (kk : k0 ≡ k1)
  (hyp0 : k0 <'' j) (hyp1 : k1 <'' j) 
  (env0 : Vec V j) (env1 : Vec V j) (envv : env0 ≡ env1) →
  mylookup k0 hyp0 env0 ≡ mylookup k1 hyp1 env1
mylookup-propirr j k0 k1 kk hyp0 hyp1 env0 env1 envv =
  λ i → mylookup (kk i) (hetpath i) (envv i)
  where
    hetpath : PathP (λ i → (kk i) <'' j) hyp0 hyp1
    hetpath =
      isOfHLevelPathP' {A = λ i → (kk i) <'' j} 0 (<''isPropValued k1 j) hyp0 hyp1 .fst


mylookup-snoc : ∀ {V : Type} (n j : ℕ) (env' : Vec V n) (env : Vec V j) (v : V) →
  mylookup n (n<''sucn+j j n) (vecsnoc v env' ++ env) ≡ v
mylookup-snoc zero j [] env v = refl
mylookup-snoc (suc n) j (x ∷ env') env v =
  flip _∙_
    (mylookup-snoc n j env' env v)
    λ i → mylookup n (<''isPropValued n (suc (n + j)) (n<''sucn+j j (suc n)) (n<''sucn+j j n) i) (vecsnoc v env' ++ env)

mylookup-++ : ∀ {V : Type} (j n : ℕ) (k : ℕ) (hypk : k <'' j) --(pf : (n + k) <'' (n + j))
  (env : Vec V j) (env' : Vec V n) →
  mylookup (n + k) (<''+ n k j hypk) (env' ++ env) ≡ mylookup k hypk env
mylookup-++ (suc j) zero k hypk env [] =
  mylookup-propirr (suc j) k k refl _ hypk env env refl
mylookup-++ (suc j) (suc n) k hypk env (x ∷ env') =
  flip _∙_ (mylookup-++ (suc j) n k hypk env env')
  (mylookup-propirr  (n + (suc j)) (n + k) (n + k) refl _ _ (env' ++ env) (env' ++ env) refl)
