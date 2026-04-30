{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}


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

open import LambdaDefs
open import VecLemmas



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





-- FIRST ORDER models of untyped lambda calculus (no equations)
-- See LamChurch
-- (_ : 1) × (L : ℕ → Type) ×
--   (∀ n i → (i my< n ≡ true) → L n) ×
--   (∀ n → L (suc n) → L n) ×
--   (∀ n → Lam n → Lam n → Lam n)
FoModLam : Type₁
FoModLam = ModLamPresNRG .nrg-cr



    


------------------------------------------------------------------------


module NominalEnc≃HoEnc where

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


  Nenc→Hoenc : ∀ {j : ℕ} → ((VN : PhoasModLam j) → ncrOf VN) → ((H : HoasMod j) → hcr H)
  Nenc→Hoenc nch H = nch (HoasMod→PhoasModLam H)

  Hoenc→Nenc : ∀ {j : ℕ} → ((H : HoasMod j) → hcr H) → ((VN : PhoasModLam j) → ncrOf VN)
  Hoenc→Nenc hoch VN = hoch (PhoasModLam→HoasMod VN)

  -- Andreas: This can be proven already for the NRelators between the contexts.
  Hoenc<=Nenc : ∀ {j : ℕ} (hoch : ((H : HoasMod j) → hcr H)) →
    hoch ≡ Nenc→Hoenc (Hoenc→Nenc hoch)
  --funExt λ H → refl
  Hoenc<=Nenc hoch = funExt λ H →
    funExtDep⁻ {A = λ _ → HoasMod _} {B = λ i → hcr} {f = hoch} {g = hoch} refl
    (ΣPathP (refl ,
    ΣPathP (sym (mapvec-id (henvOf H)) ,
    refl)))


  Nenc<=Hoenc : ∀ {j : ℕ} → (nch : ((VN : PhoasModLam j) → ncrOf VN)) →
    nch ≡ Hoenc→Nenc (Nenc→Hoenc nch)
  Nenc<=Hoenc nch = funExt λ VN →
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
    Hoenc→Nenc
    Nenc→Hoenc
    (λ nch → sym (Nenc<=Hoenc nch))
    λ hoch → sym (Hoenc<=Nenc hoch))


open NominalEnc≃HoEnc public









-- module Batch1 where

--   HoasMod' = Σ Type (λ X → ((X → X) → X) × (X → X → X))

--   HoasModm = Σ Type (λ X →
--     (∀ n i → (i my< n ≡ true) → Vec X n → X) ×
--     ((X → X) → X) ×
--     (X → X → X))

--   FoModLamm = Σ (ℕ → Type) (λ L →
--     (∀ n i → (i my< n ≡ true) → L n) ×
--     (∀ n → L (suc n) → L n) ×
--     (∀ n → L n → L n → L n))

--   varHof : (H : HoasModm) → (∀ n i → (i my< n ≡ true) → Vec (H .fst) n → H .fst)
--   varHof H = H .snd .fst

--   appHof : (H : HoasModm) → H .fst → H .fst → H .fst
--   appHof H = H .snd .snd .snd

--   lamHof : (H : HoasModm) → (H .fst → H .fst) → H .fst
--   lamHof H = H .snd .snd .fst

--   famOof : (M : FoModLamm) → ℕ → Type
--   famOof M = M .fst

--   varOof : (M : FoModLamm) → (∀ n i → (i my< n ≡ true) → famOof M n)
--   varOof M = M .snd .fst

--   lamOof : (M : FoModLamm) → (∀ n → famOof M (suc n) → famOof M n)
--   lamOof M = M .snd .snd .fst

--   appOof : (M : FoModLamm) → (∀ n → famOof M n → famOof M n → famOof M n)
--   appOof M = M .snd .snd .snd


--   -- (n i : ℕ) → (i my< n) ≡ true → Vec (H .fst) n → H .fst
--   toFo : HoasModm → FoModLamm
--   toFo H =
--     ((λ n → Vec (H .fst) n → H .fst)) ,
--     varHof H ,
--     (λ n bod env → lamHof H (λ h → bod (h ∷ env))) ,
--     λ n u v env → appHof H (u env) (v env)


--   toHo : FoModLamm → HoasModm
--   toHo M =
--     (∀ n → famOof M n) ,
--     (λ n i hyp hs → lookup (asFin n i hyp) hs ) ,
--     (λ f i → lamOof M i (flip f (suc i) (aux i))) ,
--     λ u v n → appOof M n (u n) (v n)
--     where
--       aux : ∀ (i j : ℕ) → famOof M j
--       --Cheating a bit. "Crucially it is always the case that j>i",  in [Atkey] "Syntax for free"  
--       --The hope here is that the rhs below when will never be used when j <= i
--       aux i 0 = lamOof M _ (varOof M 1 0 refl)  
--       aux i (suc j) = varOof M (suc j) (j ∸ (suc i)) (my<AND∸ (suc i) j)



--   toHoChurch : ∀ n → ((M : FoModLamm) → famOof M n) → ((H : HoasModm) → Vec (H .fst) n → H .fst)
--   toHoChurch n foCh H = foCh (toFo H)


--   toFoChurch0 : ((H : HoasModm) → H .fst) → ((M : FoModLamm) → famOof M 0)
--   toFoChurch0 hoCh M = hoCh (toHo M) 0


--   -- fo<=ho : ∀ (foCh : (M : FoModLam) → famOof M 0) →
--   --   foCh ≡
--   --   (toFoChurch0 (λ H → (toHoChurch 0 foCh) H []))
--   -- fo<=ho foCh = funExt λ M →
--   --   {!toFoChurch0 (λ H → toHoChurch 0 foCh H []) M!}

--   -- -- maybe: famOof

-- ------------------------------------------------------------------------


-- module Batch2 where


--   -- "contextualization"
--   -- H ↦ λn. H^n → H
--   toFoMod : HoasMod → FoModLam
--   toFoMod H = (tt ,
--               λ n → Vec (hcr H) n → (hcr H)) ,
--               (λ n i hyp env → lookup  (asFin n i hyp) env) ,
--               (λ n body env → hlamOf H λ h → body (h ∷ env) ) ,
--               λ n u v env → happOf H (u env) (v env)


--   -- -- L : ℕ → Type ↦ ∀n. L n
--   -- toHoMod : FoModLam → HoasMod
--   -- toHoMod M = (tt ,
--   --             (∀ n → famOf M n)) ,
--   --             (λ f i → lamOf M i (flip f (suc i) expr)) ,
--   --             λ u v n → applOf M n (u n) (v n)
--   --   where
--   --     expr : ∀ j → famOf M j
--   --     expr = {!!}

--   -- L : ℕ → Type ↦ ∀ n m. L(n + m)
--   -- toHoMod2 : FoModLam → HoasMod
--   -- toHoMod2 M = (tt ,
--   --              ∀ n m → famOf M (n + m)) ,
--   --              (λ body ctx pad →
--   --                {!!}) ,
--   --              λ u v → λ n m → applOf M (n + m) (u n m) (v n m)
--   --   where
--   --     itlam : ∀ i j → famOf M (i + j) → famOf M i
--   --     itlam = {!!}



--   -- toHoChurch : (∀ M → famOf M 0) → (∀ H → hcr H)
--   -- toHoChurch foCh H = foCh (toFoMod H) []

--   -- toFoChurch : (∀ H → hcr H) → (∀ M → famOf M 0)
--   -- toFoChurch hoCh M = hoCh (toHoMod M) 0


--   -- fo<=ho : ∀ (foCh : (∀ M → famOf M 0)) →
--   --   foCh ≡ toFoChurch ((toHoChurch foCh))
--   -- fo<=ho foCh = funExt λ M → {!!}


--   -- foGph : ∀ M → ModLamPresNRG ⦅ M , toFoMod (toHoMod M) ⦆
--   -- foGph M = (tt ,
--   --           (λ n0 n1 nn t0 {- : famOf M n0 -} b1 {- : Vec (∀n. Ln) n1 → ∀n. Ln -} →
--   --             {!!})) ,
--   --           {!!} ,
--   --           {!!} ,
--   --           {!!}


--   ------------------------------------------------------------------------
--   -- tentative reprodcution of [Atkey] "Syntax for free"
--   -- note: we don't have kripke param

--   Lam→HoChurch :  ∀ n → Lam n → (∀ H → Vec (hcr H) n → hcr H)
--   Lam→HoChurch n (appl .n u v) H env = happOf H (Lam→HoChurch n u H env) (Lam→HoChurch n v H env)
--   Lam→HoChurch n (var .n i hyp) H env = lookup (asFin n i hyp) env
--   Lam→HoChurch n (lam .n bod) H env =
--     hlamOf H λ h →
--       Lam→HoChurch (suc n) bod H -- Vec n+1 → Vec n
--         ( h ∷ env )


--   -- -- can Lam be turned into a higher order model itself??
--   -- hoChurch→Lam0 : (∀ H → hcr H) → Lam 0
--   -- hoChurch→Lam0 hoCh = hoCh LamAsHomod 0
--   --   where
--   --     aux : ∀ i j → Lam j
--   --     aux i 0 = lam _ (var 1 0 refl)   --weird when j<= i
--   --     aux i (suc j) = var (suc j) (j ∸ (suc i)) (my<AND∸ (suc i) j)

--   --     LamAsHomod : HoasMod
--   --     LamAsHomod = (tt ,
--   --                  (∀ n → Lam n)) ,
--   --                  (λ f i → lam i (flip f (suc i) (aux i))) ,
--   --                  λ u v i → appl i (u i) (v i)


--   -- hoChurch→Lam : ∀ n → (∀ H → Vec (hcr H) n → hcr H) → Lam n
--   -- hoChurch→Lam n hoCh-n = {!!}
--   --   where
--   --     aux : ∀ i j → Lam j
--   --     aux i 0 = lam _ (var 1 0 refl)   --weird when j<= i
--   --     aux i (suc j) = var (suc j) (j ∸ (suc i)) (my<AND∸ (suc i) j)

--   --     LamAsHomod : HoasMod
--   --     LamAsHomod = (tt ,
--   --                  (∀ n → Lam n)) ,
--   --                  (λ f i → lam i (flip f (suc i) (aux i))) ,
--   --                  λ u v i → appl i (u i) (v i)



--   -- Lam0<=hoChurch : ∀ (t : Lam 0) → t ≡ hoChurch→Lam0 (λ H → (Lam→HoChurch 0 t H []))
--   -- Lam0<=hoChurch (var .0 i ctr) = rec (not<0 i ctr)
--   -- Lam0<=hoChurch (lam .0 bod) = {!!}
--   -- Lam0<=hoChurch (appl .0 u v) = cong₂ (appl 0) (Lam0<=hoChurch u) (Lam0<=hoChurch v)









-- module Junk where

--   NOpnMod : ℕ → Type → Type₁
--   NOpnMod n V = Σ[ N ∈ Type ] (
--     (Fin n → N) ×
--     (V → N) ×
--     (N → N → N) ×
--     ((V → N) → N)
--     )

--   NIdxMod = Σ[ V ∈ Type ] Σ[ K ∈ (ℕ → Type) ] (
--     (∀ n → Fin n → K n) ×
--     (∀ n → V → K n) ×
--     (∀ n → K n → K n → K n) ×
--     (∀ n → (V → K n) → K n)
--     )

--   toNOpnMod : NIdxMod → (Σ[ V ∈ Type ] (∀ n → NOpnMod n V))
--   toNOpnMod Nx = Nx .fst , λ n → 
--     let K = Nx .snd .fst in
--     K n ,
--     Nx .snd .snd .fst n ,
--     Nx .snd .snd .snd .fst n ,
--     Nx .snd .snd .snd .snd .fst n ,
--     Nx .snd .snd .snd .snd .snd n

--   toNIdxMod : (Σ[ V ∈ Type ] (∀ n → NOpnMod n V)) → NIdxMod
--   toNIdxMod Vbla =
--     Vbla .fst ,
--     (λ n → Vbla .snd n .fst) ,
--     (λ n → Vbla .snd n .snd .fst) ,
--     (λ n → Vbla .snd n .snd .snd .fst) ,
--     (λ n → Vbla .snd n .snd .snd .snd .fst) ,
--     λ n → Vbla .snd n .snd .snd .snd .snd

--   NIdxMod<= : ∀ (VK : NIdxMod) → toNIdxMod (toNOpnMod VK) ≡ VK
--   NIdxMod<= VK = refl -- ΣPathP (refl , refl)

--   NOpnMod<= : ∀ (VN : (Σ[ V ∈ Type ] (∀ n → NOpnMod n V))) →  toNOpnMod(toNIdxMod VN) ≡ VN
--   NOpnMod<= VN = refl
