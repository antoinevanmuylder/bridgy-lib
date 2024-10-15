{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module VoigtlanderTheorems where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.List
open import Bridgy.Core.GelExamples
open import Bridgy.Core.EquGraph
open import Bridgy.Core.BDisc 

open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.MoreVarRules
open import Bridgy.ROTT.Param

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.List hiding ( [_] )
open import Cubical.Data.Sigma

postulate
  l : Level
  A : Type l
  hasbA : isBDisc A

-- In this file: formalisation of the first five theorems of
-- Janis Voigtländer's "Free Theorems Involving Type Constructor Classes"
-- concerning effect parametricity (i.e. quantification over premonads)
-- Theorems 1-4 deal with effect polymorphic programs of type
-- ∀ (κ : PMnd) → List (κ A) → κ A

------------------------------------------------------------------------
-- Preliminaries 

-- Type of premonads (we write for PMnd for the type of premonads and pmnd for the type transformer)

PMnd : Type (ℓ-suc l)
PMnd = Σ (Type l → Type l) (λ pmnd → ((X : Type l) → X → pmnd X)
  × ((X Y : Type l) → pmnd X → (X → pmnd Y) → pmnd Y))

pmnd : (κ : PMnd) → Type l → Type l
pmnd κ = κ .fst

ret : (κ : PMnd) → (X : Type l) → X → pmnd κ X
ret κ = κ .snd .fst

bind : (κ : PMnd) → (X Y : Type l) → pmnd κ  X → (X → pmnd κ Y) → pmnd κ Y
bind κ = κ .snd .snd

-- Identity premonad (used for theorems 1-2)

IdPmnd : PMnd
IdPmnd = (λ X → X) , (λ X x → x) , λ X Y x k → k x

-- Type of premonad morphisms (used for theorems 3-4)

record PMndMorphism (κ0 κ1 : PMnd) : Type (ℓ-suc l) where
  field
    morphism : (X : Type l) → pmnd κ0 X → pmnd κ1 X 
    morphismRet : (X : Type l) (x : X) → morphism X (ret κ0 X x) ≡ ret κ1 X x  
    morphismBind :  (X Y : Type l) (κx0 : pmnd κ0 X) (k : X → pmnd κ0 Y) →
      morphism Y (bind κ0 X Y κx0 k) ≡ bind κ1 X Y (morphism X κx0) ((morphism Y) ∘ k)
open PMndMorphism public

------------------------------------------------------------------------
-- Constructing the premonad NRG and dNRG

-- Premonad NRG

Unit,pmnd : NRGraph (ℓ-suc l)
Unit,pmnd = topNRG # (→Form _ _ (UForm l) (UForm l))

retDNRG : DispNRG (ℓ-suc l) Unit,pmnd
retDNRG = ΠForm (UForm l) 
  (→Form _ _
    -- X : Type
    (El (let v = var0 Unit,pmnd (UForm l) 
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
    -- κ X
    (El (app (Unit,pmnd # (UForm l)) (UForm l) (UForm l)
      -- κ : Type → Type
      (let v = var1 {Γ = topNRG} (→Form _ _ (UForm l) (UForm l)) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      -- X 
      let v = var0 Unit,pmnd (UForm l) 
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))

bindDNRG : DispNRG (ℓ-suc l) Unit,pmnd
bindDNRG = ΠForm (UForm l) (ΠForm (UForm l) 
  (→Form _ _
    -- κ X
    (El (app _ (UForm l) (UForm l)
      --κ
      (let v = var2 topNRG (→Form _ _ (UForm l) (UForm l)) (UForm l) (UForm l) 
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ } )
      -- X
      let v = var1 {Γ = Unit,pmnd} (UForm l) (UForm l) 
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
  -- (X → κ Y) → κ Y
  (→Form _ _
    -- X → κ Y
    (→Form _ _
      (El (let v = var1 {Γ = Unit,pmnd} (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
    (El (app ((Unit,pmnd # (UForm l)) # (UForm l)) (UForm l) (UForm l)
      (let v = var2 topNRG (→Form _ _ (UForm l) (UForm l)) (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    let v = var0 (Unit,pmnd # (UForm l)) (UForm l)
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))
  -- κ Y
  (El (app ((Unit,pmnd # (UForm l)) # (UForm l)) (UForm l) (UForm l)
    (let v = var2 topNRG (→Form _ _ (UForm l) (UForm l)) (UForm l) (UForm l)
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
  let v = var0 (Unit,pmnd # (UForm l)) (UForm l)
  in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))))

PMndNRG : NRGraph (ℓ-suc l)
PMndNRG = Unit,pmnd # (×Form _ _ retDNRG bindDNRG)

-- Renaming for readability

PMnd→cr : (κ : PMnd) → PMndNRG .nrg-cr
PMnd→cr κ = ((tt , pmnd κ) , ret κ , bind κ)

NRGpmnd : (κ : PMndNRG .nrg-cr) → Type l → Type l
NRGpmnd κ = κ .fst .snd

NRGret : (κ : PMndNRG .nrg-cr) → (X : Type l) → X → NRGpmnd κ X
NRGret κ = κ .snd .fst

NRGbind : (κ : PMndNRG .nrg-cr) → (X Y : Type l) → NRGpmnd κ  X → (X → NRGpmnd κ Y) → NRGpmnd κ Y
NRGbind κ = κ .snd .snd

-- dNRG (∀ (κ : PMnd) → List (κ A) → κ A)

voigtDNRG : DispNRG l PMndNRG
voigtDNRG = wkn (→Form _ _
  -- List (κ A)
  (ListdNRG' (El (app Unit,pmnd (UForm l) (UForm l)
    (let v = var0 topNRG (→Form _ _ (UForm l) (UForm l))
    in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ})
      --A
      (code (bDisc-asDNRG A hasbA)))))
  -- κ A
  (El (app Unit,pmnd (UForm l) (UForm l)
  (let v = var0 topNRG (→Form _ _ (UForm l) (UForm l))
   in record {tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ})
     -- A
     (code (bDisc-asDNRG A hasbA)))))

------------------------------------------------------------------------
-- Theorem 1: if f : ∀ (κ : PMnd) → List (κ A) → κ A and if κas : List (κ A) is a
-- pure list (i.e. all monadic compuations are return values) then the output of f (f κ κas)
-- is pure as well

module theorem1
  (f : ∀ (κ : PMndNRG .nrg-cr) → List (NRGpmnd κ A) → NRGpmnd κ A)
  (κ : PMnd)
  -- The following monad law is required to prove the compatibilty of bind with
  -- the chosen logical relation
  (law1-κ : ∀ (X Y : Type l) (x : X) (k : X → pmnd κ Y) → (bind κ X Y (ret κ X x) k) ≡ k x)
  where

-- Definition of a pure value and list

  pureval : pmnd κ A → Type l
  pureval κa = Σ A (λ a → κa ≡ ret κ A a)

  purelist : List (pmnd κ A) → Type l
  purelist [] = Lift Unit
  purelist (κa ∷ κas) = pureval κa × (purelist κas)

-- If a list of monadic compuations is pure, then giveVals returns a list of ordinary values

  giveVals : (κas : List (pmnd κ A)) (plis : purelist κas) → List A
  giveVals [] _ = []
  giveVals (κa ∷ κas) (pκa , pκas) = (pκa .fst) ∷ giveVals κas pκas

-- Logical relation between κ and IdPmnd

  edge-κ-Id : PMndNRG .nedge (PMnd→cr κ) (PMnd→cr IdPmnd)
  edge-κ-Id = (tt , λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (ret κ X0 x0 ≡ κx0) × (XX x0 x1))) , --pmnd
    (λ X0 X1 XX x0 x1 xx → x0 , refl , xx) , --ret
    λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
        let
          hypk-fwd : Σ Y0 (λ y0 → (ret κ Y0 y0 ≡ k0 (hyp .fst)) × YY y0 (k1 x1))
          hypk-fwd  = hypk (hyp .fst) x1 (hyp .snd .snd)
         
          dedct1 : ret κ X0 (hyp .fst) ≡ κx0
          dedct1 = hyp .snd .fst in

        hypk-fwd .fst ,
        ((hypk-fwd .snd .fst) ∙ (sym (law1-κ X0 Y0 (hyp .fst) k0)))
        ∙ cong (λ blank → bind κ X0 Y0 blank k0) dedct1  ,
        hypk-fwd .snd .snd --bind

-- Call to param

  Theorem1 : ∀ (κas : List (pmnd κ A)) → purelist κas →
    pureval (f (PMnd→cr κ) κas)
  Theorem1 κas plis =
    let
      partialParam = param PMndNRG voigtDNRG f (PMnd→cr κ) (PMnd→cr IdPmnd) edge-κ-Id
        κas (giveVals κas plis) (aux κas plis)
    in
    partialParam .fst , sym (partialParam .snd .fst)

    where

      aux : ∀ κas plis →
       ListRCover
       (λ κx0 x1 → Σ A (λ x0 → (ret κ A x0 ≡ κx0) × Path A x0 x1)) κas
       (giveVals κas plis)
      aux [] _ = lift tt
      aux (κa ∷ κas) (pκa , pκas) =
        (pκa .fst , (sym (pκa .snd)) , refl) ,
        aux κas pκas

------------------------------------------------------------------------
-- Theorem 2: if f : ∀ (κ : PMnd) → List (κ A) → κ A and if we have a program that can
-- extract monadic computations (p : (X : Type) → κ X → X) then the following equality holds:
-- p A (f κ κas) ≡ f IdPmnd (map (p A) κas)

module VOIGT2
  (f : ∀ (κ : PMndNRG .nrg-cr) → List (NRGpmnd κ A) → NRGpmnd κ A)
  (κ : PMnd)
  (p : ∀ (X : Type l) → pmnd κ X → X)
  -- eq1 is needed to prove the compatibility of ret
  (eq1 : ∀ (X : Type l) (x : X) → (p X (ret κ X x)) ≡ x)
  -- eq2 is needed to prove the compatibility of bind
  (eq2 : ∀ (X : Type l) (Y : Type l) (κx : pmnd κ X) (q : X → pmnd κ Y)
    → p Y (bind κ X Y κx q) ≡ p Y (q (p X  κx)))
  where

-- Logical relation between κ and IdPmnd

  edge-κ-Id : PMndNRG .nedge (PMnd→cr κ) (PMnd→cr IdPmnd)
  edge-κ-Id = (tt , λ X0 X1 XX κx0 x1 → Σ X0 (λ x0 → (p X0 κx0 ≡ x0) × (XX x0 x1))) , --pmnd
    (λ X0 X1 XX x0 x1 xx → x0 , eq1 X0 x0 , xx) , --ret
    λ X0 X1 XX Y0 Y1 YY κx0 x1 hyp k0 k1 hypk →
        let
          hypk-fwd : Σ Y0 (λ y0 → (p Y0 (k0 (hyp .fst)) ≡ y0) × YY y0 (k1 x1))
          hypk-fwd  = hypk (hyp .fst) x1 (hyp .snd .snd)
         
          dedct1 : p X0 κx0 ≡ hyp .fst
          dedct1 = hyp .snd .fst

          apEq2 : p Y0 (bind κ X0 Y0 κx0 k0) ≡ p Y0 (k0 (p X0 κx0))
          apEq2 = eq2 X0 Y0 κx0 k0 in

        hypk-fwd .fst ,
        sym (sym (cong (p Y0) (cong k0 dedct1) ∙ hypk-fwd .snd .fst) ∙ sym apEq2)  ,
        hypk-fwd .snd .snd --bind

-- Call to param

  Theorem2 : ∀ (κas : List (pmnd κ A)) → p A (f (PMnd→cr κ) κas) ≡ f (PMnd→cr IdPmnd) (map (p A) κas)
  Theorem2 κas = 
    let
      partialParam = param PMndNRG voigtDNRG f (PMnd→cr κ) (PMnd→cr IdPmnd) edge-κ-Id κas (map (p A) κas) (aux κas) 
    in
    partialParam .snd .fst ∙ partialParam .snd .snd

    where

      aux : ∀ (κas : List (κ .fst A)) → ListRCover (λ κx0 x1 → Σ A (λ x0 → (p A κx0 ≡ x0) × Path A x0 x1)) κas (map (p A) κas)
      aux [] = lift tt
      aux (κa ∷ κas) = (p A κa , refl , refl) , aux κas

------------------------------------------------------------------------
-- Theorem 3: if f : ∀ (κ : PMnd) → List (κ A) → κ A and h is a premonad morphism between
-- premonads κ1 and κ2, then f commutes with h

module VOIGT3
  (f : ∀ (κ : PMndNRG .nrg-cr) → List (NRGpmnd κ A) → NRGpmnd κ A)
  (κ1 κ2 : PMnd) 
  (h : PMndMorphism κ1 κ2)
  where

-- We will also need to assume that κ2 preserves bridge discreteness

  postulate
    hasbκ2A : isBDisc (pmnd κ2 A)  

-- And that κ2 acts as a native relator

  -- Canonical endo edge of κ2 obtained from refl bridge
  κ2ac : PMndNRG .nedge (PMnd→cr κ2) (PMnd→cr κ2)
  κ2ac = invEq (PMndNRG .nativ (PMnd→cr κ2) (PMnd→cr κ2)) λ a → (PMnd→cr κ2)
  
  
  κ2acNativRel = (g0 g1 : Type l) (gg : TypeNRG l ⦅ g0 , g1 ⦆)
    (gbdg : BridgeP (λ _ → Type l) g0 g1) →
    gg [ relativity ] gbdg → κ2ac .fst .snd g0 g1 gg [ relativity ] (λ x → pmnd κ2 (gbdg x))

  postulate
    κ2acnativrel : κ2acNativRel

-- Logical relation between κ2 and κ1

  edge-κ2-κ1 : PMndNRG .nedge (PMnd→cr κ2) (PMnd→cr κ1)
  edge-κ2-κ1 = (tt , λ X0 X1 XX κ2x0 κ1x1 → Σ (pmnd κ2 X1) (λ κ2x1 →
    (κ2ac .fst .snd X0 X1 XX κ2x0 κ2x1) × (κ2x1 ≡ h .morphism X1 κ1x1))) , --pmnd
    (λ X0 X1 XX x0 x1 xx → ret κ2 X1 x1 , κ2ac .snd .fst X0 X1 XX x0 x1 xx ,
    sym (h .morphismRet X1 x1)) , --ret
    (λ X0 X1 XX Y0 Y1 YY κ2x0 κ1x1 hyp k0 k1 hypk →
    bind κ2 X1 Y1 (hyp .fst) (λ x1 → h .morphism Y1 (k1 x1)) ,
    κ2ac .snd .snd X0 X1 XX Y0 Y1 YY κ2x0 (hyp .fst) (hyp .snd .fst) k0
    (λ x1 → h .morphism Y1 (k1 x1)) (λ x0 x1 xx →
      let
        hypk-fwd = Σ (pmnd κ2 Y1) (λ κ2x1 →
          κ2ac .fst .snd Y0 Y1 YY (k0 x0) κ2x1 × (κ2x1 ≡ h .morphism Y1 (k1 x1)))
        hypk-fwd = hypk x0 x1 xx in

    transport (cong (κ2ac .fst .snd Y0 Y1 YY (k0 x0)) (hypk-fwd .snd .snd)) (hypk-fwd .snd .fst)) ,
    cong (λ blank → bind κ2 X1 Y1 blank (h .morphism Y1 ∘ k1)) (hyp .snd .snd) ∙
    sym (h .morphismBind X1 Y1 κ1x1 k1)) --bind

  Theorem3 : ∀ (κas : List (pmnd κ1 A))
    → f  (PMnd→cr κ2) (map (h .morphism A) κas )  ≡ h .morphism A (f (PMnd→cr κ1) κas)
  Theorem3 κas =
    let partialParam = param PMndNRG voigtDNRG f (PMnd→cr κ2) (PMnd→cr κ1) edge-κ2-κ1
          (map (h .morphism A) κas) κas (aux κas) in   
       
    (transport (eq (f (PMnd→cr κ2) (map (h .morphism A) κas)) (partialParam .fst))
      (partialParam .snd .fst)) ∙ partialParam .snd .snd  

      where

-- partialParam gives us something of the form κ2ac .fst .snd A A (Path A) _ _, while we require
-- something of the form Path (pmnd κ2 A) _ _.
-- To obtain this we can use our two assumptions we made earlier

      from-A-bdsc : κ2ac .fst .snd A A (Path A) ≡ κ2ac .fst .snd A A (Bridge A)
      from-A-bdsc = cong (κ2ac .fst .snd A A)
        (funExt λ a0 → funExt λ a1 → ua (isBDisc→equiv A hasbA a0 a1))

      from-κ2-nrel : κ2ac .fst .snd A A (Bridge A) ≡ BridgeP (λ x → pmnd κ2 A)
      from-κ2-nrel = outEquGrInv (κ2acnativrel A A (Bridge A) (λ _ → A) (inEquGrInv refl))

      from-κ2-bdsc : Bridge (pmnd κ2 A) ≡ Path (pmnd κ2 A)
      from-κ2-bdsc = funExt λ v0 → funExt λ v1 → sym (ua (isBDisc→equiv (pmnd κ2 A) hasbκ2A v0 v1))

      together : κ2ac .fst .snd A A (Path A) ≡ Path (pmnd κ2 A)
      together = from-A-bdsc ∙ from-κ2-nrel ∙ from-κ2-bdsc

      eq : (x y : pmnd κ2 A) →  κ2ac .fst .snd A A (Path A) x y ≡ Path (pmnd κ2 A) x y 
      eq x y = cong (λ blank → blank y) (cong (λ blank → blank x) together)

      aux : ∀ (κas : List (pmnd κ1 A)) →
        ListRCover (edge-κ2-κ1 .fst .snd A A (Path A)) (map (h .morphism A) κas) κas
      aux [] = lift tt
      aux (κa ∷ κas) = (h .morphism A κa ,
        transport (sym (eq (h .morphism A κa) (h .morphism A κa))) refl , refl) ,
        aux κas

-- As a corollary from theorem 3 we obtain theorem 4: given two lists of monadic compuations
-- κas1 and κas2, if h applied to κas1 equals h applied to κas2, then h applied to f κ1 κas1 equals
-- h applied to f κ2 κas2

  Theorem4 : ∀ (κas1 κas2 : List (pmnd κ1 A)) → map (h .morphism A) κas1 ≡ map (h .morphism A) κas2
    → h .morphism A (f (PMnd→cr κ1) κas1) ≡ h .morphism A (f (PMnd→cr κ1) κas2)
  Theorem4  κas1 κas2 eq = sym (Theorem3 κas1) ∙ cong (f (PMnd→cr κ2)) eq ∙ Theorem3 κas2

