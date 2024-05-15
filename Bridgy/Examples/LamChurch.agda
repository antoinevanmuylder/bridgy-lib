{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}



module Bridgy.Examples.LamChurch where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
--open import Cubical.Data.FinData.Base
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit



open import Bridgy.Core.EquGraph
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.Bool

open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.MoreRules
open import Bridgy.ROTT.MoreVarRules


_my<_ : ℕ → ℕ → Bool
0 my< 0 = false
0 my< (suc n) = true
(suc n) my< 0 = false
(suc n) my< (suc m) = n my< m

data Lam : ℕ → Type where
  var : ∀ n i → (i my< n ≡ true) → Lam n
  lam : ∀ n → Lam (suc n) → Lam n
  appl : ∀ n → Lam n → Lam n → Lam n

------------------------------------------------------------------------
-- lemmas


not<0' : ∀ i → (i my< 0) ≡ false
not<0' 0 = refl
not<0' (suc n) = refl

not<0 : ∀ i → ((i my< 0) ≡ true) → ⊥
not<0 i ctr = false≢true (sym (not<0' i) ∙ ctr) 



-- turn the above into a term of ROTT (in an arbitrary context)
-- Γ ⊨ < : nat → nat → Bool
my<Term : ∀ {l} {Γ : NRGraph l} → TermDNRG Γ (→Form _ _ NatForm (→Form _ _ NatForm (BoolForm)))
my<Term = record {
  tm0 = λ _ n m → n my< m  ;
  tm1 = λ _ _ _ → tm1my< ;
  tm-nativ = λ _ _ _ _ _ →
    -- can shortcut by observing that Bool is an hset.
    inEquGrInv (funExt λ n0 → funExt λ n1 → funExt λ nn →  funExt λ m0 →  funExt λ m1 → funExt λ mm → isOfHLevelRespectEquiv 1 (Bool≡≃ _ _) (isSetBool _ _) _ _ )
  }
  where
    tm1my< : ∀ n0 n1 (nn : codeℕ n0 n1) m0 m1 (mm : codeℕ m0 m1) → Bool~ (n0 my< m0) (n1 my< m1)
    tm1my< 0 (suc n) ctr = rec ctr
    tm1my< (suc n) 0 ctr = rec ctr
    tm1my< _ _ _ 0 (suc m) ctr = rec ctr
    tm1my< _ _ _ (suc m) 0 ctr = rec ctr
    tm1my< zero zero nn zero zero mm = tt
    tm1my< zero zero nn (suc m0) (suc m1) mm = tt
    tm1my< (suc n0) (suc n1) nn zero zero mm = tt
    tm1my< (suc n0) (suc n1) nn (suc m0) (suc m1) mm =
      tm1my< n0 n1 nn m0 m1 mm


    
------------------------------------------------------------------------
-- a presentation of the theory of lambda terms, written as a dNRG
-- _:1 , L : ℕ → Type ⊨ (∀ n i → (i my< n ≡ true) → L n) × (∀ n → L (suc n) → L n) × (∀ n → Lam n → Lam n → Lam n)
-- we proceed in three steps.

varDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
varDNRG = ΠForm (NatForm) (ΠForm (NatForm)
  (→Form _ _
  -- (i my< n ≡ true)
  (≡Form (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm # NatForm) BoolForm
    (app2 my<Term
      (let v = var0 ctx13 NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      let v = var1 {Γ = ctx23} NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    (boolCons true))
  -- L n
  (El (app _ NatForm (UForm ℓ-zero)
    (let v = var2 topNRG (→Form _ _ (NatForm) (UForm ℓ-zero)) NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
  let v = var1 {Γ = topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero))} NatForm NatForm in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))

  where
    ctx03 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm # NatForm)
    ctx13  = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm)
    ctx23 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)

-- (∀ n → L (suc n) → L n)
lamDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
lamDNRG = ΠForm NatForm (
  let
    n = var0 ctx12 NatForm
    L = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)) NatForm
  in
  →Form _ _
  -- L (suc n)
  (El (app ctx02 NatForm (UForm ℓ-zero)
    (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ })
    (app _ _ _ sucTerm (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ }))))

  -- L n
  (El (app ctx02 NatForm (UForm ℓ-zero)
    (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ })
    (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ }))))

  where

    ctx12 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero))
    ctx02 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm



-- (∀ n → Lam n → Lam n → Lam n)
applDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
applDNRG = ΠForm NatForm
  let
    n = var0 ctx12 NatForm
    L = var1 {Γ = topNRG} (→Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero)) NatForm
    localApp' = app ctx02 NatForm (UForm ℓ-zero)
    localApp = (El (localApp' (record { tm0 = L .tm0 ; tm1 = L .tm1 ; tm-nativ = L .tm-nativ }) (record { tm0 = n .tm0 ; tm1 = n .tm1 ; tm-nativ = n .tm-nativ })))
  in
  →Form _ _ localApp (→Form _ _ localApp localApp)

  where
    ctx12 = (topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero))
    ctx02 = topNRG # →Form ℓ-zero (ℓ-suc ℓ-zero) NatForm (UForm ℓ-zero) # NatForm

      
-- _:1 , L : ℕ → Type ⊨ (∀ n i → (i my< n ≡ true) → L n) × (∀ n → L (suc n) → L n) × (∀ n → Lam n → Lam n → Lam n)
LamPresDNRG : DispNRG ℓ-zero (topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)))
LamPresDNRG = ×Form _ _ varDNRG (×Form _ _ lamDNRG applDNRG)


-- the models of lambda calculus,
-- more precisely of LamPres
-- these are the families L : ℕ → Type equipped with operations var, lam, appl
ModLamPresNRG : NRGraph (ℓ-suc ℓ-zero)
ModLamPresNRG = topNRG # (→Form _ _ (NatForm) (UForm ℓ-zero)) # LamPresDNRG

module _ (M : ModLamPresNRG .nrg-cr) where
  famOf = M .fst .snd
  varOf = M .snd .fst
  lamOf = M .snd .snd .fst
  applOf = M .snd .snd .snd


-- for each n of Agda bridges, the dNRG
-- tt:1, L : ℕ → Type, ...   ⊨  L n
idxCarrier : ℕ → DispNRG _ ModLamPresNRG
idxCarrier n = El (app ModLamPresNRG (NatForm) (UForm ℓ-zero)
  ((let v = var1 {Γ = topNRG} (→Form _ _ (NatForm) (UForm ℓ-zero)) LamPresDNRG in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })) 
  (cstNatTerm n))


-- registering Lam as a model
LamAsMod : ModLamPresNRG .nrg-cr
LamAsMod = (tt , Lam) , var , lam , appl


-- recursion principle with heterogeneous indices
LamRec : (M : ModLamPresNRG .nrg-cr) (n0 n1 : ℕ) → codeℕ n0 n1 → Lam n0 → (famOf M n1)
LamRec M 0 (suc n) ctr = rec ctr
LamRec M (suc n) 0 ctr = rec ctr
LamRec M 0 0 tt (var .zero i ctr) = rec (not<0 i ctr)
LamRec M 0 0 tt (lam .zero body) = lamOf M 0 (LamRec M 1 1 tt body )
LamRec M 0 0 tt (appl .zero t1 t2) = applOf M 0 (LamRec M 0 0 tt t1) (LamRec M 0 0 tt t2)
LamRec M (suc n0) (suc n1) prf (var .(suc n0) i small) = varOf M (suc n1) i (transport (λ j → (i my< suc (decodeℕ n0 n1 prf j)) ≡ true) small)
-- ( _∙_ (λ j → (i my< suc (decodeℕ n0 n1 prf (~ j)))) small)
LamRec M (suc n0) (suc n1) prf (lam .(suc n0) body) =
  -- why does this pass termination checker?
  let Mbody = LamRec M (suc (suc n0)) (suc (suc n1)) prf body in
  lamOf M (suc n1) Mbody
LamRec M (suc n0) (suc n1) prf (appl .(suc n0) t1 t2) =
  let Mt = LamRec M (suc n0) (suc n1) prf in
  applOf M (suc n1) (Mt t1) (Mt t2)

--registering the graph of the above recursor as a logical relation of models
grLamRecLrel : (M : ModLamPresNRG .nrg-cr) → ModLamPresNRG ⦅ LamAsMod , M ⦆
grLamRecLrel M =
  (tt , (λ n0 n1 nn t0 m1 → LamRec M _ _ nn t0 ≡ m1)) ,
  -- Semantic operations varOf M, lamOf M, applOf M preserve the property of being in the image of the recursor (1ary param reading)
  -- Alternatively: they preserve the graph of LamRec (written right above)
  varCompat , lamCompat , {!!}
  where
    -- if vm is in the
    varCompat : varDNRG ⦅  varOf LamAsMod ,  varOf M ⦆# (tt , (λ n0 n1 nn t0 m1 → LamRec M n0 n1 nn t0 ≡ m1))
    varCompat 0 (suc n) ctr = rec ctr
    varCompat (suc n) 0 ctr = rec ctr
    varCompat _ _ _ 0 (suc n) ctr = rec ctr
    varCompat _ _ _ (suc n) 0 ctr = rec ctr
    varCompat 0 0 tt (suc m0) (suc m1) mm ctr = rec (false≢true ctr)
    varCompat 0 0 tt 0 0 tt ctr = rec (false≢true ctr)
    varCompat (suc n0) (suc n1) nn 0 0 tt _ _ _ =
      cong (varOf M (suc n1) 0) (isSetBool true true _ _)
    varCompat (suc n0) (suc n1) nn (suc m0) (suc m1) mm small0 small1 _ =
      --need: `my<` is displayed bridge-discrete over ℕ (twice ie bidisplayed)
      {!(transp (λ i → (m0 my< decodeℕ n0 n1 nn i) ≡ true) i0 small0)!}

    -- if mbody is in the image of the recursor, then so is lamOf M _ mbody
    lamCompat : lamDNRG ⦅  lamOf LamAsMod ,  lamOf M ⦆# (tt , (λ n0 n1 nn t0 m1 → LamRec M n0 n1 nn t0 ≡ m1))
    lamCompat 0 (suc n) ctr = rec ctr
    lamCompat (suc n) 0 ctr = rec ctr
    lamCompat 0 0 tt body0 mbody1 bodyy = cong (lamOf M 0) bodyy
    lamCompat (suc n0) (suc n1) nn body0 mbody1 bodyy = cong (lamOf M (suc n1)) bodyy

    smth : Unit
    smth = {!varCompat!}
    

