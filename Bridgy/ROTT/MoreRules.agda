{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.MoreRules where


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.CubicalLemmas
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Bridgy.Core.BDisc
open import Bridgy.Core.List
open import Bridgy.Core.Nat
open import Bridgy.Core.Bool
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.List hiding ( [_] )
open import Cubical.Data.Nat
open import Cubical.Data.Bool

-- temp file for writing rules


-- Γ ⊨ a : A
-- -----------
-- Γ → Γ . A
tmToSub : ∀ {lΓ lA} {Γ : NRGraph lΓ} (A : DispNRG lA Γ) →
  TermDNRG Γ A → NRelator Γ (Γ # A)
tmToSub {lΓ} {lA} {Γ} A a = record {
  nrel0 = λ g → (g , a .tm0 g) ;
  nrel1 = λ g0 g1 gg → (gg , a .tm1 g0 g1 gg) ;
  nativ-rel = λ g0 g1 gg gbdg gprf →
    nativ-#-split Γ A g0 g1 gg gbdg gprf _ _ (a .tm1 g0 g1 gg) (λ x → a .tm0 (gbdg x))
    (a .tm-nativ g0 g1 gg gbdg gprf)
  }



-- dependent app
-- Γ, x:A ⊨ B
-- Γ ⊨ f : Π A B    Γ ⊨ a : A
-- ----------------------------
-- Γ ⊨ dapp(f,a) : B[a/x]
dapp : ∀ {lΓ lA lB} {Γ : NRGraph lΓ} (A : DispNRG lA Γ) (B : DispNRG lB (Γ # A)) →
  (f : TermDNRG Γ (ΠForm A B)) (a : TermDNRG Γ A) →
  TermDNRG Γ (tySubst Γ (Γ # A) (tmToSub _ a) B)
dapp A B f a = record {
  tm0 = λ g → f .tm0 g (a .tm0 g) ;
  tm1 = λ g0 g1 gg → f .tm1  _ _ gg _ _ (a .tm1 _ _ gg) ;
  tm-nativ = λ g0 g1 gg gbdg gprf →
    let thingf = outEquGrInv (f .tm-nativ g0 g1 gg gbdg gprf) in
    let thingf2 = funExt⁻ {f = f .tm1 g0 g1 gg} thingf (a .tm0 g0) in
    let thingf3 = funExt⁻ {f = tm1 f g0 g1 gg (a .tm0 g0)} thingf2 (a .tm0 g1) in
    let thingf4 = funExt⁻ {f = tm1 f g0 g1 gg (a .tm0 g0) (a .tm0 g1)} thingf3 (a .tm1 g0 g1 gg) in
    let replace-a1 = invEq (A .dnativ g0 g1 gg gbdg gprf (tm0 a g0) (tm0 a g1)) (λ x → tm0 a (gbdg x)) in
    let thingf4bis = funExt⁻ {f = tm1 f g0 g1 gg (a .tm0 g0) (a .tm0 g1)} thingf3 replace-a1 in
    {!ΠForm A B .dnativ g0 g1 gg gbdg gprf (tm0 f g0) (tm0 f g1)!}
    -- outEquGr (f .tm-nativ g0 g1 gg gbdg gprf)
    --inEquGr λ i x → {!!}
  }



