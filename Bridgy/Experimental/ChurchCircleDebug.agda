{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  -v tc.prim.mhcomp:40 #-} -- -v tc.prim.hcomp:30 -- -v tc.prim.mhcomp:40

module Bridgy.Experimental.ChurchCircleDebug where


open import Bridgy.Core.GelExamples
open import Cubical.Data.Unit
open import Cubical.Foundations.Univalence


open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.CubicalLemmas
open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Bridgy.Experimental.ChurchCircle

-- (X:Type, x:X) →  X:Type, x:X, y:X
preDiag : ∀ {l} →  PreNRelator (Type⋆NRG l) (X,x,y-NRG l)
preDiag .prenrel0 (X , x) = (X , x) , x
preDiag .prenrel1 (X0 , x0) (X1 , x1) (XX , xx) = ( XX , xx ) , xx

diag : ∀ {l} →  NRelator (Type⋆NRG l) (X,x,y-NRG l)
diag {l} .nrel0 (X , x) = preDiag .prenrel0 (X , x)
diag {l} .nrel1 (X0 , x0) (X1 , x1) (XX , xx) = preDiag .prenrel1 (X0 , x0) (X1 , x1) (XX , xx)
diag {l} .nativ-rel = {!!} 

Have
  _[_]_ {ℓ-suc l}
  {Σ {ℓ-suc l} {l}
   (Σ {ℓ-suc l} {l} (X0 → X1 → Type l)
    (λ v → _⦅_,_⦆#_ (X⊨ElX {l}) {X0} {X1} x0 x1 v))
   (_⦅_,_⦆#_ (X,stuff⊨ElX {l} {l} (X⊨ElX {l})) {X0 , x0} {X1 , x1} x0
    x1)}
  {BridgeP {ℓ-max (ℓ-suc l) l}
   (λ _ →
      nrg-cr
      (_#_ {ℓ-suc l} {l} (Type⋆NRG l) (X,stuff⊨ElX {l} {l} (X⊨ElX {l}))))
   ((X0 , x0) , x0) ((X1 , x1) , x1)}
  ((XX , xx) , xx) (sameEquivs i1) (λ x → Xxbdg x , Xxbdg x .snd)


Goal: _[_]_ {ℓ-suc l}
      {X,x,y-NRG l .nedge ((X0 , x0) , x0) ((X1 , x1) , x1)}
      {BridgeP {ℓ-suc l} (λ _ → nrg-cr (X,x,y-NRG l)) ((X0 , x0) , x0)
       ((X1 , x1) , x1)}
      ((XX , xx) , xx)
      (X,x,y-NRG l .nativ ((X0 , x0) , x0) ((X1 , x1) , x1))
      (λ x → (fst (Xxbdg x) , snd (Xxbdg x)) , snd (Xxbdg x))



  where

    -- thing = X,x,y-NRG _ .nativ ((X0 , x0) , x0) ((X1 , x1) , x1)

    hlp0 : 
      xx [ X,stuff⊨ElX X⊨ElX .dnativ (X0 , x0) (X1 , x1) (XX , xx) Xxbdg Xxprf x0 x1 ] (λ z → Xxbdg z .snd) →
      ((XX , xx) , xx) [ (Type⋆NRG l # X,stuff⊨ElX X⊨ElX) .nativ ((X0 , x0) , x0) ((X1 , x1) , x1) ] (λ x → Xxbdg x , Xxbdg x .snd)
    hlp0 = nativ-#-split (Type⋆NRG l) (X,stuff⊨ElX (X⊨ElX)) (X0 , x0) (X1 , x1) (XX , xx)
      Xxbdg Xxprf x0 x1 xx (λ z → Xxbdg z .snd)

    hlp1 = nativ-#-proj1 (TypeNRG l) X⊨ElX X0 X1 XX (λ z → Xxbdg z .fst) x0 x1 xx (λ z → Xxbdg z .snd) Xxprf

    hlp2 : xx [ X,stuff⊨ElX X⊨ElX .dnativ (X0 , x0) (X1 , x1) (XX , xx) Xxbdg Xxprf x0 x1 ] (λ z → Xxbdg z .snd)
    hlp2 = nativ-#-proj2 (TypeNRG l) X⊨ElX X0 X1 XX (λ z → Xxbdg z .fst) x0 x1 xx (λ z → Xxbdg z .snd) Xxprf


    -- ≡ at
    -- Σ (Type⋆NRG l ⦅ X0 , x0 , X1 , x1 ⦆)
    -- (_⦅_,_⦆#_ (X,stuff⊨ElX X⊨ElX) x0 x1)
    -- ≃
    -- BridgeP (λ _ → Σ (Type⋆NRG l .nrg-cr) (X,stuff⊨ElX X⊨ElX .dcr))
    -- ((X0 , x0) , x0) ((X1 , x1) , x1)
    sameEquivs :
      (Type⋆NRG l # X,stuff⊨ElX X⊨ElX) .nativ ((X0 , x0) , x0) ((X1 , x1) , x1)
      ≡
      X,x,y-NRG l .nativ ((X0 , x0) , x0) ((X1 , x1) , x1)
    sameEquivs = equivEq refl
      

    -- sameEquivs :
    --   X,stuff⊨ElX X⊨ElX .dnativ (X0 , x0) (X1 , x1) (XX , xx) Xxbdg Xxprf x0 x1
    --   ≡ 
    --   X⊨ElX .dnativ X0 X1 XX (λ z → Xxbdg z .fst)
    --   (nativ-#-proj1 (TypeNRG _) X⊨ElX X0 X1 XX (λ z → Xxbdg z .fst) x0
    --    x1 xx (λ z → Xxbdg z .snd) Xxprf)
    --   x0 x1
    -- sameEquivs =
    --   equivEq refl

    -- hlp2' = (transport (λ i → xx [ sameEquivs (~ i) ] (λ z → Xxbdg z .snd)) hlp2)
