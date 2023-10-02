{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-} -- --allow-unsolved-metas

module Bridgy.Experimental.ChurchCircle where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.EquGraph
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.MyPathToEquiv
open import Bridgy.Core.CubicalLemmas
-- open import Bridgy.Core.GelExamples
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.Param
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit



-- want: ∀ (X⋆ : Type⋆) . Ω X⋆ → X     ≃     S1
-- where x is the point carried by X anx where Ω X⋆ = x≡x is the loop space functor.
-- hence we must build
-- 0) the Type⋆ NRG
-- 1) X⋆ : Type⋆ ⊨ fgPt (X⋆) dNRG
-- 2) X⋆ : Type⋆ ⊨ Ω X⋆ dNRG



-- 0) the NRG of pointed types.
Type⋆NRG : ∀ (l : Level) → NRGraph (ℓ-suc l)
Type⋆NRG l = (TypeNRG l) # (X⊨ElX)

-- 1) the forget-pt displayed NRG
fgPt : ∀ {l} → DispNRG l (Type⋆NRG l)
fgPt = X,stuff⊨ElX (X⊨ElX) 


-- 2) the loop space displayed NRG. X:Type , x:X ⊨ x ≡ x


------------------------------------------------------------------------
-- the Path dNRG.
-- X:Type, x:X, y:X ⊨ x≡y dNRG

X,x,y-NRG : ∀ (l : Level) → NRGraph (ℓ-suc l)
X,x,y-NRG l = _#_
  (Type⋆NRG l)
  (X,stuff⊨ElX (X⊨ElX))

-- X:Type, x:X, y:X ⊨ x ≡ y dNRG
PathdNRG : ∀ {l} → DispNRG l (X,x,y-NRG l)
PathdNRG .dcr ((X , x) , y) = x ≡ y
PathdNRG .dedge ((X0 , x0) , y0) ((X1 , x1) , y1) ((XX , xx) , yy) p0 p1 =
  PathP (λ i → XX (p0 i) (p1 i)) xx yy
PathdNRG .dnativ ((X0 , x0) , y0) ((X1 , x1) , y1) ((XX , xx) , yy) Xxy-bdg Xxy-prf p0 p1 =
  flip compEquiv (PathPvsBridgeP (λ x i → Xxy-bdg x .fst .fst) {a00 = x0} {a10 = x1} {a01 = y0} {a11 = y1})
  (mypathToEquiv
    (PathP≡PathP (λ i → XX (p0 i) (p1 i)) (λ i → BridgeP (λ x → Xxy-bdg x .fst .fst) (p0 i) (p1 i))
    ((λ i → funExt⁻ (funExt⁻ (outEquGrInv Xxy-prf-fst-fst) (p0 i)) (p1 i))) -- XX x0 x1 ≡ BridgeP (λ x → Xxy-bdg x .fst .fst) x0 x1
      (symP (toPathP (sym (outEquGrInv (Xxy-prf-fst-snd)) )))
    (symP ((toPathP (sym (outEquGrInv (Xxy-prf-snd))))))))

  where

    Xxy-prf-fst : (XX , xx) [ Type⋆NRG _ .nativ (X0 , x0) (X1 , x1) ] (λ z → Xxy-bdg z .fst)
    Xxy-prf-fst = nativ-#-proj1 (Type⋆NRG _) (X,stuff⊨ElX (X⊨ElX)) (X0 , x0) (X1 , x1) (XX , xx) (λ z → Xxy-bdg z .fst) y0 y1 yy (λ z → Xxy-bdg z .snd) Xxy-prf

    Xxy-prf-fst-fst : XX [ TypeNRG _ .nativ X0 X1 ] (λ z → Xxy-bdg z .fst .fst)
    Xxy-prf-fst-fst = nativ-#-proj1 (TypeNRG _) (X⊨ElX) X0 X1 XX (λ z → Xxy-bdg z .fst .fst) x0 x1 xx (λ z → Xxy-bdg z .fst .snd) Xxy-prf-fst

    -- Xxy-prf-fst-snd ~: xx [ X⊨ElX .dnativ ..] (λ z → Xxy-bdg z .fst .snd)
    Xxy-prf-fst-snd = nativ-#-proj2 (TypeNRG _) (X⊨ElX) X0 X1 XX (λ z → Xxy-bdg z .fst .fst) x0 x1 xx (λ z → Xxy-bdg z .fst .snd) Xxy-prf-fst

    -- Xxy-prf-snd ~: yy [ dnativ ...] (λ z → Xxy-bdg z .snd)
    Xxy-prf-snd = nativ-#-proj2 (Type⋆NRG _) (X,stuff⊨ElX (X⊨ElX)) (X0 , x0) (X1 , x1) (XX , xx) (λ z → Xxy-bdg z .fst) y0 y1 yy (λ z → Xxy-bdg z .snd) Xxy-prf



    


-- X : Type, x:X ⊨ x ≡ x dNRG
-- ΩdNRG
    





-- smth : Unit
-- smth = {!Type⋆NRG ℓ-zero!}






-- open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Unit renaming (Unit to ⊤)
-- open import Cubical.Data.Sigma
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.Function
-- open import Cubical.HITs.S1

-- open import Bridgy.BridgePrims
-- open import Bridgy.BridgeExamples
-- open import Bridgy.ExtentExamples
-- open import Bridgy.GelExamples
-- open import Bridgy.NRGRelRecord
-- open import Bridgy.Param


-- -- in this file we prove a Church encoding for the circle
-- -- Namely:    ∀ (X⋆ : Type⋆) . Ω X⋆ → X     ≃     S1
-- -- say ≤ means "retract"
-- -- S1 ≤ ∀ (X⋆ : Type⋆) . Ω X⋆ → X essentially by computation.
-- -- ∀ (X⋆ : Type⋆) . Ω X⋆ → X  ≤   S1 by parametricity.
-- -- the proof is hence similar to eg ∀ X . X → X → X     ≃     Bool
-- -- (both are instances of yoneda)


-- -- pointed types
-- Type⋆ : ∀ (ℓ : Level) → Type (ℓ-suc ℓ)
-- Type⋆ ℓ = Σ[ X ∈ Type ℓ ] X

-- Type⋆₀ : Type₁
-- Type⋆₀ = Type⋆ ℓ-zero

-- -- Type⋆ with pointed relations is a native reflexive graph.
-- Type⋆NRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
-- Type⋆NRG ℓ  =
--   record {
--     nrg-cr = Type⋆ ℓ ;
--     nedge = λ A0⋆ A1⋆ → Σ (A0⋆ .fst → A1⋆ .fst → Type ℓ) (λ R → R (A0⋆ .snd) (A1⋆ .snd)) ;
--     nativ = λ A0⋆ A1⋆ → flip compEquiv ΣvsBridgeP
--       (Σ-cong-equiv relativity λ R → invEquiv (pathToEquiv (funExt⁻ (funExt⁻ (rel-retract R) _) _)))
--     }

-- -- the forgetful native relator Type⋆ → Type
-- forgPt : ∀ {ℓ} → NRelator (Type⋆NRG ℓ) (TypeNRG ℓ)
-- forgPt = record {
--   nobjMap = λ X⋆  → X⋆ .fst ;
--   nedgeMap =  λ R⋆  → R⋆ .fst ;
--   nativ-rel = λ A0⋆ A1⋆ → refl
--   }



-- -- the loop-space native relator Ω : Type⋆ → Type
-- -- bug: normalization does not seem to terminate!
-- -- + we need more computational rules to conclude (wip)
-- Ω : ∀ {ℓ} → NRelator (Type⋆NRG ℓ) (TypeNRG ℓ)
-- Ω = record {
--   nobjMap = λ X⋆ → X⋆ .snd ≡ X⋆ .snd ;
--   nedgeMap = λ {g0 = A0⋆} {g1 = A1⋆} R⋆ →
--     λ loop0 loop1 →  PathP (λ i → R⋆ .fst (loop0 i) (loop1 i)) (R⋆ .snd) (R⋆ .snd) ;
--   nativ-rel =
--     λ A0⋆ A1⋆ → funExt λ q → funExt λ l0 → funExt λ l1 →
--     ua (isoToEquiv (iso
--       (λ pth → {!λ x i → pth i x!}) {!!} {!!} {!!}))
--   }
-- -- Ω = record { nobjMap = λ { (X , pt) → pt ≡ pt }
-- --            ; nedgeMap = λ { (R , ptd) → λ loop0 loop1 →  PathP (λ i → R (loop0 i) (loop1 i)) ptd ptd  }
-- --            -- ; nativ-rel = λ where (X0 , x0) (X1 , x1) → funExt λ q → funExt λ l0 → funExt λ l1 → {!!} }
-- --            ; nativ-rel = λ where (X0 , x0) (X1 , x1) → funExt λ q → funExt λ l0 → funExt λ l1 →
-- --                                    ua (isoToEquiv (iso
-- --                                      (λ pth → {!λ x i → pth i x!}) -- λ x i → pth i x
-- --                                      (λ bdg → {!λ i x → bdg x i!}) {!!} {!!})) } -- λ i x → bdg x i


-- -- -- below a trick to avoid weird instance resolution freezes. we define S¹NRelator
-- -- -- directly as an eta expansion
-- -- S¹NRelator : NRelator (Type⋆₀) Type
-- -- S¹NRelator = let ofc = compNRelator ⟨ Ω , forgPt ⟩nrel arrowNRelator
-- --              in
-- --                record { nobjMap =  ofc . nobjMap ; nedgeMap =  ofc .nedgeMap ; nativ-rel =  ofc .nativ-rel }

-- -- churchS¹ :  ( ∀ (X⋆ : Type⋆₀) → Ω .nobjMap X⋆ → forgPt .nobjMap X⋆ )   ≃    S¹
-- -- churchS¹ = isoToEquiv (iso
-- --              (λ c → c (S¹ , base) loop)
-- --              (λ { base → λ { ( X , x ) → λ _ → x } ; (loop j) → λ { (X , x) → λ p → p j } })
-- --              (λ { base → refl ; (loop j) → refl })
-- --              λ c → funExt λ where (A , a) → funExt λ h →
-- --                                    {! !})
-- --   where
-- --   edgeChoice : ∀ {A : Type} {a : A} {h : a ≡ a} →  Σ (S¹ → A → Type) (λ R → R base a)
-- --   edgeChoice {A} {a} {h}  = (λ { base → λ x → a ≡ x ; (loop j) → λ x → h j ≡ x }) , refl

-- --   -- smth = (param S¹NRelator c (S¹ , base) (A , a) edgeChoice loop h refl)


-- -- X* ⊧ X dnrg
-- fg : ∀ {ℓ} → DispNRG ℓ (Type⋆NRG ℓ)
-- fg {ℓ} .dcr (X , x) = X
-- fg {ℓ} .dedge (X0 , x0) (X1 , x1) (XX , xx) = XX
-- fg {ℓ} .dnativ (X0 , x0) (X1 , x1) Xbdg a0 a1 = idEquiv _

-- -- X* ⊧ x : X
-- pt : ∀ {ℓ} → SectNRG (Type⋆NRG ℓ) fg
-- pt .ac0 (X , x) = x
-- pt .ac1 (X0 , x0) (X1 , x1) (XX , xx) = xx
-- pt .tm-nativ (X0 , x0) (X1 , x1) Xbdg = {!refl!}

-- -- X* ⊧ x ≡ x dnrg?
-- omg : ∀ {ℓ} → DispNRG ℓ (Type⋆NRG ℓ)
-- omg {ℓ} = {!PathForm (Type⋆NRG ℓ) fg!}
