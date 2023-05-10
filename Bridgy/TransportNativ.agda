{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce   #-}

open import Bridgy.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Data.Unit
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit
open import Bridgy.MyPathToEquiv

-- if G ≅ H as rgraphs, and hasNativ(H), then hasNativ(G)
-- we just need to prove the sip for rgraphs
module Bridgy.TransportNativ where


-- no nativeness, compared to NRGraph's (native reflexive graphs)
record RGraph ℓ : Type (ℓ-suc ℓ) where
  -- constructor mkNRG
  field
    rg-cr : Type ℓ
    redge :  rg-cr → rg-cr → Type ℓ
    -- nativ : ∀ (a b : rg-cr) → nedge a b ≃ BridgeP (λ _ → rg-cr) a b
open RGraph public

-- dependent SIP for this type
-- G : Type l ⊢ G → G → Type l
-- (would be part of this displayed "native groupoid":)
--   G : Type l ⊧ G → G → Type l dNGPD
--
-- a dependent SIP at a line of types, characterizes the PathP along the line.
redgeSipP : ∀ {l : Level} (G0 G1 : Type l) (GG : G0 ≃ G1) (Gpth : G0 ≡ G1)
              (iso-pth : ua GG ≡ Gpth)
              (rdg0 : G0 → G0 → Type l) (rdg1 : G1 → G1 → Type l) →
              (∀ (g0 : G0) (g1 : G1) (hgg : equivFun GG g0 ≡ g1)
                 (l0 : G0) (l1 : G1) (hll : equivFun GG l0 ≡ l1) →
                 rdg0 g0 l0 ≃ rdg1 g1 l1)
              ≃
              PathP (λ i → Gpth i → Gpth i → Type l) rdg0 rdg1
redgeSipP G0 G1 GG Gpth hypG rdg0 rdg1 =
  flip compEquiv funExtDepEquiv
  (flip compEquiv (invEquiv (implicit≃Explicit))
  (equivΠCod λ g0 →
  flip compEquiv (invEquiv (implicit≃Explicit))
  (equivΠCod λ g1 → equivΠ'
    (flip compEquiv (invEquiv (PathP≃Path _ _ _))
    (compPathlEquiv
    (_∙_ (λ i → transport (λ j → hypG (~ i) j) g0 )
    (transportRefl _))))
  λ {gg gbdg} hypg →
  flip compEquiv funExtDepEquiv
  (flip compEquiv (invEquiv (implicit≃Explicit)) (equivΠCod λ l0 →
  flip compEquiv (invEquiv (implicit≃Explicit)) (equivΠCod λ l1 →
  equivΠ'
    (flip compEquiv (invEquiv (PathP≃Path _ _ _))
    (compPathlEquiv
    (_∙_ (λ i → transport (λ j → hypG (~ i) j) l0 )
    (transportRefl _))))
  λ {ll lpth} hypl →
  invEquiv univalence))))))




-- SIP in RGraph: what's a path of Rgraph's?

module ObsEqRGraph {l : Level} (G H : RGraph l) where

  --observational equality at RGraph
  record RGraph≅ : Type l where
    field
      rg-cr≅ : G .rg-cr ≃ H .rg-cr
      redge≅ : ∀ (g0 : G .rg-cr) (h0 : H .rg-cr) (gh0 : equivFun rg-cr≅ g0 ≡ h0) →
               ∀ (g1 : G .rg-cr) (h1 : H .rg-cr) (gh1 : equivFun rg-cr≅ g1 ≡ h1) →
               G .redge g0 g1 ≃ H .redge h0 h1
  open RGraph≅ public


  --preobservational equality at RGraph
  record pre-RGraph≅ : Type (ℓ-suc l) where
    field
      rg-cr≡ : G .rg-cr ≡ H .rg-cr
      redgePath : PathP (λ i → rg-cr≡ i → rg-cr≡ i → Type l) (G .redge) (H .redge)
  open pre-RGraph≅ public

  -- when are 2 such values equal?
  pre-RGraph≅≡ : (poeq0 poeq1 : pre-RGraph≅)
    (rg-cr≡p : (poeq0 .rg-cr≡) ≡ (poeq1 .rg-cr≡))
    (redgePathp : PathP (λ k → PathP (λ i → rg-cr≡p k i → rg-cr≡p k i → Type l) (G .redge) (H .redge)) (poeq0 .redgePath) (poeq1 .redgePath)) →
    poeq0 ≡ poeq1
  pre-RGraph≅≡ poeq0 poeq1 rg-cr≡p redgePathp = λ i → record {
    rg-cr≡ = rg-cr≡p i ;
    redgePath = redgePathp i }

  preObsEqIsPath : pre-RGraph≅ ≃ (G ≡ H)
  preObsEqIsPath = isoToEquiv (iso
    (λ recOf≡ → λ i → record {
      rg-cr = recOf≡ .rg-cr≡ i  ;
      redge = recOf≡ .redgePath i })
    (λ GH → record {
      rg-cr≡ = λ i → GH i .rg-cr ;
      redgePath = λ i → GH i .redge })
    (λ _ → refl)
    λ _ → refl)

  RGraph-SIP : RGraph≅ ≃ (G ≡ H)
  RGraph-SIP = flip compEquiv preObsEqIsPath
    (isoToEquiv (iso
    (λ obseq → record {
      rg-cr≡ = ua (obseq .rg-cr≅) ;
      redgePath =
        funExtDep λ {g0 h0} gh0 →
        funExtDep λ {g1 h1} gh1 →
        ua (obseq .redge≅ g0 h0 (sym (transportRefl _) ∙ fromPathP gh0) g1 h1 (sym (transportRefl _) ∙ fromPathP gh1))  })
    (λ poeq → record {
      rg-cr≅ = mypathToEquiv (poeq .rg-cr≡ ) ;
      redge≅ = λ g0 h0 gh0 g1 h1 gh1 → mypathToEquiv
        (invEq funExtDepEquiv (invEq funExtDepEquiv (poeq .redgePath) {g0} {h0}
          (toPathP gh0)) {g1} {h1}
        (toPathP gh1)) } )
    (λ poeq → pre-RGraph≅≡ _ _
      (ua-mypathToEquiv (poeq .rg-cr≡))
      (toPathP (flip _∙_ (secEq funExtDepEquiv (poeq .redgePath))
      (flip _∙_ (secEq funExtDepEquiv _)
      {!funExtDepEquiv .fst
      (invEq funExtDepEquiv
       (funExtDepEquiv .fst (invEq funExtDepEquiv (poeq .redgePath))))!} ))))
    {!!}))
-- {PathP {ℓ-suc l}
--        (λ i → (x : rg-cr≡ poeq i) → rg-cr≡ poeq i → Type l) (G .redge)
--        (H .redge)}

      -- (symP (toPathP {!transport
      -- (λ i →
      --    PathP
      --    (λ i₁ →
      --       ua-mypathToEquiv (poeq .rg-cr≡) (~ i) i₁ →
      --       ua-mypathToEquiv (poeq .rg-cr≡) (~ i) i₁ → Type l)
      --    (G .redge) (H .redge))
      -- (redgePath poeq)!}) )


-- ( sym (equivFun (equivAdjointEquiv funExtDepEquiv) {!!}))

-- ∀ (g0 : G .rg-cr) (h0 : H .rg-cr) (gh0 : equivFun rg-cr≅ g0 ≡ h0) →
--              ∀ (g1 : G .rg-cr) (h1 : H .rg-cr) (gh1 : equivFun rg-cr≅ g1 ≡ h1) →
--              G .redge g0 g1 ≃ H .redge h0 h1
