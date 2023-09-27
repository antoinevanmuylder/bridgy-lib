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
open import Cubical.Data.Sigma
open import Bridgy.MyPathToEquiv

open import Bridgy.NRGRelRecord

-- if G ≅ H as rgraphs, and hasNativ(H), then hasNativ(G)
-- we just need to prove the sip for rgraphs

-- lessons learned...
-- while proving SIP (for Bridge commutation it's basically the same recipe) for a record type R,
-- ie observational equality ≃ equality: (r0 [R≅] r1) ≃ Path R r0 r1) where R≅ : R → R → Type is the type of isos
-- it's good to
-- 0. if some fields depend on a field B, prove a simpl commutation pcpl for B (SIP or bdg comm.)
-- 0bis. for fields of R that are dependent on say B, prove their dependent SIP
--    equivalently, formulate those dependent types as displayed native groupoids (resp. dNRGs in the case of bridges)
-- 1. rephrase (r0 [R≅] r1) as a sigma type (R≅EquivR≅-asΣ : R≅ r0 r1 ≃ R≅-asΣ r0 r1)
-- 2. have a Σ type preOeq of preobservational equalities. ie record values that have path fields.
--      proving this should then be routine
--      preEquiv: preOeq r0 r1  ≃ Path R r0 r1
-- 3. by 1 and 2 the goal is now R≅-asΣ r0 r1 ≃ preOeq r0 r1, an equiv of sigma types.
-- 4. We can now use commutation withΣ,  Σ-cong-equiv : ... → Σ S T ≡ Σ S' T'
-- 5. S≃S' goes by 0
-- 6. ...⊢ T≃T' goes by 0bis.
--
-- Overall this technique avoids having inlined proofs of dependent commutation principles,
-- And it does not commit fully to "writing the type in the syntax of displayed native groupoids/native reflexive graphs."
-- The latter DSL is interesting theoretically but gives types and terms with questionable definitional behaviour.
-- Moreover writing in this DSL can be cumbersome inferencewise (it's often the case for DTT in DTT)

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
  --an easier version (less parametric formulation) is provided at the end of the module
  record RGraph≅ : Type l where
    field
      rg-cr≅ : G .rg-cr ≃ H .rg-cr
      redge≅ : ∀ (g0 : G .rg-cr) (h0 : H .rg-cr) (gh0 : equivFun rg-cr≅ g0 ≡ h0) →
               ∀ (g1 : G .rg-cr) (h1 : H .rg-cr) (gh1 : equivFun rg-cr≅ g1 ≡ h1) →
               G .redge g0 g1 ≃ H .redge h0 h1
  open RGraph≅ public

  RGraph≅-asΣ : Type l
  RGraph≅-asΣ =
    Σ (G .rg-cr ≃ H .rg-cr) (λ rgcr≅ →
      ∀ (g0 : G .rg-cr) (h0 : H .rg-cr) (gh0 : equivFun rgcr≅ g0 ≡ h0) →
      ∀ (g1 : G .rg-cr) (h1 : H .rg-cr) (gh1 : equivFun rgcr≅ g1 ≡ h1) →
      G .redge g0 g1 ≃ H .redge h0 h1)
  
  RGraph≅EquivRGraph≅-asΣ : RGraph≅ ≃ RGraph≅-asΣ
  RGraph≅EquivRGraph≅-asΣ = isoToEquiv (iso
    (λ obseq → (obseq .rg-cr≅ ) , (obseq .redge≅))
    (λ apr → record { rg-cr≅ = apr .fst ; redge≅ = apr .snd })
    (λ _ → refl)
    λ _ → refl)

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

  pre-RGraph≅-asΣ : Type (ℓ-suc l)
  pre-RGraph≅-asΣ = Σ (G .rg-cr ≡ H .rg-cr) (λ rgcr≡ → PathP (λ i → rgcr≡ i → rgcr≡ i → Type l) (G .redge) (H .redge))

  pre-RGraph≅Equivpre-RGraph≅-asΣ : pre-RGraph≅ ≃ pre-RGraph≅-asΣ
  pre-RGraph≅Equivpre-RGraph≅-asΣ = isoToEquiv (iso
    (λ rv → (rv .rg-cr≡) , rv .redgePath)
    (λ apr → record { rg-cr≡ = apr .fst ; redgePath = apr .snd })
    (λ _ → refl)
    λ _ → refl)

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
    (compEquiv RGraph≅EquivRGraph≅-asΣ
    (flip compEquiv (invEquiv pre-RGraph≅Equivpre-RGraph≅-asΣ)
    (Σ-cong-equiv (invEquiv univalence) λ GH →
    redgeSipP (G .rg-cr) (H .rg-cr) GH
      (equivFun (invEquiv univalence) GH) refl
      (G .redge) (H .redge))))

  record RGraph≅' : Type l where
    field
      rg-cr≅' : G .rg-cr ≃ H .rg-cr
      redge≅' : ∀ x0 x1 → G .redge x0 x1 ≃ H .redge (rg-cr≅' .fst x0) (rg-cr≅' .fst x1)
  open RGraph≅'

  -- RGraph≅'EquivRGraph≅ : RGraph≅' ≃ RGraph≅
  -- RGraph≅'EquivRGraph≅ = isoToEquiv (iso
  --   (λ iso' → record {
  --     rg-cr≅ = iso' .rg-cr≅' ;
  --     redge≅ = λ g0 h0 gh0 g1 h1 gh1 →
  --       compEquiv (iso' .redge≅' g0 g1)
  --       (mypathToEquiv λ j → H .redge (gh0 j) (gh1 j))  })
  --   (λ iso → record {
  --     rg-cr≅' = iso .rg-cr≅ ;
  --     redge≅' = λ x0 x1 → iso .redge≅ x0 _ refl x1 _ refl })
  --   (λ iso →
  --     λ i → record { rg-cr≅ = iso .rg-cr≅ ;
  --       redge≅ = λ g0 h0 gh0 g1 h1 gh1 → {!
  --                  secEq (compEquiv
  --                  (iso .redge≅ g0 (equivFun (rg-cr≅ iso) g0)
  --                  (λ _ → equivFun (rg-cr≅ iso) g0) g1 (equivFun (rg-cr≅ iso) g1)
  --                  (λ _ → equivFun (rg-cr≅ iso) g1))
  --                  (mypathToEquiv (λ j → H .redge (gh0 j) (gh1 j)))) !} })
  --   {!!})

      -- redge≅' : ∀ (g0 : G .rg-cr) (h0 : H .rg-cr) (gh0 : equivFun rg-cr≅ g0 ≡ h0) →
      --          ∀ (g1 : G .rg-cr) (h1 : H .rg-cr) (gh1 : equivFun rg-cr≅ g1 ≡ h1) →
      --          G .redge g0 g1 ≃ H .redge h0 h1
  open RGraph≅' public

open ObsEqRGraph public

-- we can now transport nativeness proofs along RGraph isomorphisms

hasNativ : ∀ {l} (G : RGraph l) → Type l
hasNativ G = ∀ g0 g1 → G .redge g0 g1 ≃ BridgeP (λ _ → G .rg-cr) g0 g1

transpNativ : ∀ {l} (G H : RGraph l) (gh : RGraph≅ G H) → (hasNativ G ≡ hasNativ H)
transpNativ G H gh =
  λ i → hasNativ (equivFun (RGraph-SIP _ _) gh i)
