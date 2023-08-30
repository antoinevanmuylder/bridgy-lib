{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.Judgments where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Unit

-- SEMANTIC CONTEXTS.
-- A native reflexive graph is a type equipped with a relation equivalent to its Bridge relation.
record NRGraph ℓ : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    nrg-cr : Type ℓ
    nedge :  nrg-cr → nrg-cr → Type ℓ
    nativ : ∀ (a b : nrg-cr) → nedge a b ≃ BridgeP (λ _ → nrg-cr) a b

  reflNedge : ∀ (a : nrg-cr) → nedge a a
  reflNedge a = invEq (nativ a a) (λ _ → a)

open NRGraph public

_⦅_,_⦆ : ∀ {ℓ} (G : NRGraph ℓ) → G .nrg-cr → G .nrg-cr → Type ℓ
_⦅_,_⦆ {ℓ} G g0 g1 = G .nedge g0 g1


-- relatedness under equivalences
module EquGraph {l : Level} {A0 A1 : Type l} where

  abstract

    _[_]_ : A0 → A0 ≃ A1 → A1 → Type l
    _[_]_ a0 e a1 = (equivFun e a0) ≡ a1

    -- e a0 ≡ a1 → a0 [e] a1
    inEquGr : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) → 
      (equivFun e a0) ≡ a1 → (a0 [ e ] a1)
    inEquGr a0 e a1 prf = prf

    -- a0 [e] a1 → a0 ≡ e^-1 a1
    outEquGrInv : (a0 : A0) → (e : A0 ≃ A1) → (a1 : A1) →
      (a0 [ e ] a1) → a0 ≡ invEq e a1
    outEquGrInv a0 e a1 aprf = invEq (equivAdjointEquiv e) aprf

open EquGraph public
    


-- SEMANTIC SUBSTITUTIONS.
-- A native relator is a morphism of native reflexive graphs.
-- It asks for this square between nativeness of G and H:

{-
                         G nativ
              G{g0,g1}  ---- ≃ -----  BridgeP (_.G) g0 g1
                 |                         |
     F .nrel1    |                         | λ q x. F(q x)
                 ∨                         ∨
              H{Fg0, Fg1} --- ≃ ----  BridgeP (_.H) (F g0) (F g1)
                           Hnativ
-}

-- TODO: ℓ's implicit? endpoints implicit in nedgeMap? implicit fields? nativ-rel irrelevant?
-- isProp nativ-rel? (maybe necessary for a propositional η rule)
module NativeRelator {ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) where

  record NRelator : Type (ℓ-max ℓG ℓH) where
    no-eta-equality
    field
      nrel0 : G .nrg-cr  → H .nrg-cr --action on 0cells in G
      nrel1 : (g0 g1 : G .nrg-cr) → G .nedge g0 g1 → H .nedge (nrel0 g0) (nrel0 g1) --action on 1cells in G
      nativ-rel : (g0 g1 : G .nrg-cr) (gg : G ⦅ g0 , g1 ⦆ ) (gbdg : BridgeP (λ _ → G .nrg-cr) g0 g1) →
        gg [ G .nativ g0 g1 ] gbdg →
        (nrel1 g0 g1 gg) [ H .nativ (nrel0 g0) (nrel0 g1) ] (λ x → nrel0 (gbdg x))

  open NRelator public

open NativeRelator public


-- SEMANTIC (DEPENDENT) TYPES
-- a Γ-displayed NRG (or NRG displayed over Γ) is basically a NRG whose every operation is indexed using the operations of Gamma
record DispNRG {ℓ} (ℓ' : Level) (Γ : NRGraph ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  no-eta-equality
  field
    -- displayed carriers
    dcr : Γ .nrg-cr → Type ℓ'
    -- displayed edges
    dedge : ∀ (g0 g1 : Γ .nrg-cr) (gg : Γ ⦅ g0 , g1 ⦆ ) (a0 : dcr g0) (a1 : dcr g1) → Type ℓ'
    -- displayed nativeness
    dnativ : (g0 g1 : Γ .nrg-cr) →
      (gg : Γ ⦅ g0 , g1 ⦆ ) (gbdg : Bridge (Γ .nrg-cr) g0 g1) → gg [ Γ .nativ g0 g1 ] gbdg →
      (a0 : dcr g0) (a1 : dcr g1) →
      dedge g0 g1 gg a0 a1 ≃ BridgeP (λ x → dcr (gbdg x)) a0 a1

open DispNRG public

_⦅_,_⦆#_ : ∀ {ℓ ℓ' : Level} {Γ} (A : DispNRG {ℓ = ℓ} ℓ' Γ) {γ0 γ1 : Γ .nrg-cr} (a0 : A .dcr γ0) (a1 : A .dcr γ1) (γγ : Γ ⦅ γ0 , γ1 ⦆) → Type ℓ'
_⦅_,_⦆#_ {ℓ} {ℓ'} {Γ} A {γ0} {γ1} a0 a1 γγ = A .dedge γ0 γ1 γγ a0 a1



-- SEMANTIC (OPEN) TERMS
record TermDNRG {ℓ} {ℓA} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) : Type (ℓ-max ℓ ℓA) where
  no-eta-equality
  field
    -- action on Γ's 0-cells
    tm0 : ∀ (g : Γ .nrg-cr) → A .dcr g
    -- action on Γ's 1-cells
    tm1 : ∀ (g0 g1 : Γ .nrg-cr) (gg : Γ ⦅ g0 , g1 ⦆) → A ⦅ tm0 g0 , tm0 g1 ⦆# gg
    tm-nativ : ∀ (g0 g1 : Γ .nrg-cr)
      (gg : Γ ⦅ g0 , g1 ⦆ ) (gbdg : Bridge (Γ .nrg-cr) g0 g1) → (gprf : gg [ Γ .nativ g0 g1 ] gbdg) →
      tm1 g0 g1 gg [ A .dnativ g0 g1 gg gbdg gprf (tm0 g0) (tm0 g1) ] (λ x → tm0 (gbdg x))

open TermDNRG public

















-- JUNK

  -- -- nativ-rel stated as ∀ r : G{g0,g1}, ... instead
  -- switchNativeRelSqu : ∀ (F : NRelator) →
  --   ∀ (g0 g1 : G .nrg-cr) → bdg-action (F .nobjMap) ∘ (G .nativ g0 g1 .fst) ≡ H .nativ (F .nobjMap g0) (F .nobjMap g1) .fst ∘ F .nedgeMap
  -- switchNativeRelSqu F g0 g1 = switchEquivSqu (G .nativ g0 g1) (H .nativ (F .nobjMap g0) (F .nobjMap g1)) (F .nedgeMap) (bdg-action (F .nobjMap))
  --                              (F .nativ-rel g0 g1)

  -- pNativRel : ∀ (F : NRelator) →
  --   ∀ (g0 g1 : G .nrg-cr) (q : BridgeP (λ _ → G .nrg-cr) g0 g1) →
  --             (F .nedgeMap ((invEq (G .nativ g0 g1) q))) ≡ invEq (H .nativ (F .nobjMap g0) (F .nobjMap g1)) λ x → F .nobjMap (q x)
  -- pNativRel F g0 g1 q = cong (λ blank → blank q) (F .nativ-rel g0 g1)

  -- nedgeMap≡ByNativ : (g0 g1 : G .nrg-cr) (F : NRelator) →
  --   F .nedgeMap ≡ (invEq (H. nativ (F .nobjMap g0) (F .nobjMap g1) )) ∘ (bdg-action (F .nobjMap)) ∘ (G. nativ g0 g1 .fst)
  -- nedgeMap≡ByNativ g0 g1 F = 
  --   sym ( equivAdjointEquiv (preCompEquiv (G. nativ g0 g1))
  --          {a =  (invEq (H .nativ (F .nobjMap g0) (F .nobjMap g1)) ∘ bdg-action (F .nobjMap))}
  --          {b = F .nedgeMap} .fst (sym ( F .nativ-rel g0 g1)) )
  --   ∙ ∘-assoc (invEq (H. nativ (F .nobjMap g0) (F .nobjMap g1))) (bdg-action (F .nobjMap)) (G. nativ g0 g1 .fst)


    -- displayed nativeness ("forall bridge" version)
    -- we choose this version to be able to formulate tm-natv as ∀ bridge as well.
    -- dnativ : ∀ (γ0 γ1 : Γ .nrg-cr) (γbdg : BridgeP (λ _ → Γ .nrg-cr) γ0 γ1) (a0 : dcr γ0) (a1 : dcr γ1) →
    --                dedge γ0 γ1 (invEq (Γ .nativ γ0 γ1) γbdg) a0 a1 ≃ BridgeP (λ x → dcr (γbdg x)) a0 a1

      -- (γbdg : BridgeP (λ _ → Γ .nrg-cr) γ0 γ1) →
      --            ac1 γ0 γ1 (invEq (Γ .nativ γ0 γ1) γbdg) ≡ invEq (A .dnativ γ0 γ1 γbdg (ac0 γ0) (ac0 γ1)) (λ x → ac0 (γbdg x) )
