{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module Bridgy.NativeReflGraphRelator where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma using (_×_ ; ≃-× ; ≡-× ; Σ-cong-equiv ; Σ-cong-equiv-snd)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

-- cubical lemmas
module _ where
  
  equivInj : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (I : A ≃ B) →
    (a a' : A) → I .fst a ≡ I .fst a' → a ≡ a'
  equivInj I a a' prf = sym (retEq I a) ∙ cong (invEq I) prf ∙ (retEq I a')


  switchEquivSqu : ∀ {ℓ ℓ'} {Aleft Aright : Type ℓ} {Bleft Bright : Type ℓ'}
    (Aequiv : Aleft ≃ Aright) (Bequiv : Bleft ≃ Bright) (fleft : Aleft → Bleft) (fright : Aright → Bright) → 
    fleft ∘ (invEq Aequiv) ≡ (invEq Bequiv) ∘ fright → fright ∘ (Aequiv .fst) ≡ (Bequiv .fst) ∘ fleft
  switchEquivSqu Aequiv Bequiv fleft fright hyp =
    sym (equivInj (preCompEquiv (invEquiv Aequiv)) ((Bequiv .fst) ∘ fleft) (fright ∘ (Aequiv .fst))
        (funExt λ a →
        equivFun (equivAdjointEquiv Bequiv)
        (λ i → hyp i a) ∙
        cong fright (sym (secEq Aequiv a))))

  -- {-
  --             ulur
  --         UL ----> UR
  --         |        |
  --   uldl  ∨        ∨ urdr
  --         DL ----> DR
  --            dldr

  -- some  ulur reordering...
  -- if uldl ∘ ulur⁻¹ ≡ dldr⁻¹ ∘ urdr (cf nativ-rel) then
  --    uldl ≡ dldr⁻¹ ∘ urdr ∘ ulur
  -- -}
  -- cmp2compEquiv→1equivVs3Equiv : ∀ {ℓ ℓ'} {UL : Type ℓ} {UR : Type ℓ} {DL : Type ℓ'} {DR : Type ℓ'}
  --   (uldl : UL ≃ DL)  (urdr : UR ≃ DR) (dldr : DL ≃ DR) (ulur : UL ≃ UR) →
  --     compEquiv (invEquiv ulur) (uldl) ≡ compEquiv urdr (invEquiv dldr)
  --     →
  --     uldl ≡ compEquiv (compEquiv ulur urdr) (invEquiv dldr)
  -- cmp2compEquiv→1equivVs3Equiv uldl urdr dldr ulur =

  funExt2⁻ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → A → I → Type ℓ'}
    {f : (x y : A) → B x y i0} {g : (x y : A) → B x y i1} →
    (x y : A) →
    PathP (λ i → (x y : A) → B x y i) f g →
    PathP (B x y) (f x y) (g x y)
  funExt2⁻ x y eq = λ i → eq i x y
  
-- functions F have a canonical action on bridges
bdg-action : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} {x0 x1 : X} →
             (F : X → Y) → BridgeP (λ _ → X) x0 x1 → BridgeP (λ _ → Y) (F x0) (F x1)
bdg-action F q = λ x → F (q x)


-- when possible we use instance arguments to infer native rgraph "implementation"
-- todo: isProp nativ ?
module NativeReflexiveGraph where

  -- typeclass for native reflexive graphs. we can omit refl edges.
  record HasNRGraph {ℓ} (A : Type ℓ) : Type (ℓ-suc ℓ) where
    field
      nedge : A → A → Type ℓ
      nativ : ∀ (a b : A) → nedge a b ≃ BridgeP (λ _ → A) a b
  open HasNRGraph ⦃...⦄ public

  -- smart packed class version
  record NRGraph ℓ : Type (ℓ-suc ℓ) where
    constructor mkNRGraph
    field
      nrg-carrier : Type ℓ
      ⦃ has-nativergraph ⦄ : HasNRGraph nrg-carrier
open NativeReflexiveGraph public


-- TODO: ℓ's implicit? endpoints implicit in nedgeMap? implicit fields? nativ-rel irrelevant?
-- isProp nativ-rel? (maybe necessary for a propositional η rule)
-- NRelator is just a record - no typeclasses are used

{-
                         G nativ
              G{g0,g1}  ---------->  BridgeP (_.G) g0 g1
                 |                         |
     F nedgeMap  |                         | λ q x. F(q x)
                 ∨                         ∨
              H{Fg0, Fg1} -------->  BridgeP (_.H) (F g0) (F g1)
                           Hnativ
-}
module NativeRelator {ℓG ℓH} (G : Type ℓG) (H : Type ℓH) ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ where

  record NRelator : Type (ℓ-max ℓG ℓH) where
    field
      nobjMap : G → H
      nedgeMap : ∀ {g0 g1 : G} → nedge g0 g1 → nedge (nobjMap g0) (nobjMap g1)
      -- nativeness square. Up to funext, equality says ∀ q : Bdg, bla
      nativ-rel : ∀ (g0 g1 : G) → nedgeMap ∘ invEq (nativ g0 g1) ≡ invEq (nativ (nobjMap g0) (nobjMap g1)) ∘ (bdg-action nobjMap)
  open NRelator public

  -- nativ-rel stated as ∀ r : G{g0,g1}, ... instead
  switchNativeRelSqu : ∀ (F : NRelator) →
    ∀ (g0 g1 : G) → bdg-action (F .nobjMap) ∘ (nativ g0 g1 .fst) ≡ nativ (F .nobjMap g0) (F .nobjMap g1) .fst ∘ F .nedgeMap
  switchNativeRelSqu F g0 g1 = switchEquivSqu (nativ g0 g1) (nativ (F .nobjMap g0) (F .nobjMap g1)) (F .nedgeMap) (bdg-action (F .nobjMap))
                               (F .nativ-rel g0 g1)

  pNativRel : ∀ (F : NRelator) →
    ∀ (g0 g1 : G) (q : BridgeP (λ _ → G) g0 g1) →
              (F .nedgeMap ((invEq (nativ g0 g1) q))) ≡ invEq (nativ (F .nobjMap g0) (F .nobjMap g1)) λ x → F .nobjMap (q x)
  pNativRel F g0 g1 q = cong (λ blank → blank q) (F .nativ-rel g0 g1)

  -- preCompEquiv (nativ g0 g1) : (BridgeP (λ _ → G) g0 g1 → H{} ) ≃ (G{} → H{})
  nedgeMap≡ByNativ : (g0 g1 : G) (F : NRelator) →
    F .nedgeMap ≡ (invEq (nativ (F .nobjMap g0) (F .nobjMap g1) )) ∘ (bdg-action (F .nobjMap)) ∘ (nativ g0 g1 .fst)
  nedgeMap≡ByNativ g0 g1 F = 
    sym ( equivAdjointEquiv (preCompEquiv (nativ g0 g1))
           {a =  (invEq (HasNRGraph.nativ hnrgH (F .nobjMap g0) (F .nobjMap g1)) ∘ bdg-action (F .nobjMap))}
           {b = F .nedgeMap} .fst (sym ( F .nativ-rel g0 g1)) )
    ∙ ∘-assoc (invEq (nativ (F .nobjMap g0) (F .nobjMap g1))) (bdg-action (F .nobjMap)) (nativ g0 g1 .fst) -- ? (bdg-action (F .nobjMap)) ?
    -- (equivAdjointEquiv (preCompEquiv {C = nedge (F .nobjMap g0) (F .nobjMap g1)} (nativ g0 g1)) {b = F .nedgeMap} .fst)

       -- (invEq
       -- (HasNRGraph.nativ hnrgH (F .nobjMap g0) (F .nobjMap g1))
       -- ∘ bdg-action (F .nobjMap))

open NativeRelator public

NRelator' : ∀ {ℓG ℓH} (G : NRGraph ℓG) (H : Type ℓH) ⦃ hnrgH : HasNRGraph H ⦄ → Type (ℓ-max ℓG ℓH)
NRelator' (mkNRGraph G) H = NRelator G H



-- {-
--   Next we provide elementary native reflexive graphs and explain how to combine them

--   the forward and *backward* maps of `nativ` for a native reflexive
--   graph G should be as simple as possible.
--   This way, proofs that F : G → _ or F : _ → G is native relator become simpler
-- -}


topBdgDiscrLemma : (q : BridgeP (λ _ → ⊤) tt tt) → (λ _ → tt) ≡ q
topBdgDiscrLemma q = λ i x → isContrUnit .snd (q x) i

topBdgDiscrEquiv : ⊤ ≃ BridgeP (λ _ → ⊤) tt tt
topBdgDiscrEquiv  = isoToEquiv (iso
                      (λ _ _ → tt)
                      (λ _ → tt)
                      (λ q → topBdgDiscrLemma q)
                      λ where tt → refl)

instance
  topHasNRG : HasNRGraph ⊤
  topHasNRG = record { nedge = λ _ _ → ⊤
                     ; nativ = λ where tt tt → topBdgDiscrEquiv}


-- Type with -logical- relations is a native reflexive graph
-- this is proved using relativity
instance
  TypeHasNRG : ∀ {ℓ} → HasNRGraph (Type ℓ)
  TypeHasNRG = record { nedge = λ A B → (A → B → Type _)
                      ; nativ = λ A B → relativity }


-- nRG has binary products
instance
  prodHasNRG : ∀ {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ →
    HasNRGraph (G × H)
  prodHasNRG = record
    { nedge = λ where (g0 , h0) (g1 , h1) → (nedge g0 g1) × (nedge h0 h1)
    ; nativ = λ where (g0 , h0) (g1 , h1) → compEquiv (≃-× (nativ g0 g1) (nativ h0 h1)) ×vsBridgeP }

-- nRG has exponentials. H^G = NRelator G H.
module Exponentials {ℓG ℓH} {G : Type ℓG} {H : Type ℓH} ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ where

  -- record NRelator-logrel {ℓ} (E F : NRelator G H)  : Type _ where
  --   field
  --     objrel : G → H → Type ℓ
  --     edgerel : ∀ (g g' : G) (h h' : H) (gh : objrel g h) (gh' : objrel g' h') → edge g g' → edge h h' → Type ℓ

  -- instance
  --   nrelHasNRGraph : HasNRGraph (NRelator G H)
  --   nrelHasNRGraph = record
  --     { nedge = {!!} ; nativ = {!!} }

-- the identity native relator
idNRelator : ∀ {ℓ} {G : Type ℓ} ⦃ hnrgG : HasNRGraph G ⦄ → NRelator G G
idNRelator = record
  { nobjMap = λ g → g
  ; nedgeMap = λ e → e
  ; nativ-rel = λ g0 g1 → refl }

-- universal pty of product in NRGraph (1 direction, the "useful" one)
⟨_,_⟩nrel :  ∀ {ℓG ℓH ℓK} {G : Type ℓG} {H : Type ℓH} {K : Type ℓK}
            ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ ⦃ hnrgK : HasNRGraph K ⦄ →
            NRelator G H → NRelator G K → NRelator G (H × K)
⟨_,_⟩nrel E F = record
  { nobjMap = λ g → (E .nobjMap g , F .nobjMap g)
  ; nedgeMap = λ e → ( E .nedgeMap e , F .nedgeMap e)
  ; nativ-rel = λ g0 g1 → funExt λ q → ≡-× (pNativRel _ _ E g0 g1 q) (pNativRel _ _ F g0 g1 q)  }


-- the arrow native relator
arrowNRelator : ∀ {ℓ} → NRelator (Type ℓ × Type ℓ) (Type ℓ)
arrowNRelator = record
  { nobjMap = λ where (X , Y) → (X → Y)
  ; nedgeMap = λ where (XX , YY) f0 f1 → ∀ x0 x1 → XX x0 x1 → YY (f0 x0) (f1 x1)
  ; nativ-rel = λ where
      (X0 , Y0) (X1 , Y1) → funExt λ q → funExt λ f0 → funExt λ f1 →
        ua (flip compEquiv ΠvsBridgeP
        (equivΠCod λ x0 →
        equivΠCod λ x1 →
        equivΠCod λ xx →
        idEquiv _))  }

-- the diagonal native relator  Type → Type×Type
diagNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ × Type ℓ)
diagNRelator = record
  { nobjMap = λ X → (X , X)
  ; nedgeMap = λ XX → (XX , XX)
  ; nativ-rel = λ X0 X1 → refl }


-- native relators do compose
compNRelator : ∀ {ℓG ℓH ℓK} {G : Type ℓG} {H : Type ℓH} {K : Type ℓK}
               ⦃ hnrgG : HasNRGraph G ⦄ ⦃ hnrgH : HasNRGraph H ⦄ ⦃ hnrgK : HasNRGraph K ⦄
               (E : NRelator G H) (F : NRelator H K) → NRelator G K
compNRelator E F = record
  { nobjMap = F .nobjMap  ∘ E .nobjMap
  ; nedgeMap = λ g01 → F .nedgeMap (E .nedgeMap g01)
  -- diagram chasing!
  ; nativ-rel = λ g0 g1 → ∘-assoc (F .nedgeMap) (E .nedgeMap) (invEq (nativ g0 g1)) ∙
                          cong (λ blank → F .nedgeMap ∘ blank) (E .nativ-rel g0 g1) ∙
                          sym (∘-assoc (F .nedgeMap) (invEq (nativ (E .nobjMap g0) (E .nobjMap g1))) (bdg-action (E .nobjMap))) ∙
                          cong (λ blank → blank ∘ (bdg-action (E .nobjMap))) (F .nativ-rel (E .nobjMap g0) (E .nobjMap g1) ) ∙
                          funExt λ q →  refl}
  
-- example: X ↦ X → X relator
churchUnitNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ)
churchUnitNRelator = compNRelator diagNRelator arrowNRelator

-- example: X ↦ X → X → X relator
churchBoolNRelator : ∀ {ℓ} → NRelator (Type ℓ) (Type ℓ)
churchBoolNRelator = compNRelator ( ⟨ idNRelator , churchUnitNRelator ⟩nrel ) arrowNRelator

-- sigmas?
module Sigmas0 {ℓ ℓ'} {G : Type ℓ} ⦃ hnrgG : HasNRGraph G ⦄ (F : NRelator G (Type ℓ')) where

  instance
    ΣHasNRG : HasNRGraph (Σ G (F .nobjMap))
    ΣHasNRG = record { nedge = λ gg0 gg1 → 
                         Σ (nedge (gg0 .fst) (gg1 .fst)) (λ e → F .nedgeMap e (gg0 .snd) (gg1 .snd))
                      ; nativ = λ gg0 gg1 → 
                          flip compEquiv ΣvsBridgeP (Σ-cong-equiv
                            (nativ (gg0 .fst) (gg1 .fst))
                            λ e →   pathToEquiv (flip funExt⁻ (gg1 .snd) (flip funExt⁻ (gg0 .snd) (funExt⁻ (nedgeMap≡ByNativ G (Type ℓ') (gg0 .fst) (gg1 .fst) F) e)))  ) }  
open Sigmas0 public
 

-- conjecture (kind of proven on paper for hProp):
-- for any level n, nType is a native reflexive graph by taking "nType relations" as edges
--    ∀ A0 A1 → (A0 → A1 → nType) ≃ BridgeP (λ _ → nType) A0 A1
-- For instance a bridge between two hProps is a proof irrelvant relation:)
module HSet (ℓ : Level) where

  -- We begin by proving the conjecture for hContr

  hContr : Type (ℓ-suc ℓ)
  hContr = TypeOfHLevel ℓ 0

  -- instance
  --   hContrHasNRG : HasNRGraph hContr
  --   hContrHasNRG = {!!}

                   -- flip compEquiv ΣvsBridgeP
                   -- (flip compEquiv (Σ-cong-equiv relativity
                   --   λ R → flip compEquiv ΣvsBridgeP (flip compEquiv (Σ-cong-equiv (pathToEquiv (λ i → retEq relativity R (~ i) (prf0 .fst) (prf1 .fst)))
                   --   λ rprf → {!ΠvsBridgeP!}) {!!}))
                   --   {!!})

                   -- flip compEquiv ΣvsBridgeP
                   -- (flip compEquiv (Σ-cong-equiv-snd  (λ q → ΣvsBridgeP))
                   -- (flip compEquiv (Σ-cong-equiv-snd {A = (BridgeP (λ x → Type ℓ) A0 A1)}
                   --    {B = {!Σ-cong-equiv-snd!}}
                   --    λ q →  flip compEquiv (Σ-cong-equiv-snd {A = (BridgeP (λ x → q x) (fst prf0) (fst prf1))}
                   --    {B = {!!}} λ q → ΠvsBridgeP ) {!!})
                   --    {!!}))


{- 
need rewriting badly
?0 : l ≡ r0
    α0 : R0 r1 ≡ r0
?0 := ?1 ∙ α0
    α1 : R1 r2 ≡ r1
?1 := ?2 ∙ R0 α1
    α2 : R2 r3 ≡ r2
?2 := ?3 ∙ R0 R1 α2
    α3 : R3 r4 ≡ r3
?3 := ?4 ∙ R0 R1 R2 α3

...

?0      
?1 ∙ α0           
(?2 ∙ R0 α1) ∙ α0
((?3 ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
(((?4 ∙ R0 R1 R2 α3) ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
((((?5 ∙ R0 R1 R2 R3 α4) ∙ R0 R1 R2 α3) ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
-}
