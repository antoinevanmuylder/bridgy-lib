{-
  a record version of NRGraph, instead of instance version
-}

{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module Bridgy.NRGRelRecord where

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
open import Cubical.Foundations.Path using (congPathEquiv)

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


record NRGraph ℓ : Type (ℓ-suc ℓ) where
  -- constructor mkNRG
  field
    nrg-cr : Type ℓ
    nedge :  nrg-cr → nrg-cr → Type ℓ
    nativ : ∀ (a b : nrg-cr) → nedge a b ≃ BridgeP (λ _ → nrg-cr) a b

  reflNedge : ∀ (a : nrg-cr) → nedge a a
  reflNedge a = invEq (nativ a a) (λ _ → a)
open NRGraph public

_⦅_,_⦆ : ∀ {ℓ} (G : NRGraph ℓ) → G .nrg-cr → G .nrg-cr → Type ℓ
_⦅_,_⦆ {ℓ} G g0 g1 = G .nedge g0 g1



-- -- TODO: ℓ's implicit? endpoints implicit in nedgeMap? implicit fields? nativ-rel irrelevant?
-- -- isProp nativ-rel? (maybe necessary for a propositional η rule)
-- -- NRelator is just a record - no typeclasses are used

-- {-
--                          G nativ
--               G{g0,g1}  ---------->  BridgeP (_.G) g0 g1
--                  |                         |
--      F nedgeMap  |                         | λ q x. F(q x)
--                  ∨                         ∨
--               H{Fg0, Fg1} -------->  BridgeP (_.H) (F g0) (F g1)
--                            Hnativ
-- -}
module NativeRelator {ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) where

  record NRelator : Type (ℓ-max ℓG ℓH) where
    field
      nobjMap : G .nrg-cr  → H .nrg-cr
      nedgeMap : ∀ {g0 g1 : G .nrg-cr} → G .nedge g0 g1 → H .nedge (nobjMap g0) (nobjMap g1)
      -- nativeness square. Up to funext, equality says ∀ q : Bdg, bla
      nativ-rel : ∀ (g0 g1 : G .nrg-cr) → nedgeMap ∘ invEq (G .nativ g0 g1) ≡ invEq (H .nativ (nobjMap g0) (nobjMap g1)) ∘ (bdg-action nobjMap)
  open NRelator public

  -- nativ-rel stated as ∀ r : G{g0,g1}, ... instead
  switchNativeRelSqu : ∀ (F : NRelator) →
    ∀ (g0 g1 : G .nrg-cr) → bdg-action (F .nobjMap) ∘ (G .nativ g0 g1 .fst) ≡ H .nativ (F .nobjMap g0) (F .nobjMap g1) .fst ∘ F .nedgeMap
  switchNativeRelSqu F g0 g1 = switchEquivSqu (G .nativ g0 g1) (H .nativ (F .nobjMap g0) (F .nobjMap g1)) (F .nedgeMap) (bdg-action (F .nobjMap))
                               (F .nativ-rel g0 g1)

  pNativRel : ∀ (F : NRelator) →
    ∀ (g0 g1 : G .nrg-cr) (q : BridgeP (λ _ → G .nrg-cr) g0 g1) →
              (F .nedgeMap ((invEq (G .nativ g0 g1) q))) ≡ invEq (H .nativ (F .nobjMap g0) (F .nobjMap g1)) λ x → F .nobjMap (q x)
  pNativRel F g0 g1 q = cong (λ blank → blank q) (F .nativ-rel g0 g1)

  nedgeMap≡ByNativ : (g0 g1 : G .nrg-cr) (F : NRelator) →
    F .nedgeMap ≡ (invEq (H. nativ (F .nobjMap g0) (F .nobjMap g1) )) ∘ (bdg-action (F .nobjMap)) ∘ (G. nativ g0 g1 .fst)
  nedgeMap≡ByNativ g0 g1 F = 
    sym ( equivAdjointEquiv (preCompEquiv (G. nativ g0 g1))
           {a =  (invEq (H .nativ (F .nobjMap g0) (F .nobjMap g1)) ∘ bdg-action (F .nobjMap))}
           {b = F .nedgeMap} .fst (sym ( F .nativ-rel g0 g1)) )
    ∙ ∘-assoc (invEq (H. nativ (F .nobjMap g0) (F .nobjMap g1))) (bdg-action (F .nobjMap)) (G. nativ g0 g1 .fst)

open NativeRelator public


{-
  Next we provide elementary native reflexive graphs and explain how to combine them

  the forward and *backward* maps of `nativ` for a native reflexive
  graph G should be as simple as possible.
  This way, proofs that F : G → _ or F : _ → G is native relator become simpler
-}


topBdgDiscrLemma : (q : BridgeP (λ _ → ⊤) tt tt) → (λ _ → tt) ≡ q
topBdgDiscrLemma q = λ i x → isContrUnit .snd (q x) i

topBdgDiscrEquiv : ⊤ ≃ BridgeP (λ _ → ⊤) tt tt
topBdgDiscrEquiv  = isoToEquiv (iso
                      (λ _ _ → tt)
                      (λ _ → tt)
                      (λ q → topBdgDiscrLemma q)
                      λ where tt → refl)

topNRG : NRGraph ℓ-zero
topNRG .nrg-cr = ⊤
topNRG .nedge  = (λ _ _ → ⊤)
topNRG .nativ  = (λ where tt tt → topBdgDiscrEquiv)


-- -- Type with -logical- relations is a native reflexive graph
-- -- this is proved using relativity
TypeNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
TypeNRG ℓ .nrg-cr = Type ℓ
TypeNRG ℓ .nedge  = λ A0 A1 → (A0 → A1 → Type ℓ)
TypeNRG ℓ .nativ  = λ A0 A1 → relativity



-- -- nRG has binary products
_×NRG_ : ∀{ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) → NRGraph (ℓ-max ℓG ℓH)
_×NRG_ G H = record
               { nrg-cr = (G .nrg-cr × H .nrg-cr)
               ; nedge  = (λ where (g0 , h0) (g1 , h1) → G .nedge g0 g1 × H .nedge h0 h1 )
               ; nativ  = (λ where (g0 , h0) (g1 , h1) → flip compEquiv ×vsBridgeP
                                     (≃-× (G .nativ g0 g1) (H .nativ h0 h1)))
               }

-- the identity native relator
idNRelator : ∀ {ℓ} {G : NRGraph ℓ} → NRelator G G
idNRelator = record
  { nobjMap = λ g → g
  ; nedgeMap = λ e → e
  ; nativ-rel = λ g0 g1 → refl }

-- universal pty of product in NRGraph (1 direction, the "useful" one)
⟨_,_⟩nrel :  ∀ {ℓG ℓH ℓK} {G : NRGraph ℓG} {H : NRGraph ℓH} {K : NRGraph ℓK} →
            NRelator G H → NRelator G K → NRelator G (H ×NRG K)
⟨_,_⟩nrel E F = record
  { nobjMap = λ g → (E .nobjMap g , F .nobjMap g)
  ; nedgeMap = λ e → ( E .nedgeMap e , F .nedgeMap e)
  ; nativ-rel = λ g0 g1 → funExt λ q → ≡-× (pNativRel _ _ E g0 g1 q) (pNativRel _ _ F g0 g1 q)  }


-- the arrow native relator
arrowNRelator : ∀ {ℓ} → NRelator (TypeNRG ℓ ×NRG TypeNRG ℓ) (TypeNRG ℓ)
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
diagNRelator : ∀ {ℓ} → NRelator (TypeNRG ℓ) (TypeNRG ℓ ×NRG TypeNRG ℓ)
diagNRelator = record
  { nobjMap = λ X → (X , X)
  ; nedgeMap = λ XX → (XX , XX)
  ; nativ-rel = λ X0 X1 → refl }


-- native relators do compose
compNRelator : ∀ {ℓG ℓH ℓK} {G : NRGraph ℓG} {H : NRGraph ℓH} {K : NRGraph ℓK}
               (E : NRelator G H) (F : NRelator H K) → NRelator G K
compNRelator {G = G} {H = H} {K = K} E F = record
  { nobjMap = F .nobjMap  ∘ E .nobjMap
  ; nedgeMap = F .nedgeMap ∘ E .nedgeMap
  -- diagram chasing!
  ; nativ-rel = λ g0 g1 → ∘-assoc (F .nedgeMap) (E .nedgeMap) (invEq (G .nativ g0 g1)) ∙
                          cong (λ blank → F .nedgeMap ∘ blank) (E .nativ-rel g0 g1) ∙
                          sym (∘-assoc (F .nedgeMap) (invEq (H .nativ (E .nobjMap g0) (E .nobjMap g1))) (bdg-action (E .nobjMap))) ∙
                          cong (λ blank → blank ∘ (bdg-action (E .nobjMap))) (F .nativ-rel (E .nobjMap g0) (E .nobjMap g1) ) ∙
                          funExt λ q →  refl}
  
-- example: X ↦ X → X relator
churchUnitNRelator : ∀ {ℓ} → NRelator (TypeNRG ℓ) (TypeNRG ℓ)
churchUnitNRelator = compNRelator diagNRelator arrowNRelator

-- example: X ↦ X → X → X relator
churchBoolNRelator : ∀ {ℓ} → NRelator (TypeNRG ℓ) (TypeNRG ℓ)
churchBoolNRelator = compNRelator ( ⟨ idNRelator , churchUnitNRelator ⟩nrel ) arrowNRelator

-- sigmas?
module SigmaNRG {ℓ ℓ' : Level} where

  --should I use p.m. "λ where" when defining nedge/nativ?
  ΣNRG : (G : NRGraph ℓ) (F : NRelator G (TypeNRG ℓ')) → NRGraph (ℓ-max ℓ ℓ')
  ΣNRG G F = record
    { nrg-cr = Σ (G .nrg-cr) (F .nobjMap)
    ; nedge = λ gg0 gg1 → Σ (G .nedge (gg0 .fst) (gg1 .fst)) (λ e → F .nedgeMap e (gg0 .snd) (gg1 .snd)) 
    ; nativ = λ gg0 gg1 → flip compEquiv ΣvsBridgeP
        (Σ-cong-equiv (G .nativ (gg0 .fst) (gg1 .fst)) λ e →
        pathToEquiv (flip funExt⁻ (gg1 .snd) (flip funExt⁻ (gg0 .snd) (funExt⁻ (nedgeMap≡ByNativ G (TypeNRG ℓ') (gg0 .fst) (gg1 .fst) F) e))))
    }

open SigmaNRG public


-- Type*NRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
-- Type*NRG0 ℓ = ΣNRG (TypeNRG ℓ) (idNRelator)

module PiNRG {ℓ ℓ' : Level} where

  ΠNRG : (G : NRGraph ℓ) (F : NRelator G (TypeNRG ℓ')) → NRGraph (ℓ-max ℓ ℓ')
  ΠNRG G F = record
    { nrg-cr = (g : G .nrg-cr) → F .nobjMap g
    ; nedge = λ f0 f1 → (g0 g1 : G .nrg-cr) (e : G .nedge g0 g1) → F .nedgeMap e (f0 g0) (f1 g1)
    ; nativ = λ f0 f1 → flip compEquiv ΠvsBridgeP
        (equivΠCod λ g0 → equivΠCod λ g1 →
        equivΠ (G .nativ g0 g1) λ e →
        pathToEquiv (flip funExt⁻ (f1 g1) (flip funExt⁻ (f0 g0) (funExt⁻ (nedgeMap≡ByNativ G (TypeNRG ℓ') g0 g1 F) e)))) }

open PiNRG public

module PathpNRG {ℓ : Level} where

  PathPNRG : (A : I → NRGraph ℓ) (a0 : A i0 .nrg-cr) (a1 : A i1 .nrg-cr) → NRGraph ℓ
  PathPNRG A a0 a1 = record
    { nrg-cr = PathP (λ i → A i .nrg-cr) a0 a1
    -- todo: reflNedge is by def η⁻¹ (refl bridge). is this bad computationally?
    ; nedge = λ p0 p1 → PathP (λ i → A i .nedge (p0 i) (p1 i)) (reflNedge (A i0) _) (reflNedge (A i1) _)
    ; nativ = λ p0 p1 →
        flip compEquiv (PathPvsBridgeP (λ (@tick x : BI) i → A i .nrg-cr) {down = λ _ → a0} {up = λ _ → a1})
        (invEquiv (congPathEquiv (λ i → invEquiv (A i .nativ (p0 i) (p1 i))))) }

  -- c ⊢ λ c' → c ≡ c' native rel
  -- PathPRel

open PathpNRG public




-- -- conjecture (kind of proven on paper for hProp):
-- -- for any level n, nType is a native reflexive graph by taking "nType relations" as edges
-- --    ∀ A0 A1 → (A0 → A1 → nType) ≃ BridgeP (λ _ → nType) A0 A1
-- -- For instance a bridge between two hProps is a proof irrelvant relation:)
-- module HSet (ℓ : Level) where

--   -- We begin by proving the conjecture for hContr

--   hContr : Type (ℓ-suc ℓ)
--   hContr = TypeOfHLevel ℓ 0

--   instance
--     hContrHasNRG : HasNRGraph hContr
--     hContrHasNRG = {!!}

--                    -- flip compEquiv ΣvsBridgeP
--                    -- (flip compEquiv (Σ-cong-equiv relativity
--                    --   λ R → flip compEquiv ΣvsBridgeP (flip compEquiv (Σ-cong-equiv (pathToEquiv (λ i → retEq relativity R (~ i) (prf0 .fst) (prf1 .fst)))
--                    --   λ rprf → {!ΠvsBridgeP!}) {!!}))
--                    --   {!!})

--                    -- flip compEquiv ΣvsBridgeP
--                    -- (flip compEquiv (Σ-cong-equiv-snd  (λ q → ΣvsBridgeP))
--                    -- (flip compEquiv (Σ-cong-equiv-snd {A = (BridgeP (λ x → Type ℓ) A0 A1)}
--                    --    {B = {!Σ-cong-equiv-snd!}}
--                    --    λ q →  flip compEquiv (Σ-cong-equiv-snd {A = (BridgeP (λ x → q x) (fst prf0) (fst prf1))}
--                    --    {B = {!!}} λ q → ΠvsBridgeP ) {!!})
--                    --    {!!}))


-- {- 
-- need rewriting badly
-- ?0 : l ≡ r0
--     α0 : R0 r1 ≡ r0
-- ?0 := ?1 ∙ α0
--     α1 : R1 r2 ≡ r1
-- ?1 := ?2 ∙ R0 α1
--     α2 : R2 r3 ≡ r2
-- ?2 := ?3 ∙ R0 R1 α2
--     α3 : R3 r4 ≡ r3
-- ?3 := ?4 ∙ R0 R1 R2 α3

-- ...

-- ?0      
-- ?1 ∙ α0           
-- (?2 ∙ R0 α1) ∙ α0
-- ((?3 ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
-- (((?4 ∙ R0 R1 R2 α3) ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
-- ((((?5 ∙ R0 R1 R2 R3 α4) ∙ R0 R1 R2 α3) ∙ R0 R1 α2) ∙ R0 α1) ∙ α0
-- -}


-- record NRGraph ℓ : Type (ℓ-suc ℓ) where
--   -- constructor mkNRG
--   field
--     nrg-cr : Type ℓ
--     nedge :  nrg-cr → nrg-cr → Type ℓ
--     nativ : ∀ (a b : nrg-cr) → nedge a b ≃ BridgeP (λ _ → nrg-cr) a b

--   reflNedge : ∀ (a : nrg-cr) → nedge a a
--   reflNedge a = invEq (nativ a a) (λ _ → a)
-- open NRGraph public


{-

ATTEMPT: shallow CwF structure on NRG

-}


-- a Γ-displayed NRG is basically a NRG over Gamma (other side of some Grothendieck corr for NRG)
-- this would correspond to semantics of the @Ty@ operation of CwFs
record DispNRG {ℓ} (ℓ' : Level) (Γ : NRGraph ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    -- displayed carriers
    dcr : Γ .nrg-cr → Type ℓ'
    -- displayed edges
    dedge : ∀ (γ0 γ1 : Γ .nrg-cr) (e : Γ ⦅ γ0 , γ1 ⦆ ) (a0 : dcr γ0) (a1 : dcr γ1) → Type ℓ'
    -- displayed nativeness
    dnativ : ∀ (γ0 γ1 : Γ .nrg-cr) (e : Γ ⦅ γ0 , γ1 ⦆ ) (a0 : dcr γ0) (a1 : dcr γ1) →
                   dedge γ0 γ1 e a0 a1 ≃ BridgeP (λ x → dcr (Γ .nativ γ0 γ1 .fst e x)) a0 a1
open DispNRG public

_⦅_,_⦆#_ : ∀ {ℓ ℓ' : Level} {Γ} (A : DispNRG {ℓ = ℓ} ℓ' Γ) {γ0 γ1 : Γ .nrg-cr} (a0 : A .dcr γ0) (a1 : A .dcr γ1) (γγ : Γ ⦅ γ0 , γ1 ⦆) → Type ℓ'
_⦅_,_⦆#_ {ℓ} {ℓ'} {Γ} A {γ0} {γ1} a0 a1 γγ = A .dedge γ0 γ1 γγ a0 a1

-- semantical terms are sections of displayed NRGs
record SectNRG {ℓ} {ℓA} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) : Type (ℓ-max ℓ ℓA) where
  field
    -- action on Γ's 0-cells
    ac0 : ∀ (γ : Γ .nrg-cr) → A .dcr γ
    -- action on Γ's 1-cells
    ac1 : ∀ {γ0 γ1 : Γ .nrg-cr} (γγ : Γ ⦅ γ0 , γ1 ⦆) → A ⦅ ac0 γ0 , ac0 γ1 ⦆# γγ
    -- nativeness (must be stated dependently, and pointwise)
    -- this is the forward formulation.
    -- easier as displayed nativeness for types is edge dependent
    -- but mismatch with common nativeness formulation for relators...
    tm-nativ : ∀ (γ0 γ1 : Γ .nrg-cr) (γγ : Γ ⦅ γ0 , γ1 ⦆ ) →
                   PathP (λ _ → BridgeP (λ x → A .dcr (equivFun( Γ .nativ γ0 γ1  ) γγ x)) (ac0 γ0) (ac0 γ1))
                     (λ x → ac0 ((equivFun (Γ .nativ γ0 γ1) γγ) x) ) --use ac0
                     (equivFun (A .dnativ γ0 γ1 γγ (ac0 γ0) (ac0 γ1)) (ac1 γγ))


-- one side of the NRG Grothendieck correspondance.
-- makePsh : ∀ (ℓ : Level) (E B : NRGraph ℓ) (F : NRelator E B) → DispNRG B
-- makePsh ℓ E B F =
--   record {
--     dcr = fiber (F .nobjMap) ;
--     dedge = λ b0 b1 bb e0 e1 → fiber (F .nedgeMap {g0 = e0 .fst} {g1 = e1 .fst}) {!!}   ;
--     dnativ = {!!} }
    

-- Ctx extension, ~the other side of the NRG Grothendieck correspondance.
module CtxExtension {ℓ ℓ'} where

  -- Γ ctx
  -- Γ ⊢ A type
  -- ----------
  -- Γ.A ctx
  _#_ : ∀ (Γ : NRGraph ℓ) (A : DispNRG ℓ' Γ) → NRGraph (ℓ-max ℓ ℓ')
  _#_ Γ A =
    record {
      nrg-cr = Σ (Γ .nrg-cr) (A .dcr) ;
      nedge = λ γa0 γa1 → Σ (Γ .nedge (γa0 .fst) (γa1 .fst)) (λ γγ → A .dedge (γa0 .fst) (γa1 .fst) γγ (γa0 .snd) (γa1 .snd)) ;
      -- nedge = λ { ( γ0 , a0 ) (γ1 , a1 ) → Σ (Γ .nedge (γ0) (γ1)) (λ γγ → A .dedge γ0 γ1 γγ a0 a1) } ;
      nativ = λ γa0 γa1 → flip compEquiv ΣvsBridgeP
                 (Σ-cong-equiv (Γ .nativ (γa0 .fst) (γa1 .fst)) λ γγ → A .dnativ (γa0 .fst) (γa1 .fst) γγ (γa0 .snd) (γa1 .snd)) }
  infixl 40 _#_


open CtxExtension public

module AuxRules {ℓ} (Γ : NRGraph ℓ) where


  -- not really the var rule though
  -- var-rule : ∀ {ℓA} (A : DispNRG ℓA Γ) → DispNRG ℓA (Γ # A)
  -- var-rule A =
  --   record {
  --     dcr = λ { (γ , _) → A .dcr γ } ;
  --     dedge = λ { (γ0 , _) (γ1 , _) (γγ , _) → A .dedge γ0 γ1 γγ  }  ;
  --     dnativ = λ { (γ0 , _) (γ1 , _) (γγ , _) → A .dnativ γ0 γ1 γγ}  }

  -- Γ ⊢ A type
  -- Γ ⊢ B type
  -- ----------
  -- Γ . A ⊢ B type
  wkn-type-by : ∀ {ℓA ℓB} (A : DispNRG ℓA Γ) (B : DispNRG ℓB Γ) →
               DispNRG ℓB (Γ # A)
  wkn-type-by A B =
    record {
      dcr = λ γa → B .dcr (γa .fst) ;
      dedge = λ γa0 γa1 γγaa → B .dedge (γa0 .fst) (γa1 .fst) (γγaa .fst) ;
      dnativ = λ γa0 γa1 γγaa → B .dnativ (γa0 .fst) (γa1 .fst) (γγaa .fst)
    }

open AuxRules public

-- remove empty context dependency.
rem-top-ctx : ∀ {ℓA} (A : DispNRG ℓA topNRG) → NRGraph ℓA
rem-top-ctx A =
  record {
    nrg-cr = A .dcr tt ;
    nedge = λ a0 a1 → A .dedge tt tt tt a0 a1 ;
    nativ = λ a0 a1 → A .dnativ tt tt tt a0 a1  }


module UrulesNRG {ℓ} (Γ : NRGraph ℓ) where

  -- -----------
  -- Γ ⊢ U(l) type(l+1)
  UForm : ∀ (ℓU : Level) → DispNRG (ℓ-suc ℓU) Γ
  UForm ℓU =
    record {
    dcr = λ _ → Type ℓU ;
    dedge = λ _ _ _ A0 A1 → A0 → A1 → Type ℓU ;
    dnativ = λ _ _ _ A0 A1 → relativity }

  -- applied version of the El universal family
  -- Γ ⊢ C : U(l)
  -- -----------------
  -- Γ ⊢ El C : type(l)
  -- {ℓ'} (Disp ℓ' Γ)

  

open UrulesNRG public


module ΣrulesNRG {ℓ ℓA ℓB} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) where

  -- Γ ⊢ A type
  -- Γ . A ⊢ B type
  -- --------------
  -- Γ ⊢ Σ A B type
  ΣForm : DispNRG (ℓ-max ℓA ℓB) Γ
  ΣForm =
    record {
      dcr = λ γ → Σ (A .dcr γ) (λ a → B .dcr (γ , a))  ;
      dedge = λ γ0 γ1 γγ ab0 ab1 →  Σ (A .dedge γ0 γ1 γγ (ab0 .fst) (ab1 .fst)) (λ aa → B .dedge (γ0 , ab0 .fst) (γ1 , ab1 .fst) ( (γγ , aa)) (ab0 .snd) (ab1 .snd)) ;
      dnativ =
        λ γ0 γ1 γγ ab0 ab1 → flip compEquiv ΣvsBridgeP
                                            (Σ-cong-equiv (A .dnativ γ0 γ1 γγ (ab0 .fst) (ab1 .fst)) λ aa →
                                            B .dnativ (γ0 , ab0 .fst) (γ1 , ab1 .fst) (γγ , aa) (ab0 .snd) (ab1 .snd)) }
open ΣrulesNRG public



-- PtdTypeNRG'' : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
-- PtdTypeNRG'' ℓ = ΣForm
--                    topNRG -- ctx
--                    (UForm topNRG ℓ) -- 1 ⊢ Ul type
--                    -- 1, A:Ul ⊢ A : Ul
--                    (wkn-type-by topNRG (UForm topNRG ℓ) {!!})

-- -- goal DispNRG _ℓB_1562 (topNRG # UForm topNRG ℓ)

-- PtdTypeNRG' : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
-- PtdTypeNRG' ℓ = rem-top-ctx (PtdTypeNRG'' ℓ)

-- testt : _
-- testt = PtdTypeNRG' ℓ-zero .nedge {!!}
