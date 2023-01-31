{-
  a record version of NRGraph, instead of instance version
-}

{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
-- -v tc.prim.ungel:30 -v tc.conv.term:30 -v tc.conv.gel:40 -v tc.reduce:90 -v tc.prim.mhcomp.gel:30 
-- -v tc.prim.ungel:30  -v tc.prim.transp.bridge:40 -v tc.prim.mhcomp.gel:30 -v tc.app.mpor:30 -v tc.app.mhocom:30
--  -v tc.prim.mhcomp.gel:30 
-- -v tc.prim.ungel:27 -v tc.prim.mhcomp:25 -v tc.prim.transp:25 -v tc.conv.gel:25
-- -v tc.term.args.target:30 


module Bridgy.NRGRelRecord where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Agda.Builtin.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma using (_×_ ; ≃-× ; ≡-× ; Σ-cong-equiv ; Σ-cong-equiv-snd)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (congPathEquiv ; PathP≃Path ; compPathrEquiv ; compPathlEquiv)
open import Cubical.Foundations.Transport using (transportEquiv)

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

-- TYPES
-- a Γ-displayed NRG is basically a NRG over Gamma (other side of some Grothendieck corr for NRG)
-- this would correspond to semantics of the @Ty@ operation of CwFs
record DispNRG {ℓ} (ℓ' : Level) (Γ : NRGraph ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  no-eta-equality
  field
    -- displayed carriers
    dcr : Γ .nrg-cr → Type ℓ'
    -- displayed edges
    dedge : ∀ (γ0 γ1 : Γ .nrg-cr) (e : Γ ⦅ γ0 , γ1 ⦆ ) (a0 : dcr γ0) (a1 : dcr γ1) → Type ℓ'
    -- displayed nativeness ("forall bridge" version)
    -- we choose this version to be able to formulate tm-natv as ∀ bridge as well.
    dnativ : ∀ (γ0 γ1 : Γ .nrg-cr) (γbdg : BridgeP (λ _ → Γ .nrg-cr) γ0 γ1) (a0 : dcr γ0) (a1 : dcr γ1) →
                   dedge γ0 γ1 (invEq (Γ .nativ γ0 γ1) γbdg) a0 a1 ≃ BridgeP (λ x → dcr (γbdg x)) a0 a1
open DispNRG public

    -- dnativ : ∀ (γ0 γ1 : Γ .nrg-cr) (e : Γ ⦅ γ0 , γ1 ⦆ ) (a0 : dcr γ0) (a1 : dcr γ1) →
    --                dedge γ0 γ1 e a0 a1 ≃ BridgeP (λ x → dcr (Γ .nativ γ0 γ1 .fst e x)) a0 a1

_⦅_,_⦆#_ : ∀ {ℓ ℓ' : Level} {Γ} (A : DispNRG {ℓ = ℓ} ℓ' Γ) {γ0 γ1 : Γ .nrg-cr} (a0 : A .dcr γ0) (a1 : A .dcr γ1) (γγ : Γ ⦅ γ0 , γ1 ⦆) → Type ℓ'
_⦅_,_⦆#_ {ℓ} {ℓ'} {Γ} A {γ0} {γ1} a0 a1 γγ = A .dedge γ0 γ1 γγ a0 a1


-- dnativ' : ∀ {ℓ ℓ'} (Γ : NRGraph ℓ) (A : DispNRG ℓ' Γ)
--               (γ0 γ1 : Γ .nrg-cr) (q : BridgeP (λ _ → Γ .nrg-cr) γ0 γ1) →
--               A .dedge γ0 γ1
-- dnativ' = {!!}

-- TERMS
-- semantical terms are sections of displayed NRGs
record SectNRG {ℓ} {ℓA} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) : Type (ℓ-max ℓ ℓA) where
  field
    -- action on Γ's 0-cells
    ac0 : ∀ (γ : Γ .nrg-cr) → A .dcr γ
    -- action on Γ's 1-cells
    ac1 : ∀ (γ0 γ1 : Γ .nrg-cr) (γγ : Γ ⦅ γ0 , γ1 ⦆) → A ⦅ ac0 γ0 , ac0 γ1 ⦆# γγ
    tm-nativ : ∀ (γ0 γ1 : Γ .nrg-cr) (γbdg : BridgeP (λ _ → Γ .nrg-cr) γ0 γ1) →
                 ac1 γ0 γ1 (invEq (Γ .nativ γ0 γ1) γbdg) ≡ invEq (A .dnativ γ0 γ1 γbdg (ac0 γ0) (ac0 γ1)) (λ x → ac0 (γbdg x) )
open SectNRG public


-- Ty subst
-- σ : Γ → Δ    Δ ⊢ A type
-- ------------------------
-- Γ ⊢ A type
tySubst : ∀ {ℓΓ ℓΔ ℓ} (Γ : NRGraph ℓΓ) (Δ : NRGraph ℓΔ) →
            (NRelator Γ Δ) → (DispNRG ℓ Δ) → 
            DispNRG ℓ Γ
tySubst {ℓΔ = ℓΔ} Γ Δ σ A = record {
  dcr = λ γ → A .dcr ( σ .nobjMap γ )
  ; dedge = λ γ0 γ1 γγ → A .dedge (σ .nobjMap γ0) (σ .nobjMap γ1) (σ .nedgeMap γγ) 
  ; dnativ = λ γ0 γ1 γbdg a0 a1 → flip compEquiv (A .dnativ (σ .nobjMap γ0) (σ .nobjMap γ1) (λ x → σ .nobjMap (γbdg x)) a0 a1)
                                   (pathToEquiv (cong (λ blank → A .dedge (σ .nobjMap γ0) (σ .nobjMap γ1) blank a0 a1)
                                   (funExt⁻ (σ .nativ-rel γ0 γ1) γbdg))) }

-- + equations... behaves as a functor

-- this cwf would be wonderful if we had cwf equations by refl.
-- tySubstId : ∀ {ℓΔ ℓ} {Δ : NRGraph ℓΔ} (A : DispNRG ℓ Δ) → 
--               tySubst (idNRelator {G = Δ}) A ≡ A
-- tySubstId {Δ = Δ} A = {!!} 


-- tm subst, + equations...

-- we choose topNRG as our empty context.


-- Ctx extension: one side of the NRG Grothendieck correspondance.

-- Γ ctx
-- Γ ⊢ A type
-- ----------
-- Γ.A ctx
_#_ : ∀ {ℓ ℓ'} (Γ : NRGraph ℓ) (A : DispNRG ℓ' Γ) → NRGraph (ℓ-max ℓ ℓ')
_#_ Γ A =
  record {
    nrg-cr = Σ (Γ .nrg-cr) (A .dcr)
    -- nedge maps by copatterns, nativ by pattern matching seems nice?
    ; nedge = λ γa0 γa1 → Σ (Γ .nedge (γa0 .fst) (γa1 .fst)) (λ γγ → A .dedge (γa0 .fst) (γa1 .fst) γγ (γa0 .snd) (γa1 .snd))
    -- ; nedge = λ { ( γ0 , a0 ) (γ1 , a1 ) → Σ (Γ .nedge (γ0) (γ1)) (λ γγ → A .dedge γ0 γ1 γγ a0 a1) }
    ; nativ = λ { (γ0 , a0 ) (γ1 , a1 ) →
                flip compEquiv ΣvsBridgeP (invEquiv
                (Σ-cong-equiv (invEquiv (Γ .nativ γ0 γ1)) λ γbdg → invEquiv (A .dnativ γ0 γ1 γbdg a0 a1)))   }}

infixl 40 _#_


-- Γ ⊢ A type
-- Γ ⊢ B type
-- ----------
-- Γ . A ⊢ B type
wkn-type-by : ∀ {ℓ ℓA ℓB} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (B : DispNRG ℓB Γ) →
             DispNRG ℓB (Γ # A)
wkn-type-by Γ A B =
  record {
    dcr = λ γa → B .dcr (γa .fst) ;
    dedge = λ γa0 γa1 γγaa → B .dedge (γa0 .fst) (γa1 .fst) (γγaa .fst) ;
    dnativ = λ { (γ0 , a0) (γ1 , a1) γbdg b0 b1 → B .dnativ γ0 γ1 (λ x → γbdg x .fst) b0 b1 }
  }

-- gen-wkn-type-by : ∀ {ℓΓ ℓA ℓΔ ℓB} {Γ : NRGraph ℓ}
--                     (A : DispNRG ℓA Γ) 

-- -- Γ ⊢ A type
-- -- Γ ⊢ B type
-- -- Γ ⊢ C type
-- -- ----------
-- -- (Γ . A) . B ⊢ C type
-- wkn-type-by-by : ∀ {ℓ ℓA ℓB ℓC} {Γ : NRGraph ℓ} (A : DispNRG ℓA Γ) (B : DispNRG ℓB Γ) (C : DispNRG ℓC Γ)
--                     → DispNRG ℓC (Γ # A # B)
-- wkn-type-by-by A B C = ?


-- Γ ⊢ A type
-- -------------------
-- Γ , (x : A) ⊢ x : A
var-rule : ∀ {ℓ} {ℓA} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) →
  SectNRG (Γ # A) (wkn-type-by Γ A A)
var-rule Γ A =
  record {
    ac0 = λ γa → γa .snd ;
    ac1 = λ γa0 γa1 γγaa → γγaa .snd ;
    tm-nativ = λ γa0 γa1 γγaa → refl }


-- open AuxRules public


-- -- Γ ⊢ A type   Γ.A ⊢ B type
-- -- -----------------------
-- -- Γ, a : A, b : B ⊢ a : A
-- var1-rule : ∀ {ℓ} {ℓA} {ℓB} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) →
--   SectNRG (Γ # A # B) (wkn-type-by _ B (wkn-type-by _ A A))
-- var1-rule = λ Γ A B → record {
--   ac0 = λ γa-b → γa-b .fst .snd ;
--   ac1 = λ γa-b0 γa-b1 γγaa-bb → γγaa-bb .fst .snd ;
--   tm-nativ = λ γa-b0 γa-b1 γγaa-bb → refl }

-- -- Γ ⊢ A type   Γ.A ⊢ B type   Γ.A.B ⊢ C type
-- -- -------------------------------------------
-- -- Γ, a:A, b:B, c:C ⊢ a:A
-- var2-rule : ∀ {ℓ} {ℓA} {ℓB} {ℓC} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) (C : DispNRG ℓC (Γ # A # B)) →
--   SectNRG (Γ # A # B # C) (wkn-type-by _ C (wkn-type-by _ B (wkn-type-by _ A A)))
-- var2-rule = λ Γ A B C → record {
--   ac0 = λ γa-b-c → γa-b-c .fst .fst .snd ;
--   ac1 = λ γa-b-c0 γa-b-c1 → λ γγaa-bb-cc → γγaa-bb-cc .fst .fst .snd ;
--   tm-nativ = λ _ _ _ → refl }

-- -- Γ ⊢ A type   Γ.A ⊢ B type   Γ.A.B ⊢ C type
-- -- -------------------------------------------
-- -- Γ, a:A, b:B, c:C ⊢ b:B
-- var1over3 : ∀ {ℓ} {ℓA} {ℓB} {ℓC} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) (C : DispNRG ℓC (Γ # A # B)) →
--   SectNRG (Γ # A # B # C) (wkn-type-by _ C (wkn-type-by _ B B))
-- var1over3 Γ A B C = record {
--   ac0 = λ γa-b-c → γa-b-c .fst .snd ;
--   ac1 = λ γa-b-c0 γa-b-c1 γγaa-bb-cc → γγaa-bb-cc .fst .snd ;
--   tm-nativ = λ _ _ _ → refl }


-- remove empty context dependency.
rem-top-ctx : ∀ {ℓA} (A : DispNRG ℓA topNRG) → NRGraph ℓA
rem-top-ctx A =
  record {
    nrg-cr = A .dcr tt ;
    nedge = λ a0 a1 → A .dedge tt tt tt a0 a1 ;
    nativ = λ a0 a1 → A .dnativ tt tt (λ _ → tt) _ _  }




-- -----------------
-- Γ ⊢ U(l) type(l+1)
TypeForm : ∀ {ℓΓ} (Γ : NRGraph ℓΓ) → (ℓ : Level) → DispNRG (ℓ-suc ℓ) Γ
TypeForm Γ ℓ =
  record {
  dcr = λ _ → Type ℓ ;
  dedge = λ _ _ _ A0 A1 → A0 → A1 → Type ℓ ;
  dnativ = λ _ _ _ A0 A1 → relativity }

-- ----------------------------
-- Γ, A : Type ℓ ⊢ El A type(ℓ)
El : ∀ {ℓΓ} (Γ : NRGraph ℓΓ) (ℓ : Level) →
       DispNRG ℓ (Γ # TypeForm Γ ℓ)
El Γ ℓ = record {
  dcr = λ γA → γA .snd
  ; dedge = λ γA0 γA1 γγAA → γγAA .snd 
  ; dnativ = λ { (γ0 , A0) (γ1 , A1) γbdg a0 a1 → idEquiv _ } }

--   -- applied version of the El universal family
--   -- Γ ⊢ C : U(l')
--   -- -----------------
--   -- Γ ⊢ El C : type(l')
--   ElApply : ∀ {ℓ' : Level} → (SectNRG Γ (UForm ℓ')) → DispNRG ℓ' Γ
--   ElApply {ℓ'} C {- codes over Γ -} =
--     record {
--       dcr = C .ac0 ;
--       dedge = λ γ0 γ1 γγ → C .ac1 γ0 γ1 γγ ;
--       dnativ = λ γ0 γ1 γγ a0 a1 →
--         pathToEquiv (funExt⁻ (funExt⁻ (left-skew-tm-nativ Γ (UForm ℓ') C γ0 γ1 γγ) a0) a1) }

  



-- for now keeping Γ implicit seems to work (leads to no dumb type conversion instead of syn eq)
module ΣΠrulesNRG {ℓΓ ℓA ℓB} {Γ : NRGraph ℓΓ} (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) where

  -- Γ ⊢ A type
  -- Γ . A ⊢ B type
  -- --------------
  -- Γ ⊢ Σ A B type
  ΣForm : DispNRG (ℓ-max ℓA ℓB) Γ
  ΣForm =
    record {
      dcr = λ γ → Σ (A .dcr γ) (λ a → B .dcr (γ , a))  ;
      dedge = λ γ0 γ1 γγ ab0 ab1 →  Σ (A .dedge γ0 γ1 γγ (ab0 .fst) (ab1 .fst)) (λ aa → B .dedge (γ0 , ab0 .fst) (γ1 , ab1 .fst) ( (γγ , aa)) (ab0 .snd) (ab1 .snd)) ;
      dnativ = λ { γ0 γ1 γbdg (a0 , b0) (a1 , b1) →
        flip compEquiv ΣvsBridgeP (invEquiv
        (Σ-cong-equiv (invEquiv (A .dnativ _ _ γbdg a0 a1 )) λ abdg →
        invEquiv (B .dnativ (γ0 , a0) (γ1 , a1) (λ x → (γbdg x , abdg x )) b0 b1) )) }
    }

  -- -- Γ ⊢ A type
  -- -- Γ.A ⊢ B type
  -- -- --------------
  -- -- Γ ⊢ Π A B type
  ΠForm : DispNRG (ℓ-max ℓA ℓB) Γ
  ΠForm = record {
    dcr = λ γ → ∀ (a : A .dcr γ) → B .dcr (γ , a) ;
    dedge = λ γ0 γ1 γγ f0 f1 → ∀ (a0 : A .dcr γ0) (a1 : A .dcr γ1) (aa : A ⦅ a0 , a1 ⦆# γγ ) → B ⦅ f0 a0 , f1 a1 ⦆# (γγ , aa) ;
    dnativ = λ γ0 γ1 γbdg f0 f1 →
      flip compEquiv ΠvsBridgeP
      (equivΠCod λ a0 →
      equivΠCod λ a1 → invEquiv
      (equivΠ (invEquiv (A .dnativ _ _ γbdg a0 a1)) λ abdg →
      (invEquiv (B .dnativ (γ0 , a0) (γ1 , a1) (λ x → (γbdg x , abdg x)) (f0 a0) (f1 a1))) ) )
    }
open ΣΠrulesNRG public


adjustPathPEnds : ∀ {ℓ : Level} {A : I → Type ℓ} {a0' a0 : A i0} {a1' a1 : A i1} (prf0 : a0' ≡ a0) (prf1 : a1' ≡ a1)  →
                    PathP A a0' a1' ≃ PathP A a0 a1
adjustPathPEnds {A = A} {a0' = a0'} {a0 = a0}{a1' = a1'} {a1 = a1} prf0 prf1 =
  compEquiv (PathP≃Path A a0' a1')
  (compEquiv (compPathrEquiv prf1)
  (compEquiv (compPathlEquiv {x = transport (λ i → A i) a0} (cong (transport (λ i → A i)) (sym prf0)) )
  (invEquiv (PathP≃Path (λ i → A i) a0 a1))))


-- -- adjustPathPEnds {A = A} {a0' = a0'} {a0 = a0} prf0 prf1 =
-- --   isoToEquiv (iso
-- --     (λ strt i →  hcomp (λ j → λ {(i = i0) → prf0 j ; (i = i1) → prf1 j}) (strt i))
-- --     (λ end i →  hcomp (λ j → λ {(i = i0) → prf0 (~ j) ; (i = i1) → prf1 (~ j)}) (end i) )
-- --     (λ thing → {!!})
-- --     {!!})






-- Γ ⊢ A type
-- Γ ⊢ a : A
-- Γ ⊢ b : A
-------------------
-- Γ ⊢ a ≡A b type
PathForm : ∀ {ℓΓ ℓA} (Γ : NRGraph ℓΓ)
             (A : DispNRG ℓA Γ) (a b : SectNRG Γ A) → DispNRG ℓA Γ
PathForm Γ A a b = record {
  dcr = λ γ → (Path (A .dcr γ) (a .ac0 γ) (b .ac0 γ)) ;
  dedge = λ γ0 γ1 γγ pa pb → PathP (λ i → A ⦅ pa i , pb i ⦆# γγ) (a .ac1 γ0 γ1 γγ) (b .ac1 γ0 γ1 γγ) ;
  dnativ = λ γ0 γ1 γbdg pa pb →
    flip compEquiv (PathPvsBridgeP (λ x i → A .dcr (γbdg x))) (invEquiv
    (compEquiv (congPathEquiv (λ i → invEquiv (A .dnativ _ _ γbdg (pa i) (pb i)) )) (invEquiv
    (adjustPathPEnds (a .tm-nativ _ _ γbdg) (b .tm-nativ _ _ γbdg)))))
  }
  -- when dnativ had ∀edge phrasing...
  -- dnativ = λ γ0 γ1 γγ pa pb → flip compEquiv (PathPvsBridgeP (λ x i → A .dcr (Γ .nativ γ0 γ1 .fst γγ x)))
  --                              (flip compEquiv (adjustPathPEnds (sym (a .tm-nativ γ0 γ1 γγ)) (sym (b .tm-nativ γ0 γ1 γγ)))
  --                             (congPathEquiv λ i → A .dnativ γ0 γ1 γγ (pa i) (pb i))) }
  
  
  


-- module PointedTypes where

--   -- We build the NRG of pointed types in one go
--   -- Its field are the expected ones up to normalisation.

--   PointedTypesNRG0 : ∀ (ℓ : Level) → DispNRG (ℓ-suc ℓ) topNRG
--   PointedTypesNRG0 ℓ = ΣForm topNRG
--                          (UForm topNRG ℓ) -- Γ ⊢ Ul type(l+1)
--                          (ElApply (topNRG # (UForm  topNRG ℓ)) -- 1.X:Ul ⊢ X type(l)
--                            (var-rule topNRG (UForm topNRG ℓ))) -- 1.X:Ul ⊢ X : Ul

--   PointedTypesNRG1 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
--   PointedTypesNRG1 ℓ = rem-top-ctx (PointedTypesNRG0 ℓ)

--   pointedTypesCarrier : PointedTypesNRG1 ℓ-zero .nrg-cr ≡ Σ Type (λ A → A)
--   pointedTypesCarrier = refl
  
--   pointedTypesEdges : PointedTypesNRG1 ℓ-zero .nedge
--                      ≡ 
--                      λ Aa0 Aa1 → Σ (Aa0 .fst → Aa1 .fst → Type) λ R → R (Aa0 .snd) (Aa1 .snd)
--   pointedTypesEdges = refl

-- {-

-- heyy : ∀ {ℓ} →
--          DispNRG ℓ (topNRG # TypeForm ℓ # El ℓ # wkn-type-by (topNRG # TypeForm ℓ) (El ℓ) (El ℓ)) →
--          DispNRG ℓ (topNRG # TypeForm ℓ # El ℓ # wkn-type-by (topNRG # TypeForm ℓ) (El ℓ) (El ℓ))
-- heyy stuff = stuff





module HProp where


  -- the context is explicit in our DSL
  -- this way we have syntactic equality
  -- else agda compares at record types with exponential time

  -- 1, A : Type ℓ, c c' : El A ⊢ c ≡ c' type(l)
  -- ------------------------------------------- ...
  -- 1, A : Type ℓ ⊢ isProp(A) type(l)
  isPropNRGFromOpenPath :
    ∀ (ℓ : Level) →
    DispNRG ℓ (topNRG # 
      TypeForm topNRG ℓ #
      El topNRG ℓ #
      wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)) →
    DispNRG (ℓ) (topNRG # TypeForm topNRG ℓ)
  isPropNRGFromOpenPath ℓ  openPath =
    -- 1, A : Type ℓ ⊢ isProp A
    (ΠForm (El topNRG ℓ) -- Π A $ λ c → 
    (ΠForm {ℓB = ℓ} (wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)) -- Π A $ λ c' → 
    openPath ))  -- c ≡ c'

  -- 1, A : Type ℓ, c c' : El A ⊢ c ≡ c' type(l)
  myOpenPath : ∀ (ℓ : Level) →
    DispNRG ℓ (
      topNRG # 
      TypeForm topNRG ℓ #
      El topNRG ℓ #
      wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)
    )
  myOpenPath ℓ =
    PathForm totalCtx
    -- 1, A : Type ℓ, c, c' ⊢ El A type(l)
    -- wkning the type = substituting by a 'forgetful' subst
    (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst (El topNRG ℓ))
    -- 1, A : Type ℓ, c : El A, c' : El A ⊢ c : El A
    lhs rhs

    where
      
      totalCtx : NRGraph (ℓ-suc ℓ)
      totalCtx = topNRG # 
        TypeForm topNRG ℓ #
        El topNRG ℓ #
        wkn-type-by (topNRG # TypeForm topNRG ℓ) (El topNRG ℓ) (El topNRG ℓ)  

      smlrCtx : NRGraph (ℓ-suc ℓ)
      smlrCtx = topNRG # TypeForm topNRG ℓ # El topNRG ℓ

      aWkSubst : NRelator totalCtx (topNRG # TypeForm topNRG ℓ)
      aWkSubst = record {
        nobjMap =  λ { ( ( ( tt , A ) , c ) , c' ) →  ( tt , A ) } ;
        nedgeMap =
          λ { {g0 = ( ( ( tt , A0 ) , c0 ) , c0' ) } {g1 = ( ( ( tt , A1 ) , c1 ) , c1' ) } ( ( ( tt , AA ) , cc ) , cc' ) → 
           (tt , AA)  } ;
        nativ-rel =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) → refl } 
        }

      lhs : SectNRG totalCtx
             (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst (El topNRG ℓ))
      lhs = record {
        ac0 = λ { ( ( ( tt , A ) , c ) , c' ) → c } ;
        ac1 =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) ( ( ( tt , AA ) , cc ) , cc' ) →
          cc  } ;
        tm-nativ =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) γbdg →
          sym (transportRefl (λ x → snd (fst (γbdg x)))) }
        }

      rhs : SectNRG totalCtx
             (tySubst totalCtx (topNRG # TypeForm topNRG ℓ) aWkSubst
              (El topNRG ℓ))
      rhs = record {
        ac0 =  λ { ( ( ( tt , A ) , c ) , c' ) → c' } ;
        ac1 =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) ( ( ( tt , AA ) , cc ) , cc' ) →
          cc'  }  ;
        tm-nativ =  λ { ( ( ( tt , A0 ) , c0 ) , c0' ) ( ( ( tt , A1 ) , c1 ) , c1' ) γbdg →
          sym (transportRefl (λ x → snd (γbdg x))) } }

  -- 1, A : Type ℓ ⊢ isProp(A) type(l)
  isPropDispNRG : ∀ {ℓ : Level} → DispNRG ℓ (topNRG # TypeForm topNRG ℓ)
  isPropDispNRG {ℓ = ℓ} = isPropNRGFromOpenPath ℓ (myOpenPath ℓ)

  -- there's a simpler characterization of hProp { P0 , P1 }
  hPropNRG0 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG0 ℓ =
    rem-top-ctx -- DispNRG ℓ+1 topNRG
      (ΣForm (TypeForm topNRG ℓ) (isPropDispNRG))
      

  -- just rewriting nicely
  hPropNRG1 : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
  hPropNRG1 ℓ = record {
    nrg-cr = hProp ℓ ;
    nedge =  λ { (P0 , isp0) (P1 , isp1) →
                  Σ (P0 → P1 → (Type ℓ)) (λ PP →
                  (p0 : P0) (p1 : P1) (pp : PP p0 p1) →
                  (p0' : P0) (p1' : P1) (pp' : PP p0' p1') →
                  PathP (λ i → PP (isp0 p0 p0' i) (isp1 p1 p1' i)) pp pp') } ;
    nativ = hPropNRG0 ℓ .nativ
    }

  hPropEdgeCharac : ∀ {ℓ} (P0 P1 : Type ℓ) (isp0 : isProp P0) (isp1 : isProp P1) →
    (P0 → P1 → (hProp ℓ))
    ≃
    Σ (P0 → P1 → Type ℓ) (λ PP →
        (p0 : P0) (p1 : P1) (pp : PP p0 p1) →
        (p0' : P0) (p1' : P1) (pp' : PP p0' p1') →
        PathP (λ i → PP (isp0 p0 p0' i) (isp1 p1 p1' i)) pp pp')
  hPropEdgeCharac P0 P1 isp0 isp1 =
    isoToEquiv (iso
      (λ mrel →  (  (λ p0 p1 → mrel p0 p1 .fst) ,
                     λ p0 p1 pp p0' p1' pp' →  toPathP (mrel p0' p1' .snd _ _) ))
      (λ { (PP , prf) →  λ p0 p1 →
               (PP p0 p1 ,
               λ aa aa' → {!congPathEquiv {A = λ i → PP (isp0 p0 p0 i) (isp1 p1 p1 i)} {B = λ i → PP p0 p1}
                           (λ i → pathToEquiv (λ j → PP (ispRefl P0 isp0 p0 i j) (ispRefl P1 isp1 p1 i j) ) )!} ) }) {!!} {!!}) -- prf p0 p1 aa p0 p1 aa'

    where

      ispRefl : ∀ {ℓ} (P : Type ℓ) (isp : isProp P) (p : P) (i : I) →
        isp p p i ≡ p
      ispRefl P isp p i = isp (isp p p i) p

  -- could be more helpful to prove
  -- Let P0 P1 be hProps (with proofs isp0 isp1), R : P0 → P1 → Type ℓ relation
  -- then
  -- (∀ p0 p1, isProp (R p0 p1)) ≃ isProp{ isp0, isp1 }# R
  -- the displayed edges of isProp express "being a mere relation"

  -- isSet X <-> (x : A) → isProp (x ≡ x)



















--     ΣForm topNRG
--       {- A type code A-} (UForm topNRG ℓ)
--       {- isContr(El A) -} (ΣForm {ℓA = ℓ} {ℓB = ℓ} (topNRG # UForm topNRG ℓ)
--         {- El A -} (ElApply (topNRG # UForm topNRG ℓ) (var-rule topNRG (UForm topNRG ℓ)))
--         {- isContr -} (ΠForm (topNRG # UForm topNRG ℓ #
--            ElApply (topNRG # UForm topNRG ℓ)
--            (var-rule topNRG (UForm topNRG ℓ)))
--              (ElApply _ (var1-rule topNRG (UForm topNRG ℓ) (ElApply (topNRG # UForm topNRG ℓ) (var-rule topNRG (UForm topNRG ℓ)))))
--              (PathForm _ (ElApply _ (var2-rule topNRG (UForm topNRG ℓ) (ElApply (topNRG # UForm topNRG ℓ) (var-rule topNRG (UForm topNRG ℓ)))
--                        (ElApply
--                         (topNRG # UForm topNRG ℓ #
--                          ElApply (topNRG # UForm topNRG ℓ)
--                          (var-rule topNRG (UForm topNRG ℓ)))
--                         (var1-rule topNRG (UForm topNRG ℓ)
--                          (ElApply (topNRG # UForm topNRG ℓ)
--                           (var-rule topNRG (UForm topNRG ℓ)))))))
--                {!var1over3 topNRG (UForm topNRG ℓ) 
--                   (ElApply (topNRG # UForm topNRG ℓ)
--                   (var-rule topNRG (UForm topNRG ℓ)))
--                     (ElApply
--                      (topNRG # UForm topNRG ℓ #
--                       ElApply (topNRG # UForm topNRG ℓ)
--                       (var-rule topNRG (UForm topNRG ℓ)))
--                      (var1-rule topNRG (UForm topNRG ℓ)
--                       (ElApply (topNRG # UForm topNRG ℓ)
--                        (var-rule topNRG (UForm topNRG ℓ)))))!} {!!})))

-- -}

-- -- conversion seems to loop. why
-- -- {compareTerm
-- -- and then loop.
-- -- tc.conv.term:30 loops after a comparison at primGel (compareTm')
-- -- (bm' , m') <- reduceWithBlocker m for m equals

-- {-

-- m in context:
-- (ℓ₁ : Level)
-- (γ0
--  : (topNRG # UForm topNRG ℓ₁ #
--     ElApply (topNRG # UForm topNRG ℓ₁)
--     (var-rule topNRG (UForm topNRG ℓ₁))
--     #
--     ElApply
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (var1-rule topNRG (UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    .nrg-cr)
-- (γ1
--  : (topNRG # UForm topNRG ℓ₁ #
--     ElApply (topNRG # UForm topNRG ℓ₁)
--     (var-rule topNRG (UForm topNRG ℓ₁))
--     #
--     ElApply
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (var1-rule topNRG (UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    .nrg-cr)
-- (e
--  : (topNRG # UForm topNRG ℓ₁ #
--     ElApply (topNRG # UForm topNRG ℓ₁)
--     (var-rule topNRG (UForm topNRG ℓ₁))
--     #
--     ElApply
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (var1-rule topNRG (UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    ⦅ γ0 , γ1 ⦆)
-- (a0
--  : dcr
--    (wkn-type-by
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (ElApply
--      (topNRG # UForm topNRG ℓ₁ #
--       ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (var1-rule topNRG (UForm topNRG ℓ₁)
--       (ElApply (topNRG # UForm topNRG ℓ₁)
--        (var-rule topNRG (UForm topNRG ℓ₁)))))
--     (wkn-type-by (topNRG # UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    γ0)
-- (a1
--  : dcr
--    (wkn-type-by
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (ElApply
--      (topNRG # UForm topNRG ℓ₁ #
--       ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (var1-rule topNRG (UForm topNRG ℓ₁)
--       (ElApply (topNRG # UForm topNRG ℓ₁)
--        (var-rule topNRG (UForm topNRG ℓ₁)))))
--     (wkn-type-by (topNRG # UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    γ1)
-- (x
--  : dedge
--    (wkn-type-by
--     (topNRG # UForm topNRG ℓ₁ #
--      ElApply (topNRG # UForm topNRG ℓ₁)
--      (var-rule topNRG (UForm topNRG ℓ₁)))
--     (ElApply
--      (topNRG # UForm topNRG ℓ₁ #
--       ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (var1-rule topNRG (UForm topNRG ℓ₁)
--       (ElApply (topNRG # UForm topNRG ℓ₁)
--        (var-rule topNRG (UForm topNRG ℓ₁)))))
--     (wkn-type-by (topNRG # UForm topNRG ℓ₁)
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))
--      (ElApply (topNRG # UForm topNRG ℓ₁)
--       (var-rule topNRG (UForm topNRG ℓ₁)))))
--    γ0 γ1 e a0 a1)
-- (i : BI)

-- (fst
--  (lineToEquiv
--   (λ i →
--      funExt⁻
--      (funExt⁻
--       (left-skew-tm-nativ (topNRG # UForm topNRG ℓ)
--        (UForm (topNRG # UForm topNRG ℓ) ℓ)
--        (var-rule topNRG (UForm topNRG ℓ)) (γ0 .fst .fst) (γ1 .fst .fst)
--        (e .fst .fst))
--       a0)
--      a1 i))
--  x i)

-- with tc.reduce:90, we have a loop (?) of prim^gel appearing

-- -}


-- atel : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
-- atel ℓ = (topNRG # UForm topNRG ℓ #
--           ElApply (topNRG # UForm topNRG ℓ)
--           (var-rule topNRG (UForm topNRG ℓ))
--           #
--           ElApply
--           (topNRG # UForm topNRG ℓ #
--            ElApply (topNRG # UForm topNRG ℓ)
--            (var-rule topNRG (UForm topNRG ℓ)))
--           (var1-rule topNRG (UForm topNRG ℓ)
--            (ElApply (topNRG # UForm topNRG ℓ)
--             (var-rule topNRG (UForm topNRG ℓ)))))

-- atyp : ∀ (ℓ : Level) → DispNRG _ (atel ℓ)
-- atyp ℓ = (wkn-type-by
--           (topNRG # UForm topNRG ℓ #
--            ElApply (topNRG # UForm topNRG ℓ)
--            (var-rule topNRG (UForm topNRG ℓ)))
--           (ElApply
--            (topNRG # UForm topNRG ℓ #
--             ElApply (topNRG # UForm topNRG ℓ)
--             (var-rule topNRG (UForm topNRG ℓ)))
--            (var1-rule topNRG (UForm topNRG ℓ)
--             (ElApply (topNRG # UForm topNRG ℓ)
--              (var-rule topNRG (UForm topNRG ℓ)))))
--           (wkn-type-by (topNRG # UForm topNRG ℓ)
--            (ElApply (topNRG # UForm topNRG ℓ)
--             (var-rule topNRG (UForm topNRG ℓ)))
--            (ElApply (topNRG # UForm topNRG ℓ)
--             (var-rule topNRG (UForm topNRG ℓ)))))

-- module Bug (ℓ : Level) (γ0 γ1 : atel ℓ .nrg-cr) (γγ : atel ℓ ⦅ γ0 , γ1 ⦆)
--               (a0 : atyp ℓ .dcr γ0) (a1 : atyp ℓ .dcr γ1) (aa : atyp ℓ ⦅ a0 , a1 ⦆# γγ)
--               (@tick z : BI) where

-- {-
-- (fst
--  (lineToEquiv
--   (λ i →
--      funExt⁻
--      (funExt⁻
--       (left-skew-tm-nativ (topNRG # UForm topNRG ℓ)
--        (UForm (topNRG # UForm topNRG ℓ) ℓ)
--        (var-rule topNRG (UForm topNRG ℓ)) (γ0 .fst .fst) (γ1 .fst .fst)
--        (e .fst .fst))
--       a0)
--      a1 i))
--  x i)
-- -}
--   1,X:Ul⊢Ul:type = (UForm (topNRG # UForm topNRG ℓ) ℓ)

--   1,X:Ul⊢X:Ul = (var-rule topNRG (UForm topNRG ℓ))
--   t = 1,X:Ul⊢X:Ul

-- -- 

--   thing : Bool
--   thing = {! left-skew-tm-nativ (topNRG # UForm topNRG ℓ) (UForm (topNRG # UForm topNRG ℓ) ℓ) t (γ0 .fst .fst) (γ1 .fst .fst) (γγ .fst .fst) !}
-- {-
--  goal : γγ .fst .fst .snd ≡
--                               BridgeP
--                               (λ x →
--                                  primGel (γ0 .fst .fst .snd) (γ1 .fst .fst .snd)
--                                  (snd (γγ .fst .fst)) x)

-- leads to impossible when normalised
-- -}



-- module Bug2 (ℓ : Level) (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) (a0 : A0) (a1 : A1)
--                (base : BridgeP (λ x → primGel A0 A1 R x) a0 a1) (@tick j : BI) where

--   end : BridgeP (λ x → primGel A0 A1 R x) a0 a1
--   end = {!transp (λ _ → BridgeP (λ x → primGel A0 A1 R x) a0 a1) i0 base j!}


-- module Bug3 (ℓ : Level) (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) (a0 : A0) (a1 : A1)
--                (base : BridgeP (λ x → primGel A0 A1 R x) a0 a1)  where -- (@tick j : BI)

--   -- whnf (C-u C-u C-u C-n) the hole leads to impossible.
--   heyy : R a0 a1
--   heyy = {!prim^ungel λ j  → transp (λ _ → BridgeP (λ x → primGel A0 A1 R x) a0 a1) i0 base j!} 

-- -- λ j → transp (λ _ → BridgeP (λ x → primGel A0 A1 R x) a0 a1) i0 base j





{- JUNK 



    -- nativeness (must be stated dependently, and pointwise)
    -- "forall edge" formulation.
    -- mismatch with nativeness formulation for relators
    -- this is essentially nativeness of a section of (pr : Γ.A → Γ) relator
    -- tm-nativ : ∀ (γ0 γ1 : Γ .nrg-cr) (γγ : Γ ⦅ γ0 , γ1 ⦆ ) →
    --                PathP (λ _ → BridgeP (λ x → A .dcr (equivFun( Γ .nativ γ0 γ1  ) γγ x)) (ac0 γ0) (ac0 γ1))
    --                  (λ x → ac0 ((equivFun (Γ .nativ γ0 γ1) γγ) x) ) --use ac0
    --                  (equivFun (A .dnativ γ0 γ1 γγ (ac0 γ0) (ac0 γ1)) (ac1 γ0 γ1 γγ)) --use ac1

-- left-skew-tm-nativ : ∀ {ℓ ℓA} (Γ : NRGraph ℓ) (A : DispNRG ℓA Γ) (a : SectNRG Γ A) (γ0 γ1 : Γ .nrg-cr) (γγ : Γ ⦅ γ0 , γ1 ⦆ ) →
--   Path (A ⦅ ac0 a γ0 , ac0 a γ1 ⦆# γγ)
--     (a .ac1 γ0 γ1 γγ)
--     (invEq (A .dnativ γ0 γ1 γγ (a .ac0 γ0) (a .ac0 γ1)) λ x → a .ac0 ((equivFun (Γ .nativ γ0 γ1) γγ) x))
-- left-skew-tm-nativ Γ A a γ0 γ1 γγ =
--    invEq (equivAdjointEquiv (A .dnativ γ0 γ1 γγ (a .ac0 γ0) (a .ac0 γ1)) {a = a .ac1 γ0 γ1 γγ} {b = λ x → a .ac0 ((equivFun (Γ .nativ γ0 γ1) γγ) x)})
--      (sym (a .tm-nativ γ0 γ1 γγ))










-}
