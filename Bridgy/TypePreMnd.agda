{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce   #-} -- -v tc.meta.assign:45

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Bridgy.NRGRelRecord
open import Bridgy.TransportNativ
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using ( flip )
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Bridgy.MyPathToEquiv


-- Type premonads and a commutation principle, proved by hand
module Bridgy.TypePreMnd where

-- the Type → Type NRG.
TypeEndoNRG : (l : Level) → NRGraph (ℓ-suc l)
TypeEndoNRG l = record {
  nrg-cr = Type l → Type l ;
  nedge = λ M0 M1 → ∀ A0 A1 → (A0 → A1 → Type l) → M0 A0 → M1 A1 → Type l ;
  nativ = λ M0 M1 →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ A0 →
    equivΠCod λ A1 →
    equivΠ' relativity λ {AA Abdg} hypA →
    relativity) }

-- TypeEndoNRG l =
--   ΠNRG (TypeNRG l)
--   (record {
--     nobjMap = λ _ → Type l ;
--     nedgeMap = λ _ A0 A1 → (A0 → A1 → Type l) ;
--     nativ-rel = λ G0 G1 → funExt λ GG →
--      funExt λ A0 → funExt λ A1 → ua relativity   })





-- the ret dependent type, , as a displayed native reflexive graph.
-- => importantly, this includes a dependent bdg commutation pcpl for ret
-- M : Type l → Type l ⊧ ∀ A . A → M A  dNRG l+1
retTy : (l : Level) → DispNRG (ℓ-suc l) (TypeEndoNRG l)
retTy l = record {
  dcr = λ M → ∀ A → A → M A ;
  dedge = λ M0 M1 θ rm0 rm1 → 
    ∀ A0 A1 (AA : A0 → A1 → Type l) (a0 : A0) (a1 : A1) (aa : AA a0 a1) →
      θ A0 A1 AA (rm0 A0 a0) (rm1 A1 a1) ;
  dnativ = λ M0 M1 Mbdg rm0 rm1 →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ A0 →
    equivΠCod λ A1 →
    equivΠ' relativity λ {AA Abdg} hyp →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ a0 →
    equivΠCod λ a1 →
    equivΠ'
      (mypathToEquiv (flip _∙_ (cong (λ blank → BridgeP (λ x → blank x) a0 a1) hyp)
      (funExt⁻ (funExt⁻ (sym (retEq (relativity) AA)) a0) a1 )  ))
    λ {aa abdg} hypp →
    mypathToEquiv (change-line-path
      (λ x → Mbdg x (primGel A0 A1 AA x)) (λ x → Mbdg x (Abdg x))
      (rm0 A0 a0) (rm1 A1 a1) (rm0 A0 a0) (rm1 A1 a1)
      (λ x → cong (Mbdg x) (λ i → hyp i x))
      (transportRefl _) (transportRefl _)) )) }

-- the type of bind, as a displayed native reflexive graph.
-- (M : Type l → Type l) ⊧ ∀ A B . MA → (A → MB) → MB
-- importantly, this includes a dependent bdg commutation pcpl for bind
bindTy : (l : Level) → DispNRG (ℓ-suc l) (TypeEndoNRG l)
bindTy l = record {
  dcr = λ M → ∀ A B → (M A) → (A → M B) → M B ;
  dedge = λ M0 M1 MM bnd0 bnd1 →
    ∀ A0 A1 AA B0 B1 BB →
    ∀ ma0 ma1 (maa : MM A0 A1 AA ma0 ma1) →
    ∀ k0 k1 (kk : ∀ a0 a1 (aa : AA a0 a1) → (MM B0 B1 BB) (k0 a0) (k1 a1)) →
     MM B0 B1 BB (bnd0 A0 B0 ma0 k0) (bnd1 A1 B1 ma1 k1) ;
  dnativ = λ M0 M1 Mbdg bnd0 bnd1 →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ A0 → equivΠCod λ A1 →
    equivΠ' relativity λ {AA Abdg} hypA →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ B0 → equivΠCod λ B1 →
    equivΠ' relativity λ {BB Bbdg} hypB →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ ma0 → equivΠCod λ ma1 →
    equivΠ'
      (some-line-change M0 M1 Mbdg A0 A1 AA Abdg hypA ma0 ma1)
    λ {maa-bad maa} hyp-ma →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ k0 → equivΠCod λ k1 →
    equivΠ'
      (flip compEquiv ΠvsBridgeP
      (equivΠCod λ a0 → equivΠCod λ a1 →
      equivΠ'
        (appliedRelativityEquiv AA Abdg hypA a0 a1)
      λ {aa abdg} hypa →
      some-line-change M0 M1 Mbdg B0 B1 BB Bbdg hypB (k0 a0) (k1 a1)))
    λ {kk-bad kk} hypk →
    mypathToEquiv (change-line-path (λ x → Mbdg x (primGel B0 B1 BB x)) (λ x → Mbdg x (Bbdg x))
     (bnd0 A0 B0 ma0 k0) (bnd1 A1 B1 ma1 k1) (bnd0 A0 B0 ma0 k0) (bnd1 A1 B1 ma1 k1)
     (λ x → cong (Mbdg x) (λ k → hypB k x)) (transportRefl _) (transportRefl _)))))) }
-- technical note: at some point I had an error
-- 
-- "Cannot instantiate metavariable ... to solution ...
-- since it contains the variable ...
-- which is not in scope of the metavariable"
-- 
-- linked to
-- the use of equivΠ'. 
-- My solution was to provide the second argument of equivΠ' first, and come back the first later.

  where

    appliedRelativityEquiv : ∀ {A0 A1 : Type l}
      (AA : A0 → A1 → Type l) (Abdg : BridgeP (λ _ → Type l) A0 A1)
      (hypA : relativity .fst AA ≡ Abdg) (a0 : A0) (a1 : A1) →
      AA a0 a1 ≃ BridgeP (λ v → Abdg v) a0 a1
    appliedRelativityEquiv {A0 = A0} {A1 = A1} AA Abdg hypA a0 a1 =
      mypathToEquiv (sym (flip _∙_ (funExt⁻ (funExt⁻ (retEq relativity AA) a0) a1)
      (change-line-path (λ x → Abdg x) (λ x → primGel A0 A1 AA x) a0 a1 a0 a1 (λ x → λ j → hypA (~ j) x) (transportRefl _) (transportRefl _))))

    some-line-change :  ∀ (M0 M1 : Type l → Type l) (Mbdg : BridgeP (λ _ → Type l → Type l) M0 M1)
      (A0 A1 : Type l) (AA : A0 → A1 → Type l)  (Abdg : BridgeP (λ _ → Type l) A0 A1)
      (hypA : relativity .fst AA ≡ Abdg)
      (ma0 : M0 A0) (ma1 : M1 A1) →
      BridgeP (λ x → Mbdg x (primGel A0 A1 AA x)) ma0 ma1
        ≃
      BridgeP (λ x → Mbdg x (Abdg x)) ma0 ma1
    some-line-change M0 M1 Mbdg A0 A1 AA Abdg hypA ma0 ma1 =
      mypathToEquiv (change-line-path
      (λ x → Mbdg x (primGel A0 A1 AA x)) (λ x → Mbdg x (Abdg x))
      ma0 ma1 ma0 ma1 (λ x → cong (Mbdg x) (λ i → hypA i x)) (transportRefl _) (transportRefl _) )


module PackRetBind (l : Level) (Tret Tbnd : DispNRG (ℓ-suc l) (TypeEndoNRG l)) where

  record PreMnd : Type (ℓ-suc l) where
    field
      --action on types
      acty : TypeEndoNRG l .nrg-cr -- Type l → Type l
      --operations
      ret : Tret .dcr acty  -- ∀ A → A → M A
      bind : Tbnd .dcr acty -- ∀ A B → MA → (A → M B)
  open PreMnd public

  premnd-asΣ :
    (PreMnd)
    ≃
    ( Σ[ M ∈ (Type l → Type l) ] (Tret .dcr M × Tbnd .dcr M) )
  premnd-asΣ = isoToEquiv (iso
    (λ M → M .acty , M .ret , M .bind)
    (λ M → record { acty = M .fst ; ret = M .snd .fst ; bind = M .snd .snd })
    (λ _ → refl)
    λ _ → refl)

  -- type of logical relations btw 2 premonads M0 and M1
  record PreMndLrel (M0 M1 : PreMnd) : Type (ℓ-suc l) where
    field
      -- logical rel of type wrappers Type -> Type
      -- ∀ A0 A1 → (A0 → A1 → Type l) → M0 .acty A0 → M1 .acty A1 → Type l
      actyr : TypeEndoNRG l .nedge (M0 .acty) (M1 .acty)

      -- ret0 and ret1 must be related over actyr
      -- retr : ∀ A0 A1 (AA : A0 → A1 → Type l) (a0 : A0) (a1 : A1) (aa : AA a0 a1) → 
      --          actyr A0 A1 AA (M0 .ret a0) (M1 .ret a1)
      retr : Tret .dedge (M0 .acty) (M1 .acty) actyr (M0 .ret) (M1 .ret)

      -- -- same for bind
      -- bindr : ∀ A0 A1 AA B0 B1 BB → 
      --   ∀ ma0 ma1 (maa : actyr A0 A1 AA ma0 ma1) → --wrapped values are structurally related
      --   ∀ k0 k1 (kk : ∀ a0 a1 (aa : AA a0 a1) → (actyr B0 B1 BB) (k0 a0) (k1 a1)) → --continuations are pointwise related
      --   actyr B0 B1 BB (M0 .bind ma0 k0) (M1 .bind ma1 k1) --then their bind are related as well
      bindr : Tbnd .dedge (M0 .acty) (M1 .acty) actyr (M0 .bind) (M1 .bind)
  open PreMndLrel public


      

  record PreMndAuxBdg (M0 M1 : PreMnd) : Type (ℓ-suc l) where
    field
      actyb : BridgeP (λ _ → Type l → Type l) (M0 .acty) (M1 .acty)
      retb : BridgeP (λ x → Tret .dcr (actyb x)) (M0 .ret) (M1 .ret)
      bindb : BridgeP (λ x → Tbnd .dcr (actyb x)) (M0 .bind) (M1 .bind)
  open PreMndAuxBdg public

  PreMndAuxBdg≃BridgePreMnd : (M0 M1 : PreMnd) →
    PreMndAuxBdg M0 M1 ≃ BridgeP (λ _ → PreMnd) M0 M1
  PreMndAuxBdg≃BridgePreMnd M0 M1 = isoToEquiv (iso
    (λ recOfBdg → λ x → record {
      acty = recOfBdg .actyb x ;
      ret = recOfBdg .retb x ;
      bind = recOfBdg .bindb x })
    (λ Mbdg → record {
      actyb = λ x → Mbdg x .acty ;
      retb = λ x → Mbdg x .ret ;
      bindb = λ x → Mbdg x .bind })
    (λ _ → refl) λ _ → refl)

  PreMndAuxBdg≡ : ∀ {M0 M1 : PreMnd} (rv0 rv1 : PreMndAuxBdg M0 M1)
    (actybp : rv0 .actyb ≡ rv1 .actyb) → 
    (PathP (λ i → BridgeP (λ x → Tret .dcr (actybp i x)) (M0 .ret) (M1 .ret)) (rv0 .retb) (rv1 .retb)) →
    (PathP (λ i → BridgeP (λ x → Tbnd .dcr (actybp i x)) (M0 .bind) (M1 .bind)) (rv0 .bindb) (rv1 .bindb)) → 
    rv0 ≡ rv1
  PreMndAuxBdg≡ rv0 rv1 actybp retbp bindbp =
    λ i → record { actyb = actybp i ; retb = retbp i ; bindb = bindbp i }

  -- NRG structure for Σ [ M ∈  Ty → Ty] ret[M] × bind[M] 
  -- where ret, bind are abstract types (see module params)
  PreMndNRG-asΣ : NRGraph (ℓ-suc l)
  PreMndNRG-asΣ =  record {
    nrg-cr = Σ (TypeEndoNRG l .nrg-cr) (λ M →
             (Tret .dcr M) × Tbnd .dcr M) ;
    nedge = λ M0 M1 →
      let 
        M0acty = M0 .fst
        M0ret = M0 .snd .fst
        M0bnd = M0 .snd .snd
        M1acty = M1 .fst
        M1ret = M1 .snd .fst
        M1bnd = M1 .snd .snd
      in
        Σ (TypeEndoNRG l ⦅ M0acty , M1acty ⦆) (λ MM →
        (Tret .dedge M0acty M1acty MM M0ret M1ret) × Tbnd .dedge M0acty M1acty MM M0bnd M1bnd) ;
    nativ = λ M0 M1 →
      flip compEquiv ΣvsBridgeP
      (Σ-cong-equiv (TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) λ MM →
      flip compEquiv ×vsBridgeP
      (Σ-cong-equiv
        (flip compEquiv (Tret .dnativ (M0 .fst) (M1 .fst) (equivFun (TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) MM) (M0 .snd .fst) (M1 .snd .fst))
        (mypathToEquiv ( λ j → Tret .dedge (M0 .fst) (M1 .fst) (sym (retEq ( TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) MM) j) (M0 .snd .fst) (M1 .snd .fst))) )
      λ _ →
      flip compEquiv (Tbnd .dnativ (M0 .fst) (M1 .fst) (equivFun (TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) MM) (M0 .snd .snd) (M1 .snd .snd))
      ((mypathToEquiv ( λ j → Tbnd .dedge (M0 .fst) (M1 .fst) (sym (retEq ( TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) MM) j) (M0 .snd .snd) (M1 .snd .snd)))))) }

  -- no nativ
  PreMndRGraph : RGraph (ℓ-suc l)
  PreMndRGraph = record {
    rg-cr = PreMnd ;
    redge = λ M0 M1 → PreMndLrel M0 M1 }

  PreMndRGraph-asΣ : RGraph (ℓ-suc l)
  PreMndRGraph-asΣ = record {
    rg-cr = PreMndNRG-asΣ .nrg-cr ;
    redge = PreMndNRG-asΣ .nedge }

  PreMndRGraphISOPreMndRGraph-asΣ : RGraph≅ PreMndRGraph PreMndRGraph-asΣ
  PreMndRGraphISOPreMndRGraph-asΣ = record {
    rg-cr≅ = premnd-asΣ ;
    redge≅ = λ M0 Msig0 hypM0 M1 Msig1 hypM1 → isoToEquiv (iso
      {!λ MM → ?!} {!!} {!!} {!!}) }




  hey : Unit
  hey = {!transpNativ PreMndRGraph PreMndRGraph-asΣ!}



-- sym (retEq ( TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)) MM)
-- λ j → Tret .dedge (M0 .fst) (M1 .fst)
-- TypeEndoNRG l .nativ (M0 .fst) (M1 .fst)

      
-- -- whats a bridge at PreMnd? we can either start by transforming
-- -- PreMnd into a Sigma (see thm below), or have a custom thm making bridge
-- -- commute with the record type former. Bridge commutation for records can not
-- -- be stated generally as records are not first-class.


-- record PreMndRecOfBdg {l : Level} (M0 M1 : PreMnd l) : Type (ℓ-suc l) where
--   field
--     actyb : BridgeP (λ _ → Type l → Type l) (M0 .acty) (M1 .acty)
--     retb : BridgeP (λ x → ∀ A → A → (actyb x) A) (λ A → M0 .ret {A = A}) (λ A → M1 .ret {A = A})
--     bindb : BridgeP (λ x → ∀ A B → (actyb x) A → (A → (actyb x) B) → (actyb x) B)
--                     (λ A B → M0 .bind {A = A} {B = B}) λ A B → M1 .bind {A = A} {B = B}
-- open PreMndRecOfBdg




-- -- -- make Bridge and the record type former for PreMnd commute
-- BridgeVsPreMndRecord : {l : Level} (M0 M1 : PreMnd l) →
--   PreMndRecOfBdg M0 M1 ≃ BridgeP (λ _ → PreMnd l) M0 M1
-- BridgeVsPreMndRecord M0 M1 = isoToEquiv (iso
--   (λ recMbdg x → record {
--     acty = recMbdg .actyb x ;
--     ret = λ {_} → recMbdg .retb x _  ;
--     bind = λ {_ _} → recMbdg .bindb x _ _ })
--   (λ q → record {
--     actyb = λ x → q x .acty ;
--     retb = λ x A → q x .ret {A = A} ;
--     bindb = λ x A B → q x .bind {A = A} {B = B} })
--   (λ q → refl)
--   λ recMbdg → refl)






-- JUNK

-- since ret and bind depend on the acty term, they have a dependent bdg commutation pcpl
-- encapsulated in the retTy and bindTy displayed NRGs defined above.

-- PreMndLrelEquivPreMndRecOfBdg : {l : Level} (M0 M1 : PreMnd l) →
--   PreMndLrel M0 M1 ≃ PreMndRecOfBdg M0 M1
-- PreMndLrelEquivPreMndRecOfBdg M0 M1 = isoToEquiv (iso
--   (λ θ → record {
--     actyb = ΠBridgeP λ A0 A1 AA → equivFun relativity (θ .actyr _ _ (invEq relativity AA)) ;
--     retb = ΠBridgeP λ A0 A1 AA → ΠBridgeP λ a0 a1 aa →
--       transport (funExt⁻ (funExt⁻
--           (sym (retEq (relativity {A0 = M0 .acty A0} {A1 = M1 .acty A1}) (θ .actyr A0 A1 (BridgeP (λ x₁ → AA x₁)))))
--           (M0 .ret {A = A0} a0)) (M1 .ret {A = A1} a1))
--       ( (θ .retr A0 A1 (invEq relativity AA) a0 a1 aa)) ;
--     bindb = ΠBridgeP λ A0 A1 AA → ΠBridgeP λ B0 B1 BB → 
--       ΠBridgeP λ ma0 ma1 maa → ΠBridgeP λ k0 k1 kk →
--       transport (funExt⁻ (funExt⁻
--         (sym (retEq (relativity {A0 = M0 .acty B0} {A1 = M1 .acty B1}) (θ .actyr B0 B1 (BridgeP (λ x₁ → BB x₁)))))
--         (bind M0 ma0 k0)) (bind M1 ma1 k1))
--       (θ .bindr A0 A1 (invEq relativity AA) B0 B1 (invEq relativity BB) ma0 ma1
--         (transport (funExt⁻ (funExt⁻ (retEq (relativity {A0 = M0 .acty A0} {A1 = M1 .acty A1}) (θ .actyr A0 A1 (BridgeP (λ x₁ → AA x₁)))) ma0) ma1) maa)
--       k0 k1 λ a0 a1 aa →
--         transport (funExt⁻ (funExt⁻ (retEq (relativity {A0 = M0 .acty B0} {A1 = M1 .acty B1}) (θ .actyr B0 B1 (BridgeP (λ x₁ → BB x₁)))) (k0 a0)) (k1 a1))
--         (invEq ΠvsBridgeP kk a0 a1 aa))
--       })
--   (λ sbdg → record {
--     actyr = λ A0 A1 AA → invEq relativity (invEq ΠvsBridgeP (sbdg .actyb) A0 A1 (equivFun relativity AA)) ;
--     retr = λ A0 A1 AA a0 a1 aa →
--       invEq ΠvsBridgeP (invEq ΠvsBridgeP (sbdg .retb) A0 A1 (equivFun relativity AA)) a0 a1
--       (transport (funExt⁻ (funExt⁻ (sym (retEq (relativity {A0 = A0} {A1 = A1}) AA)) a0) a1) aa) ;
--     bindr = λ A0 A1 AA B0 B1 BB ma0 ma1 maa k0 k1 kk →
--       invEq ΠvsBridgeP (invEq ΠvsBridgeP (invEq ΠvsBridgeP (invEq ΠvsBridgeP (sbdg .bindb) A0 A1 (equivFun relativity AA)) B0 B1 (equivFun relativity BB)) ma0 ma1
--       maa)
--       k0 k1
--       (ΠBridgeP λ a0 a1 aa → kk a0 a1 (transport (funExt⁻ (funExt⁻ (retEq relativity AA) a0) a1) aa )) })
--   (λ sbdg → PreMndRecOfBdg≡ _ _
--     ( invEq ( PathPvsBridgeP _)
--       λ x → funExt λ A → {!
--         primExtent {B = λ y → !})
--     {!!}
--     {!!})
--   {!!})




-- mhocom {ζ = (i0 m∨ x =bi0) ∨∨ (i0 m∨ x =bi1) ∨∨ (i m∨ bno)} (prim^mpor ((i0 m∨ x =bi0) ∨∨ (i0 m∨ x =bi1)) (i m∨ bno) (λ _ → u0) (λ _ → u0))

-- sm-mhfill : {ℓ : Level} {A : Type ℓ} (@tick x : BI) (u0 : A) →
--   mhocom {ζ = (i0 m∨ x =bi0) ∨∨ (i0 m∨ x =bi1)} (λ _ _ → u0) u0 ≡ u0
-- sm-mhfill x u0 = λ i →
--   mhocom {ζ = (i0 m∨ x =bi0) ∨∨ (i0 m∨ x =bi1) ∨∨ (i m∨ bno)}
--     (λ j → λ { (x = bi0) → u0
--                ; (x = bi1) → u0
--                ; (i = i1) → u0})
--     u0
