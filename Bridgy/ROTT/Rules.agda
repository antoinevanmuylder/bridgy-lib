{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.ROTT.Rules where


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


------------------------------------------------------------------------
-- lemmas

funExt2⁻ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → A → I → Type ℓ'}
  {f : (x y : A) → B x y i0} {g : (x y : A) → B x y i1} →
  (x y : A) →
  PathP (λ i → (x y : A) → B x y i) f g →
  PathP (B x y) (f x y) (g x y)
funExt2⁻ x y eq = λ i → eq i x y


------------------------------------------------------------------------
-- Some NRGs


topNRG : NRGraph ℓ-zero
topNRG .nrg-cr = Unit
topNRG .nedge  = (λ _ _ → Unit)
topNRG .nativ  = (λ where tt tt → topBdgDiscrEquiv)

-- -- Type with -logical- relations is a native reflexive graph
-- -- this is proved using relativity
TypeNRG : ∀ (ℓ : Level) → NRGraph (ℓ-suc ℓ)
TypeNRG ℓ .nrg-cr = Type ℓ
TypeNRG ℓ .nedge  = λ A0 A1 → (A0 → A1 → Type ℓ)
TypeNRG ℓ .nativ  = λ A0 A1 → relativity



-- -- nRG has binary products
_×NRG_ : ∀{ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) → NRGraph (ℓ-max ℓG ℓH)
_×NRG_ G H .nrg-cr = G .nrg-cr × H .nrg-cr
_×NRG_ G H .nedge (g0 , h0) (g1 , h1)  = G .nedge g0 g1 × H .nedge h0 h1
_×NRG_ G H .nativ  (g0 , h0) (g1 , h1) = flip compEquiv ×vsBridgeP (≃-× (G .nativ g0 g1) (H .nativ h0 h1))

-- NRG closed under →
_→NRG_ : ∀{ℓG ℓH} (G : NRGraph ℓG) (H : NRGraph ℓH) → NRGraph (ℓ-max ℓG ℓH)
_→NRG_ G H .nrg-cr = G .nrg-cr → H .nrg-cr
_→NRG_ G H .nedge = λ f0 f1 → ∀ g0 g1 (gg : G ⦅ g0 , g1 ⦆ ) → H .nedge (f0 g0) (f1 g1)
_→NRG_ G H .nativ = λ f0 f1 → flip compEquiv ΠvsBridgeP
  (equivΠCod λ g0 → equivΠCod λ g1 →
  equivΠ' (G .nativ _ _) λ _ → H .nativ _ _)


trivNRG : ∀ {l} (A : Type l) → NRGraph l
trivNRG A =
  record {
    nrg-cr = A ;
    nedge = Bridge A ;
    nativ = λ a0 a1 → idEquiv _ }


------------------------------------------------------------------------
-- Some native relators

idNrel : ∀ {l} (Γ : NRGraph l) → NRelator Γ Γ
idNrel Γ .nrel0 g = g
idNrel Γ .nrel1 g0 g1 gg = gg
idNrel Γ .nativ-rel g0 g1 gg gbdg gprf = gprf

compNrel : ∀ {lG lH lK} {G : NRGraph lG} (H : NRGraph lH) {K : NRGraph lK}
  (F1 : NRelator G H) (F2 : NRelator H K) → NRelator G K
compNrel {G = G} H {K = K} F1 F2 .nrel0 g = F2 .nrel0 (F1 .nrel0 g)
compNrel {G = G} H {K = K} F1 F2 .nrel1 g0 g1 gg = F2 .nrel1 _ _ (F1 .nrel1 _ _ gg)
compNrel {G = G} H {K = K} F1 F2 .nativ-rel g0 g1 gg gbdg gprf =
  F2 .nativ-rel (F1 .nrel0 g0) (F1 .nrel0 g1) (F1 .nrel1 _ _ gg) (λ x → F1 .nrel0 (gbdg x))
  (F1 .nativ-rel g0 g1 gg gbdg gprf)


------------------------------------------------------------------------
------------------------------------------------------------------------
-- Rules of ROTT



------------------------------------------------------------------------
-- ~structural

-- Γ ctx
-- Γ ⊢ A type
-- ----------
-- Γ.A ctx
_#_ : ∀ {ℓ ℓ'} (Γ : NRGraph ℓ) (A : DispNRG ℓ' Γ) → NRGraph (ℓ-max ℓ ℓ')
_#_ Γ A .nrg-cr = Σ (Γ .nrg-cr) (A .dcr)
_#_ Γ A .nedge (g0 , a0) (g1 , a1) = Σ (Γ ⦅ g0 , g1 ⦆) (λ gg → A ⦅ a0 , a1 ⦆# gg)
_#_ Γ A .nativ (g0 , a0) (g1 , a1) =
  flip compEquiv ΣvsBridgeP
  (Σ-cong-equiv-2ary _ _ _ _ (Γ .nativ g0 g1)
   λ gg gbdg gprf → A .dnativ g0 g1 gg gbdg gprf a0 a1)

infixl 40 _#_

module Nativ-#-Lemmas where

  -- Having nativeness phrased in a 2ary fashion
  -- creates the need for the following lemmas (not trivial)

  nativ-#-split : ∀ {lΓ lA} (Γ : NRGraph lΓ) (A : DispNRG lA Γ)
    (g0 g1 : Γ .nrg-cr) (gg : Γ ⦅ g0 , g1 ⦆ ) (gbdg : Bridge (Γ .nrg-cr) g0 g1) (gprf : gg [ Γ .nativ g0 g1 ] gbdg) →
    (a0 : A .dcr g0) (a1 : A .dcr g1) (aa : A ⦅ a0 , a1 ⦆# gg) (abdg : BridgeP (λ x → A .dcr (gbdg x)) a0 a1) (aprf : aa [ A .dnativ g0 g1 gg gbdg gprf a0 a1 ] abdg ) →
    (gg , aa) [ (Γ # A) .nativ (g0 , a0) (g1 , a1) ] (λ x → gbdg x , abdg x)
  nativ-#-split Γ A g0 g1 gg gbdg gprf a0 a1 aa abdg aprf =
    compGr _ ΣvsBridgeP (gg , aa) (gbdg , abdg) (λ x → gbdg x , abdg x)
    (inEquGr (ΣPathP (outEquGr gprf ,
      change-pathp-endpoints refl (outEquGr aprf)
      λ i x → A .dnativ g0 g1 gg (outEquGr gprf i) (to-gprf i) a0 a1 .fst aa x)))
    (inEquGr refl)

    where

      aux1 = change-line-pathp (λ i → Γ .nativ g0 g1 .fst gg ≡ outEquGr gprf i) (λ i → gg [ Γ .nativ g0 g1 ] (outEquGr gprf i))
             refl (outEquGr gprf)
             (λ i hyp → inEquGr hyp)

      to-gprf : PathP (λ i → gg [ Γ .nativ g0 g1 ] (outEquGr gprf i)) (inEquGr refl) gprf
      to-gprf =
        change-pathp-endpoints refl (inOfOut gprf) (aux1
        λ i j → outEquGr gprf (i ∧ j))

  nativ-#-proj1 : ∀ {lΓ lA} (Γ : NRGraph lΓ) (A : DispNRG lA Γ)
    (g0 g1 : Γ .nrg-cr) (gg : Γ ⦅ g0 , g1 ⦆ ) (gbdg : Bridge (Γ .nrg-cr) g0 g1)
    (a0 : A .dcr g0) (a1 : A .dcr g1) (aa : A ⦅ a0 , a1 ⦆# gg) (abdg : BridgeP (λ x → A .dcr (gbdg x)) a0 a1) → 
    (gg , aa) [ (Γ # A) .nativ (g0 , a0) (g1 , a1) ] (λ x → gbdg x , abdg x) → 
    gg [ Γ .nativ g0 g1 ] gbdg
  nativ-#-proj1 Γ A g0 g1 gg gbdg a0 a1 aa abdg gaprf =
    inEquGr λ i x → outEquGr gaprf i x .fst

  nativ-#-proj2 : ∀ {lΓ lA} (Γ : NRGraph lΓ) (A : DispNRG lA Γ)
    (g0 g1 : Γ .nrg-cr) (gg : Γ ⦅ g0 , g1 ⦆ ) (gbdg : Bridge (Γ .nrg-cr) g0 g1)
    (a0 : A .dcr g0) (a1 : A .dcr g1) (aa : A ⦅ a0 , a1 ⦆# gg) (abdg : BridgeP (λ x → A .dcr (gbdg x)) a0 a1) → 
    (gaprf : (gg , aa) [ (Γ # A) .nativ (g0 , a0) (g1 , a1) ] (λ x → gbdg x , abdg x)) → 
    aa [ A .dnativ g0 g1 gg gbdg (nativ-#-proj1 Γ A g0 g1 gg gbdg a0 a1 aa abdg gaprf) a0 a1 ] abdg
  nativ-#-proj2 Γ A g0 g1 gg gbdg a0 a1 aa abdg gaprf =
    inEquGr
    (change-pathp-endpoints refl (fromPathP gaprf-extract-snd)
    (sym (fromPathP {A = (λ i → BridgeP (λ x → A .dcr (gaprf-extract i .fst x)) a0 a1)}
    λ i → A .dnativ g0 g1 gg (gaprf-extract-fst i) (inEquGr (to-gprf i)) a0 a1 .fst aa)))

    where

      gaprf-extract : Path (Σ (Bridge (Γ .nrg-cr) g0 g1) (λ q → BridgeP (λ x → A .dcr (q x)) a0 a1)) _ _
      gaprf-extract = λ i → invEq ΣvsBridgeP (outEquGr gaprf i)

      gaprf-extract-fst : Path (Bridge (Γ .nrg-cr) g0 g1) (Γ .nativ g0 g1 .fst gg) gbdg
      gaprf-extract-fst = PathPΣ gaprf-extract .fst

      gaprf-extract-snd : PathP
        (λ i → BridgeP (λ x → A .dcr (gaprf-extract-fst i x)) a0 a1)
        (A .dnativ g0 g1 gg (Γ .nativ g0 g1 .fst gg) (inEquGr refl) a0 a1 .fst aa)
        abdg
      gaprf-extract-snd = λ i → gaprf-extract i .snd

      to-gprf : PathP (λ i → Γ .nativ g0 g1 .fst gg ≡ gaprf-extract-fst i) refl (λ i x → outEquGr gaprf i x .fst)
      to-gprf = λ i j x → outEquGr gaprf (i ∧ j) x .fst



open Nativ-#-Lemmas public
  


-- Γ NRG     A NRG
-- ---------------
-- Γ ⊨ A dNRG
todNRG : ∀ {lΓ lA} (Γ : NRGraph lΓ) →
  NRGraph lA → DispNRG lA Γ
todNRG Γ A .dcr γ = A .nrg-cr
todNRG Γ A .dedge g0 g1 gg a0 a1 = A .nedge a0 a1
todNRG Γ A .dnativ g0 g1 gg gbdg gprf a0 a1 = A .nativ a0 a1


-- (Γ), X:Type l  ⊨ X dNRG (l)
lastType : ∀ {lΓ l : Level} {Γ : NRGraph lΓ} → DispNRG l (Γ # todNRG Γ (TypeNRG l))
lastType {Γ = Γ}  .dcr (g , X) = X
lastType {Γ = Γ} .dedge (g0 , X0) (g1 , X1) (gg , XX) = XX
lastType {Γ = Γ} .dnativ (g0 , X0) (g1 , X1) (gg , XX) gXbdg gXprf x0 x1 =
  mypathToEquiv (funExt⁻ (funExt⁻ (outEquGrInv aux) x0) x1)

  where

    aux = nativ-#-proj2 Γ (todNRG Γ (TypeNRG _)) g0 g1 gg (λ z → gXbdg z .fst) X0 X1 XX (λ z → gXbdg z .snd) gXprf


-- Ty subst
-- σ : Γ → Δ    Δ ⊢ A type
-- ------------------------
-- Γ ⊢ A type
tySubst : ∀ {ℓΓ ℓΔ ℓ} (Γ : NRGraph ℓΓ) (Δ : NRGraph ℓΔ) →
            (NRelator Γ Δ) → (DispNRG ℓ Δ) → 
            DispNRG ℓ Γ
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dcr g = A .dcr ( σ .nrel0 g )
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dedge g0 g1 gg = A .dedge (σ .nrel0 g0) (σ .nrel0 g1) (σ .nrel1 _ _ gg) 
tySubst {ℓΔ = ℓΔ} Γ Δ σ A .dnativ g0 g1 gg gbdg gprf a0 a1 =
  A .dnativ (σ .nrel0 g0) (σ .nrel0 g1) (σ .nrel1 _ _ gg) (λ x → σ .nrel0 (gbdg x))
  (σ .nativ-rel _ _ gg gbdg gprf)
  a0 a1

-- proj : Γ.A → Γ
pr : ∀ {l} {Γ : NRGraph l} (lA : Level) (A : DispNRG lA Γ) →
  NRelator (Γ # A) Γ
pr lA A .nrel0 (g , _) = g
pr lA A .nrel1 (g0 , a0) (g1 , a1) (gg , aa) = gg
pr lA A .nativ-rel (g0 , a0) (g1 , a1) gaa gabdg gaprf
  = inEquGr λ i x → outEquGr gaprf i x .fst


-- weakening
-- Γ ⊢ A type
-- Γ ⊢ W type
-- ----------
-- Γ.W ⊢ A type
wkn : ∀ {lΓ lA lW} {Γ : NRGraph lΓ} {W : DispNRG lW Γ} (A : DispNRG lA Γ) →
  DispNRG lA (Γ # W)
wkn {Γ = Γ} {W = W} A =
  tySubst (Γ # W) Γ (pr _ W) A



-- variable rule (last variable)
-- Γ NRG     Γ ⊨ A dNRG
-- ---------------------
-- Γ , X : A ⊨ X : A
var0 : ∀ {l lA} → (Γ : NRGraph l) → (A : DispNRG lA Γ) → TermDNRG (Γ # A) (wkn A)
var0 Γ A =
  record {
    tm0 = λ ga → ga .snd;
    tm1 = λ ga0 ga1 gaa → gaa .snd ;
    tm-nativ = λ ga0 ga1 gaa gaBdg gaPrf →
      nativ-#-proj2 Γ A (ga0 .fst) (ga1 .fst) (gaa .fst) (λ x → gaBdg x .fst) (ga0 .snd) (ga1 .snd) (gaa .snd) (λ x → gaBdg x .snd) gaPrf
    }


-- variable-like rule (essentially not stateable in normal type thy)
-- Γ NRG     Γ ⊨ A dNRG
-- ---------------------
-- (g : Γ) , a : A ⊨ g : todNRG(Γ)
var1-ctx : ∀ {l lA} → (Γ : NRGraph l) → (A : DispNRG lA Γ) →
  TermDNRG (Γ # A) (todNRG (Γ # A) Γ)
var1-ctx Γ A =
  record {
    tm0 = λ ga → ga .fst ;
    tm1 = λ ga0 ga1 gaa → gaa .fst ;
    tm-nativ = λ ga0 ga1 gaa gaBdg gaPrf →
      nativ-#-proj1 Γ A (ga0 .fst) (ga1 .fst) (gaa .fst) (λ x → gaBdg x .fst) (ga0 .snd) (ga1 .snd) (gaa .snd) (λ x → gaBdg x .snd) gaPrf
  }


-- last last variable.
-- Γ NRG   Γ ⊨ A dNRG  (Γ # A) ⊨ B dNRG
-- -------------------------------------
-- Γ , (a : A) , (b : B) ⊨ a : A
var1 : ∀ {l lA lB} {Γ : NRGraph l} →
  (A : DispNRG lA Γ) (B : DispNRG lB (Γ # A)) →
  TermDNRG (Γ # A # B) (wkn (wkn A))
var1 {Γ = Γ} A B =
  record {
    tm0 = λ gab → gab .fst .snd ;
    tm1 = λ gab0 gab1 gabb → gabb .fst .snd ;
    tm-nativ = λ gab0 gab1 gabb gabBdg gabPrf →
    let
      np1 : gabb .fst [ (Γ # A) .nativ (gab0 .fst) (gab1 .fst) ] (λ x → gabBdg x .fst)
      np1 = nativ-#-proj1 (Γ # A) B (gab0 .fst) (gab1 .fst) (gabb .fst) (λ x → gabBdg x .fst) (gab0 .snd) (gab1 .snd) (gabb .snd) (λ x → gabBdg x .snd) gabPrf in
    nativ-#-proj2 Γ A
      (gab0 .fst .fst) (gab1 .fst .fst) (gabb .fst .fst) (λ x → gabBdg x .fst .fst)
      (gab0 .fst .snd) (gab1 .fst .snd) (gabb .fst .snd) (λ x → gabBdg x .fst .snd)
      np1
  }






------------------------------------------------------------------------
-- type formers


-- Γ ⊢ A type   Γ ⊢ B type
-- ------------------------
-- Γ ⊢ A → B type
→Form : ∀ {ℓ} {Γ : NRGraph ℓ} (lA : Level) (lB : Level)
   (A : DispNRG lA Γ) (B : DispNRG lB Γ) → 
  DispNRG (ℓ-max lA lB) Γ
→Form lA lB A B .dcr g = (A .dcr g) → (B .dcr g)
→Form lA lB A B .dedge g0 g1 gg f0 f1 = ∀ a0 a1 → A ⦅ a0 , a1 ⦆# gg → B ⦅ f0 a0 , f1 a1 ⦆# gg
→Form lA lB A B .dnativ g0 g1 gg gbdg gprf f0 f1 =
  flip compEquiv ΠvsBridgeP
  (equivΠCod λ a0 → equivΠCod λ a1 →
  equivΠ' (A .dnativ g0 g1 gg gbdg gprf a0 a1) λ {aa} {abdg} aprf →
  B .dnativ g0 g1 gg gbdg gprf (f0 a0) (f1 a1) )



-- Γ ⊢ A type   Γ ⊢ B type
-- ------------------------
-- Γ ⊢ A × B type
×Form : ∀ {ℓ} {Γ : NRGraph ℓ} (lA : Level) (lB : Level)
   (A : DispNRG lA Γ) (B : DispNRG lB Γ) → 
  DispNRG (ℓ-max lA lB) Γ
×Form lA lB A B =
  record {
    dcr = λ g → A .dcr g × B .dcr g ;
    dedge = λ g0 g1 gg ab0 ab1 → (A .dedge g0 g1 gg (ab0 .fst) (ab1 .fst)) × (B .dedge g0 g1 gg (ab0 .snd) (ab1 .snd)) ;
    dnativ = λ g0 g1 gg gbdg gprf ab0 ab1 →
      flip compEquiv (ΣvsBridgeP)
      (≃-×
        (A .dnativ g0 g1 gg gbdg gprf (ab0 .fst) (ab1 .fst))
        (B .dnativ g0 g1 gg gbdg gprf (ab0 .snd) (ab1 .snd)))
    }

-- Theres a difference btw this and simply U ∈ NRG. 
--
-- -----------------
-- Γ ⊢ U(l) type(l+1)
UForm : ∀ {l} {Γ : NRGraph l} (lU : Level) → DispNRG (ℓ-suc lU) Γ
UForm lU .dcr _ = Type lU
UForm lU .dedge _ _ _ A0 A1 = A0 → A1 → Type lU
UForm lU .dnativ _ _ _ _ _ A0 A1 = relativity


-- Formation rule for the El type
--
-- Γ ⊢ C : U(lC)
-- -----------------
-- Γ ⊢ El C  type(lC)
El : ∀ {l} {Γ : NRGraph l} {lC} → TermDNRG Γ (UForm lC) → DispNRG lC Γ
El c .dcr g = c .tm0 g
El c .dedge g0 g1 gg c0 c1 = c .tm1 g0 g1 gg c0 c1
-- c .tm-nativ gives a ≡, displayed nativeness asks for a ≃.
El c .dnativ g0 g1 gg gbdg gprf c0 c1 =
  let z = (outEquGrInv (c .tm-nativ g0 g1 gg gbdg gprf)) in
  mypathToEquiv (funExt⁻ (funExt⁻ z c0) c1)

X⊨ElX : ∀ {l : Level} → DispNRG l (TypeNRG l)
X⊨ElX {l} = El (record {
  tm0 = λ X → X ;
  tm1 = λ X0 X1 XX → XX ;
  tm-nativ = λ X0 X1 XX Xbdg Xprf → Xprf})

-- X : Type ⊨ A dNRG
-- ------------------
-- X:Type, a:A ⊨ ElX dNRG
X,stuff⊨ElX : ∀ {l lA : Level} → (A : DispNRG lA (TypeNRG l)) → DispNRG l (TypeNRG l # A)
X,stuff⊨ElX A .dcr (X , a) = X
X,stuff⊨ElX A .dedge (X0 , a0) (X1 , a1) (XX , aa) = XX
X,stuff⊨ElX A .dnativ (X0 , a0) (X1 , a1) (XX , aa) Xabdg Xaprf x0 x1 =
  mypathToEquiv (funExt⁻ (funExt⁻ (outEquGrInv aux) x0) x1)

  where

    aux : XX [ relativity ] (λ x → Xabdg x .fst)
    aux = nativ-#-proj1 (TypeNRG _) A X0 X1 XX (λ x → Xabdg x .fst) a0 a1 aa (λ x → Xabdg x .snd) Xaprf

module ΣΠForm {ℓΓ ℓA ℓB} {Γ : NRGraph ℓΓ} (A : DispNRG ℓA Γ) (B : DispNRG ℓB (Γ # A)) where

  -- Γ ⊢ A type
  -- Γ . A ⊢ B type
  -- --------------
  -- Γ ⊢ Σ A B type
  ΣForm : DispNRG (ℓ-max ℓA ℓB) Γ
  ΣForm .dcr g = Σ[ a ∈ A .dcr g ] B .dcr (g , a)
  ΣForm .dedge g0 g1 gg (a0 , b0) (a1 , b1) =
    Σ[ aa ∈ A .dedge g0 g1 gg a0 a1 ] B .dedge (g0 , a0) (g1 , a1) (gg , aa) b0 b1
  ΣForm .dnativ g0 g1 gg gbdg gprf (a0 , b0) (a1 , b1) =
    flip compEquiv ΣvsBridgeP
    (Σ-cong-equiv-2ary _ _ _ _ (A .dnativ g0 g1 gg gbdg gprf a0 a1) λ aa abdg aprf →
    B .dnativ (g0 , a0) (g1 , a1) (gg , aa) (λ x → gbdg x , abdg x)
    (nativ-#-split Γ A g0 g1 gg gbdg gprf a0 a1 aa abdg aprf)
    b0 b1)
  
  -- When nativeness was phrased 1ary (there was no need for nativ-#-split)
  -- ΣForm =
  --   record {
  --     dcr = λ γ → Σ (A .dcr γ) (λ a → B .dcr (γ , a))  ;
  --     dedge = λ γ0 γ1 γγ ab0 ab1 →  Σ (A .dedge γ0 γ1 γγ (ab0 .fst) (ab1 .fst)) (λ aa → B .dedge (γ0 , ab0 .fst) (γ1 , ab1 .fst) ( (γγ , aa)) (ab0 .snd) (ab1 .snd)) ;
  --     dnativ = λ { γ0 γ1 γbdg (a0 , b0) (a1 , b1) →
  --       flip compEquiv ΣvsBridgeP (invEquiv
  --       (Σ-cong-equiv (invEquiv (A .dnativ _ _ γbdg a0 a1 )) λ abdg →
  --       invEquiv (B .dnativ (γ0 , a0) (γ1 , a1) (λ x → (γbdg x , abdg x )) b0 b1) )) }
  --   }

  -- -- Γ ⊢ A type
  -- -- Γ.A ⊢ B type
  -- -- --------------
  -- -- Γ ⊢ Π A B type
  ΠForm : DispNRG (ℓ-max ℓA ℓB) Γ
  ΠForm .dcr g = (a : A .dcr g) → B .dcr (g , a)
  ΠForm .dedge g0 g1 gg f0 f1 = ∀ a0 a1 (aa : A ⦅ a0 , a1 ⦆# gg) → B ⦅ f0 a0 , f1 a1 ⦆# (gg , aa)
  ΠForm .dnativ g0 g1 gg gbdg gprf f0 f1 =
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ a0 → equivΠCod λ a1 →
    equivΠ' (A .dnativ g0 g1 gg gbdg gprf a0 a1)
    λ {aa abdg} aprf → 
      B .dnativ (g0 , a0) (g1 , a1) (gg , aa) (λ x → gbdg x , abdg x)
      (nativ-#-split Γ A g0 g1 gg gbdg gprf a0 a1 aa abdg (inEquGr aprf))
      (f0 a0) (f1 a1))

  -- When nativeness was phrased 1ary (there was no need for nativ-#-split)
  -- ΠForm = record {
  --   dcr = λ γ → ∀ (a : A .dcr γ) → B .dcr (γ , a) ;
  --   dedge = λ γ0 γ1 γγ f0 f1 → ∀ (a0 : A .dcr γ0) (a1 : A .dcr γ1) (aa : A ⦅ a0 , a1 ⦆# γγ ) → B ⦅ f0 a0 , f1 a1 ⦆# (γγ , aa) ;
  --   dnativ = λ γ0 γ1 γbdg f0 f1 →
  --     flip compEquiv ΠvsBridgeP
  --     (equivΠCod λ a0 →
  --     equivΠCod λ a1 → invEquiv
  --     (equivΠ (invEquiv (A .dnativ _ _ γbdg a0 a1)) λ abdg →
  --     (invEquiv (B .dnativ (γ0 , a0) (γ1 , a1) (λ x → (γbdg x , abdg x)) (f0 a0) (f1 a1))) ) )
  --   }
open ΣΠForm public


-- Path type former in ROTT
-- Γ ⊨ A dNRG
-- Γ ⊨ a : A    Γ ⊨ b : A 
-- ------------------------
-- Γ ⊨ a ≡ b dNRG
≡Form : ∀ {l lA} → (Γ : NRGraph l) (A : DispNRG lA Γ) →
  (a : TermDNRG Γ A) (b : TermDNRG Γ A) →
  DispNRG lA Γ
≡Form Γ A a b = record {
  dcr = λ g → (a .tm0 g) ≡ (b .tm0 g) ;
  -- a logical relation between paths is a path between logical relations
  dedge = λ g0 g1 gg ab0 ab1 → PathP (λ i → A ⦅ ab0 i , ab1 i ⦆# gg) (a .tm1 g0 g1 gg) (b .tm1 g0 g1 gg) ;
  dnativ = λ g0 g1 gg gbdg gprf ab0 ab1 →
    flip compEquiv (PathPvsBridgeP (λ x i → A .dcr (gbdg x)) {left = ab0} {right = ab1} {down = λ x → a .tm0 (gbdg x)} {up = λ x → b .tm0 (gbdg x)})
    (compEquiv (congPathEquiv (λ i → A .dnativ g0 g1 gg gbdg gprf (ab0 i) (ab1 i)) {a₀ = a .tm1 g0 g1 gg} {a₁ = b .tm1 g0 g1 gg})
    let anativ = outEquGr (a .tm-nativ g0 g1 gg gbdg gprf) in
    let bnativ = outEquGr (b .tm-nativ g0 g1 gg gbdg gprf) in
    mypathToEquiv λ i → PathP (λ i → BridgeP (λ x → A .dcr (gbdg x)) (ab0 i) (ab1 i)) (anativ i) (bnativ i))
  }



------------------------------------------------------------------------
-- for terms


-- app rule
-- Γ ⊨ f : A → B      Γ ⊨ a : A
-- -------------------------------
-- Γ ⊨ f a : B
app : ∀ {l lA lB} →
  (Γ : NRGraph l) (A : DispNRG lA Γ) (B : DispNRG lB Γ) 
  (f : TermDNRG Γ (→Form _ _ A B))
  (a : TermDNRG Γ A) →
  TermDNRG Γ B
app Γ A B f a =
  record {
    tm0 = λ g → f .tm0 g (a .tm0 g) ;
    tm1 = λ g0 g1 gg →  f .tm1 g0 g1 gg (a .tm0 g0) (a .tm0 g1) (a .tm1 g0 g1 gg) ;
    tm-nativ = λ g0 g1 gg gbdg gprf →
      let thingf = outEquGrInv (f .tm-nativ g0 g1 gg gbdg gprf) in
      let thingf2 = funExt⁻ {f = f .tm1 g0 g1 gg} thingf (a .tm0 g0) in
      let thingf3 = funExt⁻ {f = tm1 f g0 g1 gg (a .tm0 g0)} thingf2 (a .tm0 g1) in
      let thingf4 = funExt⁻ {f = tm1 f g0 g1 gg (a .tm0 g0) (a .tm0 g1)} thingf3 (a .tm1 g0 g1 gg) in
      inEquGrInv (thingf4 ∙
         cong (invEq (B .dnativ g0 g1 gg gbdg gprf (f .tm0 g0 (a .tm0 g0)) (f .tm0 g1 (a .tm0 g1))))
         let thing-a = outEquGr (a .tm-nativ g0 g1 gg gbdg gprf) in
         λ i x → f .tm0 (gbdg x) (thing-a i x))
  }



-- double app
-- Γ ⊨ f : X → Y → Z
-- Γ ⊨ x : X         Γ ⊨ y : Y
-- ---------------------------
-- Γ ⊨ f x y : Z
app2 : ∀ {l lX lY lZ} {Γ : NRGraph l} →
  {X : DispNRG lX Γ} {Y : DispNRG lY Γ} {Z : DispNRG lZ Γ}
  (f : TermDNRG Γ (→Form _ _ X (→Form _ _ Y Z)))
  (x : TermDNRG Γ X) (y : TermDNRG Γ Y) →
  TermDNRG Γ Z
app2 {Γ = Γ} {X = X} {Y = Y} {Z = Z} f x y = app Γ Y Z (app Γ X (→Form _ _ Y Z) f x) y


-- Γ.A ⊨ b : B
-- -----------------λ
-- Γ ⊨ λ(b) : Π A B
lamm : ∀ {lΓ lA lB : Level}
  {Γ : NRGraph lΓ} → (A : DispNRG lA Γ) (B : DispNRG lB (Γ # A)) →
  (b : TermDNRG (Γ # A) B) →
  TermDNRG Γ (ΠForm A B)
lamm A B b = record {
  tm0 = λ g a → b .tm0 (g , a) ;
  tm1 = λ g0 g1 gg a0 a1 aa → b .tm1 (g0 , a0) (g1 , a1) (gg , aa)  ;
  tm-nativ = λ g0 g1 gg gbdg gprf →
    inEquGrInv
    (funExt λ a0 → funExt λ a1 → funExt λ aa →
    outEquGrInv (b .tm-nativ (g0 , a0) (g1 , a1) (gg , aa)  (λ x → gbdg x , equivFun (A .dnativ g0 g1 gg gbdg gprf a0 a1) aa x)
    (nativ-#-split _ A g0 g1 gg gbdg gprf a0 a1 aa (equivFun (A .dnativ g0 g1 gg gbdg gprf a0 a1) aa)
    (inEquGr refl))))
  }

-- Γ ⊨ A dNRG
-- -----------
-- Γ ⊨ code A : U
code : ∀ {l} {Γ : NRGraph l} {lC} → DispNRG lC Γ → TermDNRG Γ (UForm lC)
code A =
  record {
    tm0 = λ g → A .dcr g ;
    tm1 = λ g0 g1 gg a0 a1 → A .dedge g0 g1 gg a0 a1 ;
    tm-nativ = λ g0 g1 gg gbdg gprf →
      inEquGrInv (funExt λ a0 → funExt λ a1 → ua (A .dnativ g0 g1 gg gbdg gprf a0 a1))
  }



------------------------------------------------------------------------
-- Bridge discrete types


-- A (closed) bridge discrete type gives rise to a dNRG.
--
-- isBDisc (A : Type l)
-- --------------------
-- Γ ⊢ A dNRG (use paths as edges)
bDisc-asDNRG : ∀ {lΓ lA} {Γ : NRGraph lΓ} (A : Type lA) (bd : isBDisc A) → DispNRG lA Γ
bDisc-asDNRG A bd .dcr _ = A
bDisc-asDNRG A bd .dedge g0 g1 gg a0 a1 = a0 ≡ a1
bDisc-asDNRG A bd .dnativ g0 g1 gg gbdg gprf a0 a1 = isBDisc→equiv A bd a0 a1

-- A, B bridge-discrete, B does not depend on Γ.
-- ---------------------------------------------
-- Γ # A ⊨ B dNRG
bDiscP-asDNRG : ∀ {lΓ lA lB} (Γ : NRGraph lΓ)
  (A : Type lA) (bdA : isBDisc A)
  (B : A → Type lB) (bdB : isBDiscP A bdA B) → 
  DispNRG lB (Γ # (bDisc-asDNRG A bdA))
bDiscP-asDNRG Γ A bdA B bdB .dcr (g , a) = B a
bDiscP-asDNRG Γ A bdA B bdB .dedge (g0 , a0) (g1 , a1) (gg , aa) b0 b1 = PathP (λ i → B (aa i)) b0 b1
bDiscP-asDNRG Γ A bdA B bdB .dnativ (g0 , a0) (g1 , a1) (gg , aa) gbdg gprf b0 b1 =
  bdB a0 a1 b0 b1 aa (λ x → gbdg x .snd)
  (nativ-#-proj2 Γ (bDisc-asDNRG A bdA) g0 g1 gg (λ x → gbdg x .fst) a0 a1 aa (λ x → gbdg x .snd)
  gprf)





-- A (closed) bridge discrete type gives rise to an NRG
-- isBDIsc (A : Type l)
-- --------------------
-- A  NRG
bDisc-asNRG : ∀ {l} (A : Type l) (bd : isBDisc A) → NRGraph l
bDisc-asNRG A bd .nrg-cr = A
bDisc-asNRG A bd .nedge a0 a1 = (a0 ≡ a1)
bDisc-asNRG A bd .nativ a0 a1 = isBDisc→equiv A bd a0 a1

-- A dependently bridge-discrete type B over a closed bridge-discrete type A
-- gives rise to a dNRG.
-- isBDisc (A : Type lA)       isBDiscP A bdA (B : A → Type lB)
-- -------------------------------------------------------------
-- A ⊨ B dNRG
bDiscP-asDNRG' : ∀ {lA lB} (A : Type lA) (bdA : isBDisc A) (B : A → Type lB) (bdB : isBDiscP A bdA B) → DispNRG lB (bDisc-asNRG A bdA)
bDiscP-asDNRG' A bdA B bdB .dcr = B
bDiscP-asDNRG' A bdA B bdB .dedge a0 a1 aa b0 b1 = PathP (λ i → B (aa i)) b0 b1
bDiscP-asDNRG' A bdA B bdB .dnativ a0 a1 aa abdg aprf b0 b1 = bdB a0 a1 b0 b1 aa abdg aprf






------------------------------------------------------------------------
-- X:Type ⊨ List X dNRG

ListdNRG : ∀ {l} → DispNRG l (TypeNRG l)
ListdNRG .dcr X = List X
ListdNRG .dedge X0 X1 XX = [List XX ] --action of List on relations.
ListdNRG .dnativ X0 X1 XX Xbdg Xprf as0 as1 =
  flip compEquiv (ListvsBridgeP Xbdg)
  (ntvUnderList (help-ntv) as0 as1)

  where

    help-ntv : ∀ hd0 hd1 → XX hd0 hd1 ≃ BridgeP (λ x → Xbdg x) hd0 hd1
    help-ntv hd0 hd1 = mypathToEquiv (funExt⁻ (funExt⁻ (outEquGrInv Xprf) hd0) hd1)

    ntvUnderList : (∀ hd0 hd1 → XX hd0 hd1 ≃ BridgeP (λ x → Xbdg x) hd0 hd1) →
      ∀ as0 as1 → [List XX ] as0 as1 ≃ [List (BridgeP (λ x → Xbdg x))] as0 as1
    ntvUnderList hyp [] [] = idEquiv _
    ntvUnderList hyp [] (hd1 ∷ tl1) = idEquiv _
    ntvUnderList hyp (hd0 ∷ tl0) [] = idEquiv _
    ntvUnderList hyp (hd0 ∷ tl0) (hd1 ∷ tl1) = Σ-cong-equiv (hyp hd0 hd1)
      λ _ → ntvUnderList hyp tl0 tl1


-- Γ ⊨ Z dNRG
-- ---------------
-- Γ ⊨ List Z dNRG
ListdNRG' : ∀ {l lz} {Γ : NRGraph l} → 
  DispNRG lz Γ → DispNRG lz Γ
ListdNRG' {Γ = Γ} Z =
  record {
    dcr = λ g → List (Z .dcr g) ;
    dedge = λ g0 g1 gg zs0 zs1 → ListRCover (Z .dedge g0 g1 gg) zs0 zs1 ;
    dnativ = λ g0 g1 gg gbdg gprf zs0 zs1 → --uses ua. possible to povide equiv directly instead
      flip compEquiv (ListvsBridgeP (λ x → Z .dcr (gbdg x)))
      (mypathToEquiv
      let
         eqrel : (Z .dedge g0 g1 gg) ≡ BridgeP (λ x → Z .dcr (gbdg x))
         eqrel = (funExt λ z0 → funExt λ z1 → ua (Z .dnativ g0 g1 gg gbdg gprf z0 z1))
      in
      λ i → ListRCover (eqrel i) zs0 zs1)
  }


------------------------------------------------------------------------
-- Nat

-- Γ ⊨ Nat dNRG
NatForm : ∀ {l} {Γ : NRGraph l} → DispNRG ℓ-zero Γ
NatForm = record {
  dcr = λ _ → ℕ ;
  dedge = λ _ _ _ → codeℕ ;
  dnativ = λ _ _ _ _ _ → SRP-Nat
  }

-- Γ ⊨ z : Nat
zeroTerm : ∀ {l} {Γ : NRGraph l} →  TermDNRG Γ NatForm
zeroTerm = record {
  tm0 = λ g → zero ;
  tm1 = λ _ _ _ → tt ;
  tm-nativ = λ _ _ _ _ _ → inEquGr refl
  }


-- n natural number of agda bridges
-- ----------------
-- Γ ⊨ n : Nat
cstNatTerm :  ∀ {l} {Γ : NRGraph l} → ℕ → TermDNRG Γ NatForm
cstNatTerm n = record {
  tm0 = λ g → n ;
  tm1 = λ _ _ _ → codeℕrefl n ;
  tm-nativ = λ _ _ _ _ _ →
    inEquGrInv (isOfHLevelRespectEquiv 1 (≡ℕ≃Codeℕ n n) (isSetℕ n n) _ _)
  }

-- Γ ⊨ suc : Nat → Nat
sucTerm  : ∀ {l} {Γ : NRGraph l} → TermDNRG Γ  (→Form _ _ NatForm NatForm)
sucTerm = record {
  tm0 = λ _ n → suc n ;
  tm1 = λ _ _ _ → λ n0 n1 nn → nn ;
  tm-nativ = λ _ _ _ _ _ →
    inEquGrInv (funExt λ n0 → funExt λ n1 → funExt λ nn →
    let isPropCode = isOfHLevelRespectEquiv 1 (≡ℕ≃Codeℕ n0 n1) (isSetℕ n0 n1) in
    isPropCode _ _)
  }

-- Γ , n ⊨ suc n : Nat
-- in practice the one above is preferable because this one can only be used through term substitution
-- which is a meta theoretical operation
sucTerm'  : ∀ {l} {Γ : NRGraph l} → TermDNRG (Γ # NatForm) NatForm
sucTerm' = record {
  tm0 = λ gn → suc (gn .snd) ;
  tm1 = λ gn0 gn1 gnn → gnn .snd;
  tm-nativ =
    λ gn0 gn1 gnn gnbdg gnprf →
    -- we use the fact that Nat is a set.
    -- didn't think how to prove it otherwise
    let isPropCode = isOfHLevelRespectEquiv 1 (≡ℕ≃Codeℕ (gn0 .snd) (gn1 .snd)) (isSetℕ (gn0 .snd) (gn1 .snd))
    in inEquGrInv (isPropCode _ _)
  }


------------------------------------------------------------------------
-- Γ ⊨ Bool dNRG
BoolForm : ∀ {l} {Γ : NRGraph l} → DispNRG ℓ-zero Γ
BoolForm = record {
  dcr = λ _ → Bool ;
  dedge = λ _ _ _ → Bool~ ;
  dnativ = λ _ _ _ _ _ → SRP-Bool
  }


-- Γ ⊨ true, false : Bool
boolCons : Bool → ∀ {l} {Γ : NRGraph l} → TermDNRG Γ (BoolForm)
boolCons true = record {
  tm0 = λ _ → true ;
  tm1 = λ _ _ _ → tt ;
  tm-nativ = λ _ _ _ _ _ → inEquGrInv refl}
boolCons false = record {
  tm0 = λ _ → false ;
  tm1 = λ _ _ _ → tt ;
  tm-nativ = λ _ _ _ _ _ → inEquGrInv refl}
