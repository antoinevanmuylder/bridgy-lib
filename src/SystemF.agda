{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce --type-in-type  --allow-unsolved-metas #-} -- --no-termination-check
module SystemF where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
-- open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.FinData.Base as FIN
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_ ; idfun ; flip)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import BridgePrims
open import BridgeExamples
open import ExtentExamples
open import GelExamples
open import NativeReflGraphRelator
open import SimpleParam

{-
In this file we devise (at first) a shallow embedding of systemF types.
More precisely, impredicative systemF is interpreted into the current metalanguage (or rather open types map to native relators, cf  `⟦_⟧kjudg`).
Since systemF pi types `∀` map to agda --bridges pi types, the resulting model is provably parametric (cf ParamNativeRelator.agda).
For this intepretation to be sound and to avoid giving a complex model we assume the Type in Type inconsistency.
I believe that, in a similar fashion, predicative systemF can be given a parametric semantics into the current meta language, but without Type:Type ofc.
Experiments showed that building such a model without cumulativity is cumbersome. Cumulativity seems not compatible with agda --cubical.
-}


module _ where

  it : ∀ {a} {A : Set a} → {{A}} → A
  it {{x}} = x


module FSyntax where

  FKCtx = ℕ


  -- a sysF type with n free type variables
  -- intent: FKjudg Θ = { A  |  Θ ⊢ A : * }
  data FKjudg (Θ : FKCtx) : Type where
    Ftyvar : Fin Θ → FKjudg Θ
    _⟶_ : FKjudg Θ → FKjudg Θ → FKjudg Θ
    F∀ : FKjudg (suc Θ) → FKjudg Θ

  -- a typing context = a vector of well kinded types
  FTypCtx : FKCtx → ℕ → Type
  FTypCtx Θ = Vec (FKjudg Θ)

open FSyntax


-- ⟦ Θ ⟧ = Type × ... × Type : Type
⟦_⟧kctx : FKCtx → Type
⟦_⟧kctx 0 = ⊤
⟦_⟧kctx (suc Θ) = Type × ⟦ Θ ⟧kctx

⟦_⟧kctxhasNRG₀ : (Θ : FKCtx) → HasNRGraph ⟦ Θ ⟧kctx
⟦_⟧kctxhasNRG₀ 0 = it
⟦_⟧kctxhasNRG₀ (suc Θ) = prodHasNRG ⦃ hnrgH = ⟦ Θ ⟧kctxhasNRG₀ ⦄

instance 
  ⟦_⟧kctxhasNRG : {Θ : FKCtx} → HasNRGraph ⟦ Θ ⟧kctx
  ⟦_⟧kctxhasNRG {Θ} = ⟦ Θ ⟧kctxhasNRG₀


-- interpretation of type variables.
⟦Ftyvar⟧ : ∀ (Θ : FKCtx) → Fin Θ → NRelator ⟦ Θ ⟧kctx Type
⟦Ftyvar⟧ 0 k = (⊥.rec (¬Fin0 k)) -- in empty ctx, no well kinded type is derived using Ftyvar rule.
⟦Ftyvar⟧ (suc Θ) zero = record { nobjMap = λ { ( A , _ )  → A }    -- first projection
                               ; nedgeMap = λ { ( R , _ ) → R } 
                               ; nativ-rel = λ where ( A0 , _ ) ( A1 , _ ) → refl }
⟦Ftyvar⟧ (suc Θ) (suc k) = record { nobjMap = λ { ( _ , θ ) →  ⟦Ftyvar⟧ Θ k .nobjMap θ } -- projecting the rest by induction
                                  ; nedgeMap = λ { ( _ , Rθ ) → ⟦Ftyvar⟧ Θ k .nedgeMap Rθ }
                                  ; nativ-rel = λ { ( _ , θ0 ) ( _ , θ1 ) → funExt λ q →
                                            funExt⁻ (⟦Ftyvar⟧ Θ k .nativ-rel θ0 θ1) (λ x → snd ( q x )) } }

-- interpretation of the kinding judgment.
-- Well kinded open types are interpreted as native relators
⟦_⟧kjudg : ∀ {Θ} → FKjudg Θ → NRelator ⟦ Θ ⟧kctx Type
⟦_⟧kjudg {Θ} (Ftyvar k) = ⟦Ftyvar⟧ Θ k
⟦_⟧kjudg (τ ⟶ τ') = record { nobjMap =  λ A → ⟦ τ ⟧kjudg .nobjMap A → ⟦ τ' ⟧kjudg .nobjMap A --interpreting arrow open types.
                            ; nedgeMap = λ AA f0 f1 → ∀ a0 a1 → ⟦ τ ⟧kjudg .nedgeMap AA a0 a1 → ⟦ τ' ⟧kjudg .nedgeMap AA (f0 a0) (f1 a1)
                            ; nativ-rel = λ A0 A1 → funExt λ q → funExt λ f0 → funExt λ f1 →
                                ua (flip compEquiv ΠvsBridgeP
                                (equivΠCod λ a0 → equivΠCod λ a1 →
                                equiv→ ( pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (⟦ τ ⟧kjudg .nativ-rel A0 A1) q) a0) a1) )
                                        (pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (⟦ τ' ⟧kjudg .nativ-rel A0 A1) q) (f0 a0)) (f1 a1))))) }
⟦_⟧kjudg (F∀ τ) = record { nobjMap = λ θ → ∀ (α : Type) → ⟦ τ ⟧kjudg .nobjMap ( α , θ )
                         -- In fact, all of the above dependent functions Λ α → bla are parametric thanks to ambient parametricity
                         -- below: map related types α0 α1 to related incarnations (f0 α0) (f1 α1)
                         ; nedgeMap = λ θθ f0 f1 → ∀ α0 α1 αα → ⟦ τ ⟧kjudg .nedgeMap (αα , θθ) (f0 α0) (f1 α1)
                         ; nativ-rel = λ θ0 θ1 → funExt λ θθ → funExt λ f0 → funExt λ f1 →
                             ua (flip compEquiv ΠvsBridgeP
                             (equivΠCod λ A0 → equivΠCod λ A1 →
                             equivΠ (invEquiv relativity)
                             λ AA → flip compEquiv
                               (pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (⟦ τ ⟧kjudg .nativ-rel (A0 , θ0) (A1 , θ1)) (λ x → (to-bridge AA x , θθ x))) (f0 A0)) (f1 A1)))
                               (pathToEquiv (cong (λ blank → ⟦ τ ⟧kjudg .nedgeMap (blank , _) (f0 A0) (f1 A1)) (sym (rel-retract AA)) )) )) }


-- interpretation of typing contexts. A typing ctx Γ = {Γj|j} over kinding context Θ is the product-relator ⟦ Γ1 ⟧kjudg × ...
-- where Γj is the jth well kinded type in Γ.
-- ⟦ x1 : Γ1 , ... , xm : Γm ⟧ =    θ ↦ ⟦ Γ1 ⟧ θ × ... × ⟦ Γm ⟧ θ
⟦_⟧typctx : ∀ {m} {Θ : FKCtx} → FTypCtx Θ m → NRelator ⟦ Θ ⟧kctx Type
⟦_⟧typctx [] = record { nobjMap = λ _ → ⊤
                      ; nedgeMap = λ _ _ _ → ⊤
                      ; nativ-rel = λ A0 A1 → funExt λ q → funExt λ where tt → funExt λ where tt → ua topBdgDiscrEquiv }
⟦_⟧typctx (τ ∷ Γ) = record { nobjMap = λ A → (⟦ τ ⟧kjudg .nobjMap A) × ⟦ Γ ⟧typctx .nobjMap A
                           ; nedgeMap = λ AA → λ { ( τA0 , ΓA0 ) ( τA1 , ΓA1 ) →  ⟦ τ ⟧kjudg .nedgeMap AA τA0 τA1 × ⟦ Γ ⟧typctx .nedgeMap AA ΓA0 ΓA1 }  
                           ; nativ-rel = λ A0 A1 → funExt λ AA →   funExt λ { (τA0 , ΓA0) → funExt λ { (τA1 , ΓA1) →
                               ua (flip compEquiv ×vsBridgeP
                               (isoToEquiv (prodIso 
                                 (equivToIso ( pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (⟦ τ ⟧kjudg .nativ-rel A0 A1) AA) τA0) τA1)))
                                 ( equivToIso ( pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (⟦ Γ ⟧typctx .nativ-rel A0 A1) AA) ΓA0) ΓA1)) )))) } } }


-- instance res is slow here somehow
-- ParamTransf : ∀ {m} (Θ : FKCtx) (Γ : FTypCtx Θ m) → FKjudg Θ → NRelator ⟦ Θ ⟧kctx Type
-- ParamTransf Θ Γ τ =  compNRelator ⟨ ⟦ Γ ⟧typctx , ⟦ τ ⟧kjudg ⟩nrel arrowNRelator


-- semantic typing judgment SemTypJudg Θ Γ τ, denoted Θ|Γ ⊧ _ : τ
-- intent: Θ | Γ ⊧ t : τ iff ⟦ t ⟧term : SemTypJudg Θ Γ τ (⟦_⟧term is missing for now)
-- Formally we would have ⟦_⟧typjudg : ∀ Θ Γ τ →  (Θ|Γ ⊢ _ : τ) → (Θ|Γ ⊧ _ : τ) for the interpr of terms
-- where (Θ|Γ ⊢ _ : τ) = FTypJudg Θ Γ τ
-- in other words denotations of terms would live in SemTypJudg Θ Γ τ
-- Remark that λA. ⟦Γ⟧A → ⟦τ⟧A is a native relator.
-- parametricity of sysF means exactly param for this native relator.
SemTypJudg : ∀ {m} (Θ : FKCtx) (Γ : FTypCtx Θ m) → FKjudg Θ → Type
SemTypJudg Θ Γ τ = ∀ (A : ⟦ Θ ⟧kctx) → ⟦ Γ ⟧typctx .nobjMap A → ⟦ τ ⟧kjudg .nobjMap A

-- α:* | a:α ⊧ _ : a
semOpenChurchUnit : Type
semOpenChurchUnit = SemTypJudg 1 (Ftyvar zero  ∷ []) (Ftyvar zero)

semOpenPolymidAlone' : semOpenChurchUnit ≃ ∀ (X : Type) → X → X
semOpenPolymidAlone' = equivΠ (Σ-contractSnd λ _ → isContrUnit )
                          λ where ( A , tt ) → equiv→ (Σ-contractSnd (λ _ → isContrUnit)) (idEquiv _)

semOpenPolymidAlone : semOpenChurchUnit ≃ ⊤
semOpenPolymidAlone = compEquiv semOpenPolymidAlone' churchUnit


-- closed church unit type
FChurchUnit : FKjudg 0
FChurchUnit = F∀ (Ftyvar zero ⟶ Ftyvar zero)

-- ∅|∅ ⊧ _ : ∀α.α→α
semChurchUnit : Type
semChurchUnit = SemTypJudg 0 [] FChurchUnit

semPolymidAlone' : semChurchUnit ≃ ∀ (X : Type) → X → X
semPolymidAlone' = isoToEquiv (iso
                     (λ t → t tt tt)
                     (λ t → λ _ _ → t)
                     (λ _ → refl) (λ _ → refl))

semPolymidAlone : semChurchUnit ≃ ⊤
semPolymidAlone = compEquiv semPolymidAlone' churchUnit




{- TERMS

  -- Let σ be a permutation. if  Θ ⊢ τ THEN  σ ↷ Θ ⊢ τ 
  -- We go for all permutations because proof for head-transpositions Θ , ℓ₂ , ℓ₁ ⊢ Θ , ℓ₁ , ℓ₂
  -- require other kinds of permutations.
  module AdmissibleExchangeType where

    Perm : FKCtx → Type
    Perm Θ = Iso (Fin Θ) (Fin Θ)

    substTensorId : ∀ {Θ} → Perm Θ → Perm (suc Θ)
    substTensorId σ = iso
                        (λ {zero → zero ; (suc k) → suc (Iso.fun σ k)})
                        (λ {zero → zero ; (suc k) → suc (Iso.inv σ k)})
                        (λ {zero → refl ; (suc k) → cong suc (Iso.rightInv σ k)})
                        λ {zero → refl ; (suc k) → cong suc (Iso.leftInv σ k)}

    exchRule : ∀ {Θ} (σ : Perm Θ) → FKjudg Θ → FKjudg Θ
    exchRule σ (Ftyvar k) = Ftyvar (Iso.fun σ k)
    exchRule σ (τ ⟶ τ') = exchRule σ τ ⟶ exchRule σ τ'
    exchRule σ (F∀ τ) = F∀ (exchRule (substTensorId σ) τ)

    -- perm for head exchange
    hExchPerm : ∀ {Θ} → Perm (suc (suc Θ))
    hExchPerm = iso
                  (λ {zero → suc zero ; (suc zero) → zero ; (suc (suc k)) → suc (suc k)})
                  (λ {zero → suc zero ; (suc zero) → zero ; (suc (suc k)) → suc (suc k)})
                  (λ {zero → refl ; (suc zero) → refl ; (suc (suc k)) → refl })
                  (λ {zero → refl ; (suc zero) → refl ; (suc (suc k)) → refl })

    -- head exchange rule for well kinded types
    hExch : ∀ {Θ} → FKjudg (suc (suc Θ)) → FKjudg (suc (suc Θ))
    hExch τ = exchRule hExchPerm τ
  open AdmissibleExchangeType
  

  -- "head" weakening of types/typing contexts
  wknType : ∀ {Θ} → FKjudg Θ → FKjudg (suc Θ)
  wknType (Ftyvar k) = Ftyvar (weakenFin k)
  wknType (τ ⟶ τ') = (wknType τ) ⟶ (wknType τ')
  wknType (F∀ τ) = F∀ (wknType τ)

  wknTypCtx : ∀ {m} {Θ : FKCtx} → FTypCtx Θ m → FTypCtx (suc Θ) m
  wknTypCtx = λ Γ → map wknType Γ
  
  substType : ∀ {Θ} → FKjudg (suc Θ) → FKjudg Θ → FKjudg Θ
  substType (Ftyvar zero) = idfun _
  substType (Ftyvar (suc k)) = λ _ → Ftyvar k
  substType (τ ⟶ τ') = λ A → substType τ A ⟶ substType τ' A 
  substType (F∀ τ) = λ A → F∀ (substType (hExch τ) (wknType A)) -- termination checker not happy here

  data FTypJudg : ∀ {m} (Θ : FKCtx) (Γ : FTypCtx Θ m) → FKjudg Θ → Type where
    Fvar :  ∀ {m} {Θ : FKCtx} {Γ : FTypCtx Θ m} →
              (i : Fin m) → FTypJudg Θ Γ (lookup i Γ)
    Fλ : ∀ {m} {Θ : FKCtx} {Γ : FTypCtx Θ m} →
         {A B : FKjudg Θ} →
           -- Θ | Γ , x:A ⊢ e : B  THEN  Θ | Γ ⊢ λx.e : A → B
           FTypJudg Θ ( A ∷ Γ ) B → FTypJudg Θ Γ (A ⟶ B)
    _Fof_ : ∀ {m} {Θ : FKCtx} {Γ : FTypCtx Θ m} →
             {A B : FKjudg Θ} →
               -- Θ|Γ⊢ f :A→B AND Θ|Γ⊢ a:A THEN Θ|Γ ⊢ fa:B
               FTypJudg Θ Γ (A ⟶ B) → FTypJudg Θ Γ A → FTypJudg Θ Γ B
    FΛ : ∀ {m} {Θ : FKCtx} {Γ : FTypCtx Θ m} {τ : FKjudg (suc Θ)}  →
        (FTypJudg (suc Θ) (wknTypCtx Γ) τ)   →   FTypJudg Θ Γ (F∀ τ)
    _Fat_ : ∀ {m} {Θ : FKCtx} {Γ : FTypCtx Θ m} {τ : FKjudg (suc Θ)} →
               FTypJudg Θ Γ (F∀ τ) → (opand : FKjudg Θ) → FTypJudg Θ Γ (substType τ opand)

-}

---------------------
{- Reordering the parts.

   Andreas: All the parts of the proofs are there, but the use of native relators as opposed to an object and a relational interpretation
   may make the theorem superficially hard to recognize.
-}

-- object interpretation of the kinding judgment (type of well-kinded System F types).
⟦_⟧kjudgₒ : ∀ {Θ} → FKjudg Θ → ⟦ Θ ⟧kctx → Type
⟦ τ ⟧kjudgₒ = nobjMap ⟦ τ ⟧kjudg

-- object interpretation of typing contexts.
⟦_⟧typctxₒ : ∀ {m} {Θ : FKCtx} → FTypCtx Θ m → ⟦ Θ ⟧kctx → Type
⟦ Γ ⟧typctxₒ = nobjMap ⟦ Γ ⟧typctx

-- relational interpretation of the kinding judgment (type of well-kinded System F types).
⟦_⟧kjudgᵣ : ∀ {Θ} → (τ : FKjudg Θ) → {θ0 θ1 : ⟦ Θ ⟧kctx} → (θR : nedge θ0 θ1) → ⟦ τ ⟧kjudgₒ θ0 → ⟦ τ ⟧kjudgₒ θ1 → Type
⟦ τ ⟧kjudgᵣ {θ0} {θ1} θR t0 t1 = nedgeMap ⟦ τ ⟧kjudg θR t0 t1

-- relational interpretation of typing contexts.
⟦_⟧typctxᵣ : ∀ {m} {Θ : FKCtx} → (Γ : FTypCtx Θ m) → {θ0 θ1 : ⟦ Θ ⟧kctx} → (θR : nedge θ0 θ1) → ⟦ Γ ⟧typctxₒ θ0 → ⟦ Γ ⟧typctxₒ θ1 → Type
⟦ Γ ⟧typctxᵣ {θ0} {θ1} θR γ0 γ1 = nedgeMap ⟦ Γ ⟧typctx θR γ0 γ1

-- I suspect the following two functions can come in handy also in the semantics of ∀.
nativP' : ∀ {ℓ} {A : Type ℓ} {{hnrgA : HasNRGraph A}} (B : NRelator A Type) {a1 a2 : A} (a* : BridgeP (λ _ → A) a1 a2) (b1 : nobjMap B a1) (b2 : nobjMap B a2) → nedgeMap B (invEq (nativ a1 a2) a*) b1 b2 ≃ BridgeP (λ i → nobjMap B (a* i)) b1 b2
nativP' {ℓ} {A} {{hnrgA}} B {a1} {a2} a* b1 b2 = pathToEquiv (funExt⁻ (funExt⁻ (funExt⁻ (nativ-rel B a1 a2) a*) b1) b2)

nativP : ∀ {ℓ} {A : Type ℓ} {{hnrgA : HasNRGraph A}} (B : NRelator A Type) {a1 a2 : A} (aR : nedge a1 a2) (b1 : nobjMap B a1) (b2 : nobjMap B a2) → nedgeMap B aR b1 b2 ≃ BridgeP (λ i → nobjMap B (equivFun (nativ a1 a2) aR i)) b1 b2
nativP B aR b1 b2 = pathToEquiv {!via nativP' and inversion of (nativ a1 a2)!}

-- reflexivity (parametricity)
param-refl : ∀ {m} {Θ : FKCtx} → (Γ : FTypCtx Θ m) (τ : FKjudg Θ)
  → (t : (θ : ⟦ Θ ⟧kctx) → ⟦ Γ ⟧typctxₒ θ → ⟦ τ ⟧kjudgₒ θ)
  → {θ0 θ1 : ⟦ Θ ⟧kctx} → (θR : nedge θ0 θ1) → {γ0 : ⟦ Γ ⟧typctxₒ θ0} {γ1 : ⟦ Γ ⟧typctxₒ θ1} (γR : ⟦ Γ ⟧typctxᵣ θR γ0 γ1) → ⟦ τ ⟧kjudgᵣ θR (t θ0 γ0) (t θ1 γ1)
param-refl {m} {Θ} Γ τ t {θ0} {θ1} θR {γ0} {γ1} γR = tR
  where θ* : BridgeP (λ _ → ⟦ Θ ⟧kctx) θ0 θ1
        θ* = equivFun (nativ θ0 θ1) θR
        γ* : BridgeP (λ i → ⟦ Γ ⟧typctxₒ (θ* i)) γ0 γ1
        γ* = equivFun (nativP ⟦ Γ ⟧typctx θR γ0 γ1) γR
        t* : BridgeP (λ i → ⟦ τ ⟧kjudgₒ (θ* i)) (t θ0 γ0) (t θ1 γ1)
        t* i = (t (θ* i) (γ* i))
        tR : ⟦ τ ⟧kjudgᵣ θR (t θ0 γ0) (t θ1 γ1)
        tR = invEq (nativP ⟦ τ ⟧kjudg θR (t θ0 γ0) (t θ1 γ1)) t*

refl-edge : ∀{ℓ} {A : Type ℓ} {{hnrgA : HasNRGraph A}} → (a : A) → nedge a a
refl-edge a = invEq (nativ a a) λ _ → a

-- Maybe this is easier:
-- reflexivity (parametricity), but for a reflexive edge in Θ
-- Never mind.
param-refl' : ∀ {m} {Θ : FKCtx} → (Γ : FTypCtx Θ m) (τ : FKjudg Θ)
  → (t : (θ : ⟦ Θ ⟧kctx) → ⟦ Γ ⟧typctxₒ θ → ⟦ τ ⟧kjudgₒ θ)
  → (θ : ⟦ Θ ⟧kctx) → {γ0 : ⟦ Γ ⟧typctxₒ θ} {γ1 : ⟦ Γ ⟧typctxₒ θ} (γR : ⟦ Γ ⟧typctxᵣ (refl-edge θ) γ0 γ1) → ⟦ τ ⟧kjudgᵣ (refl-edge θ) (t θ γ0) (t θ γ1)
param-refl' {m} {Θ} Γ τ t θ {γ0} {γ1} γR = tR
  where γ* : BridgeP (λ _ → ⟦ Γ ⟧typctxₒ θ) γ0 γ1
        γ* = equivFun {!nativP ⟦ Γ ⟧typctx ? {!γ0!} {!γ1!}!} γR -- Works up to cancellation of inverses
        t* : BridgeP (λ _ → ⟦ τ ⟧kjudgₒ θ) (t θ γ0) (t θ γ1)
        t* i = (t θ (γ* i))
        tR : ⟦ τ ⟧kjudgᵣ (refl-edge θ) (t θ γ0) (t θ γ1)
        tR = invEq (nativP ⟦ τ ⟧kjudg (refl-edge θ) (t θ γ0) (t θ γ1)) {!t*!} -- Works up to cancellation of inverses
