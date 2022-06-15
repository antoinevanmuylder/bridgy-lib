{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module SystemF where

{-
An experiment to give straightforward param semantics to /predicative/ systemF
the conclusion of the experiment was: its possible but cumbersome because we lack cumulativity!
this file defines the syntax of pred sysF.
-}

open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.FinData.Base as FIN
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_ ; idfun)
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Data.List
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat.Order

plusEmpty : ∀ {A : Type} {n : ℕ} (v : Vec A n) →
  PathP (λ i → Vec A (+-zero n i) ) (v ++ []) v
plusEmpty [] = refl
plusEmpty (a ∷ v) = λ i → a ∷  (plusEmpty v i)

vecReverse : ∀ (A : Type) (n : ℕ) → Vec A n → Vec A n
vecReverse A n [] = []
vecReverse A (suc n) (a ∷ v) = transport (λ i → Vec A (+-comm n 1 i)) (vecReverse A n v ++ (a ∷ [])) 


-- In what follows we devise a deep embedding of system F.


-- the collection of predicative system F kinds: *₀, *₁, ...
FKind = ℕ

-- the collection of kinding contexts. Such a context is a list of type variables αᵢ : *(ℓ(i))
-- αn-1 , ... , α0 ⊢ ... correspond to vector α0 ∷ α1 ‌∷ ... ∷ αn-1
FKindCtx : ℕ → Type
FKindCtx = Vec FKind


-- kinding judgment
data FKjudg : ∀ {n : ℕ} → FKindCtx n → FKind → Type where
  -- ... α : *ₖ ... ⊢ α : *ₖ
  FtyvarJ : ∀ {n : ℕ} {Θ : FKindCtx n} (i : Fin n) → FKjudg Θ (lookup i Θ)
  -- Θ ⊢ σ : *ℓ₁ AND Θ ⊢ τ : *ℓ₂ THEN  Θ ⊢ σ → τ : *(max ℓ₁ ℓ₂)
  _⟶J_ : ∀ {n : ℕ} {Θ : FKindCtx n} {ℓ₁ ℓ₂ : FKind} →
           FKjudg Θ ℓ₁ → FKjudg Θ ℓ₂ → FKjudg Θ (max ℓ₁ ℓ₂)
  -- Θ, α : *ℓ₁ ⊢ τ : *ℓ₂    THEN    Θ ⊢ ∀(α : *ℓ₁). τ   : *(max (ℓ₁+1) ℓ₂)
  F∀J : ∀ {n : ℕ} {Θ : FKindCtx n} {ℓ₁ ℓ₂ : FKind} → 
          (τ : FKjudg (ℓ₁ ∷  Θ) ℓ₂) → FKjudg Θ (max (suc ℓ₁) ℓ₂)
{- Deprecated rules of this kinding judgment.
   We can define weakening and substitution on top of the kinding judgment (as admissible rules).
   And we don't need *i to be a well kinded type.
  -- Θ ⊢ *(ℓ) : *(ℓ+1)
  -- Θ⊢ τ : *ᵢ THEN Θ, α:*ⱼ ⊢ τ : *ᵢ
  -- Θ ⊢ A : *ℓα  AND    Θ, α:*ℓα ⊢ τ : *ℓτ   THEN Θ ⊢ τ[A/α] : *ℓτ
-}

-- Let σ be a permutation. if σ ↷ Θ ⊢ τ THEN Θ ⊢ τ
-- We go for all permutations because proof for head-transpositions Θ , ℓ₂ , ℓ₁ ⊢ Θ , ℓ₁ , ℓ₂
-- require other kinds of permutations.
module AdmissibleExchangeType where

  Perm : ℕ → Type
  Perm n = Iso (Fin n) (Fin n)

  _↷_ : ∀ {n} → Perm n → FKindCtx n → FKindCtx n 
  _↷_ σ Θ = FinVec→Vec (Vec→FinVec Θ ∘ (Iso.fun σ))

  lookupFinVec→Vec : ∀ {n} {A : Type} (f : FinVec A n) (j : Fin n) →
    lookup j (FinVec→Vec f) ≡ f j
  lookupFinVec→Vec f j = λ i → (FinVec→Vec→FinVec f) i j

  substTensorId : ∀ {n} → Perm n → Perm (suc n)
  substTensorId σ = iso
                      (λ {zero → zero ; (suc i) → suc (Iso.fun σ i)})
                      (λ {zero → zero ; (suc i) → suc (Iso.inv σ i)})
                      (λ {zero → refl ; (suc i) → cong suc (Iso.rightInv σ i)})
                      λ {zero → refl ; (suc i) → cong suc (Iso.leftInv σ i)}


  lookupSubst : ∀ {n} {Θ : FKindCtx n} (σ : Perm n) (i : Fin n) →
    lookup (Iso.fun σ i) Θ ≡ lookup i (σ ↷ Θ)
  lookupSubst σ i = refl ∙ sym (lookupFinVec→Vec _ i)

  -- σ ↷ Θ ⊢ τ THEN Θ ⊢ τ
  exchRuleType : ∀ {n} {ℓ : FKind} {Θ : FKindCtx n} (σ : Perm n) →
    FKjudg (σ ↷ Θ) ℓ → FKjudg Θ ℓ
  exchRuleType σ (FtyvarJ i) = transport (cong (FKjudg _) (lookupSubst σ i)) (FtyvarJ (Iso.fun σ i))
  exchRuleType σ (A ⟶J B) = exchRuleType σ A ⟶J exchRuleType σ B
  exchRuleType σ (F∀J τ) = F∀J (exchRuleType (substTensorId σ) τ)

  -- we need the special case `exchHead` (to "head" weaken ∀types ; θ⊢ ∀ ⇒ θ,α ⊢ ∀)
  -- below is the involution corresponding to exchHead
  swapHeadPerm : ∀ {n} → Perm (suc (suc n))
  swapHeadPerm = iso
                 (λ {zero → suc zero ; (suc zero) → zero ; (suc (suc i)) → suc (suc i)})
                 (λ {zero → suc zero ; (suc zero) → zero ; (suc (suc i)) → suc (suc i)})
                 (λ {zero → refl ; (suc zero) → refl ; (suc (suc i)) → refl })
                 (λ {zero → refl ; (suc zero) → refl ; (suc (suc i)) → refl })

  exchHeadRule : ∀ {n} {Θ : FKindCtx n} {ℓ₁ ℓ₂ ℓtgt : FKind} →
    FKjudg (ℓ₂ ∷ ℓ₁ ∷ Θ) ℓtgt → FKjudg (ℓ₁ ∷ ℓ₂ ∷ Θ) ℓtgt
  exchHeadRule {n} {Θ} {ℓ₁} {ℓ₂} {ℓtgt} τ = exchRuleType swapHeadPerm (transport (cong (λ blank → FKjudg (ℓ₂ ∷ ℓ₁ ∷ blank) ℓtgt) rewriteΘ) τ)
    where
    rewriteΘ : Θ ≡ FinVec→Vec (λ x → lookup x Θ)
    rewriteΘ = sym ( Vec→FinVec→Vec Θ)
open AdmissibleExchangeType


-- Next we have admissible weakening for types
module AdmissibleWeakeningType where

  wknRuleType : ∀ {n} {Θ : FKindCtx n} {ℓwk ℓτ : FKind} →
    FKjudg Θ ℓτ → FKjudg (ℓwk ∷ Θ) ℓτ
  wknRuleType (FtyvarJ i) = FtyvarJ (suc i)
  wknRuleType (A ⟶J B) = (wknRuleType A) ⟶J (wknRuleType B) 
  wknRuleType (F∀J τ) = F∀J (exchHeadRule (wknRuleType τ))

  -- Θ ⊢ τ THEN Θ , Θ' ⊢ τ
  wknRuleTypeFull : ∀ {n n'} {Θ : FKindCtx n} {ℓ : FKind} (Θ' : FKindCtx n') →
    FKjudg Θ ℓ → FKjudg (Θ' ++ Θ) ℓ
  wknRuleTypeFull [] A = A
  wknRuleTypeFull (ℓ' ∷ Θ') A = wknRuleType (wknRuleTypeFull Θ' A)

  -- swapTyCtxPerm : ∀ (n n' : ℕ) → Perm (n + n')
  -- swapTyCtxPerm n 0 = transport (λ i → Perm (+-zero n (~ i))) (iso (λ k → k) (λ k → k) (λ _ → refl) (λ _ → refl))
  -- swapTyCtxPerm n (suc n') = transport (λ i → Perm (smℕlemma n n' i)) (swapTyCtxPerm (suc n) n')

  -- swapTyCtxEq : ∀ n n' (Θ : FKindCtx n) (Θ' : FKindCtx n') →
  --   PathP (λ i → FKindCtx (+-comm n' n i)) (Θ' ++ Θ) (swapTyCtxPerm n n' ↷ (Θ ++ Θ'))
  -- swapTyCtxEq n n' Θ [] = {!!}

  -- wknLeftRuleType : ∀ {n} {Θ : FKindCtx n} {ℓ ℓwk : FKind} →
  --   FKjudg Θ ℓ → FKjudg (Θ ++ (ℓwk ∷  [])) ℓ
  -- wknLeftRuleType A = {!!}
  -- Θ ⊢ τ THEN Θ, ℓwk ⊢ τ


  -- smℕlemma : ∀ n n' → (suc n) + n' ≡ n + (suc n')
  -- smℕlemma 0 n' = refl
  -- smℕlemma (suc n) n' = cong suc (smℕlemma n n')

  -- wkFinSum : ∀ (n n' : ℕ) → Fin n → Fin (n + n')
  -- wkFinSum n 0 i = transport (λ i → Fin (+-comm n 0 (~ i))) i
  -- wkFinSum n (suc n') i = transport (λ i → Fin (smℕlemma n n' i)) (wkFinSum (suc n) n' (weakenFin i))

  -- lookupWkn : ∀ {A : Type} n n' (Θ : Vec A n) (Θ' : Vec A n') (k : Fin n)  →
  --   lookup (wkFinSum n n' k) (Θ ++ Θ')  ≡ lookup k Θ
  -- lookupWkn n n' Θ [] k = sym λ j → lookup (transport-filler (λ i → Fin (+-zero n (~ i))) k j) (plusEmpty Θ (~ j))
  -- lookupWkn n (suc n') [] (θ' ∷ Θ') k = ⊥.rec (¬Fin0 k)
  -- lookupWkn (suc n) (suc n') (θ ∷ Θ) (θ' ∷ Θ') k = {!!} ∙ lookupWkn (suc n) n' (θ ∷ Θ) Θ' k 
  -- -- lookupWkn n (suc n') Θ (θ ∷ Θ') k = {!!} ∙ lookupWkn n n' Θ Θ' k
  

  -- wknRuleTypeFull' : ∀ {n n'}  {ℓ : FKind} {Θ' : FKindCtx n'} {Θ : FKindCtx n} →
  --   FKjudg Θ ℓ → FKjudg (Θ ++ Θ') ℓ
  -- wknRuleTypeFull' {n} {n'} {ℓ} {Θ'} {Θ} (FtyvarJ i) = {!!} -- FtyvarJ  {!wkFinSum n n' i!}
  -- wknRuleTypeFull' _ = {!!}

  -- -- -- Θ ⊢ τ THEN Θ', Θ ⊢ τ
  -- -- wknRuleTypeFull' : ∀ {n n'}  {ℓ : FKind} (Θ' : FKindCtx n') (Θ : FKindCtx n) →
  -- --   FKjudg Θ ℓ → FKjudg (Θ ++ Θ') ℓ
  -- -- wknRuleTypeFull' {n} {n'} {ℓ} Θ' Θ A = exchRuleType (swapTyCtxPerm n n') {!!}
open AdmissibleWeakeningType


-- The substitution rule is also admissible.
module AdmissibleSubstitutionType where

  -- We define a notion of substitution between kinding contexts Θ ⊢ Θ'
  -- Such a substitution s : Θ ⊢ Θ' is a way to fill each variable θ' ∈ Θ' based on context Θ
  FTySubst : ∀ {n n' : ℕ} (Θ : FKindCtx n) (Θ' : FKindCtx n') → Type
  FTySubst Θ Θ' = ∀ (i : Fin _) → FKjudg Θ (lookup i Θ')

  -- Θ ⊢ Θ' then Θ, α:*ℓ ⊢ Θ'
  wkTySubst : ∀ {n n'} {Θ : FKindCtx n} {ℓ : FKind} {Θ' : FKindCtx n'} →
    FTySubst Θ Θ' → FTySubst (ℓ ∷ Θ) Θ'
  wkTySubst s i = wknRuleType (s i)

  -- Θ ⊢ Θ' THEN Θ, α:*ℓ ⊢ Θ', α : *ℓ
  tensorTySubst : ∀ {n n'} {Θ : FKindCtx n} {Θ' : FKindCtx n'} {ℓ : FKind} →
    FTySubst Θ Θ' → FTySubst (ℓ ∷ Θ) (ℓ ∷ Θ')
  tensorTySubst s zero = FtyvarJ zero
  tensorTySubst s (suc i) = wkTySubst s i


  -- Below, subsitution as an admissible kinding rule: wkinded types can
  -- be pulled back along substitutions
  substTypeRule : ∀ {n n'} {Θ : FKindCtx n} {Θ' : FKindCtx n'} {ℓ : FKind}  →
    FTySubst Θ Θ' → FKjudg Θ' ℓ → FKjudg Θ ℓ
  substTypeRule s (FtyvarJ i) = s i
  substTypeRule s (A ⟶J B) = substTypeRule s A ⟶J substTypeRule s B
  substTypeRule s (F∀J τ) = F∀J (substTypeRule (tensorTySubst s) τ)
open AdmissibleSubstitutionType

-- -- well kinded types = kinding derivations + kind annotation
record FType {n : ℕ} (Θ : FKindCtx n) : Type where
  constructor mkFType
  field
    { theKind } : FKind
    theKindingDer : FKjudg Θ theKind
open FType

Ftyvar : ∀ {n} {Θ : FKindCtx n} → (i : Fin n) → FType Θ
Ftyvar i = mkFType (FtyvarJ i)

_⟶_ : ∀ {n} {Θ : FKindCtx n} → FType Θ → FType Θ → FType Θ
_⟶_ A B = mkFType (A .theKindingDer ⟶J B .theKindingDer)

F∀ : ∀ {n} {Θ : FKindCtx n} (ℓ : FKind) → FType (ℓ ∷ Θ) → FType Θ
F∀ ℓ τ = mkFType (F∀J (τ .theKindingDer))

wknType : ∀ {n} {Θ : FKindCtx n} {ℓ : FKind} → FType Θ → FType (ℓ ∷ Θ)
wknType τ = mkFType (wknRuleType (τ .theKindingDer))

substType : ∀ {n n'} {Θ : FKindCtx n} {Θ' : FKindCtx n'} →
  FTySubst Θ Θ' → FType Θ' → FType Θ
substType σ T = mkFType (substTypeRule σ (T .theKindingDer))

substForOldTyApp : ∀ {n} {Θ : FKindCtx n} {ℓ : FKind} →
  FKjudg Θ ℓ → FTySubst Θ (ℓ ∷ Θ)
substForOldTyApp A zero = A
substForOldTyApp A (suc i) = FtyvarJ i

-- idTensorSubst : ∀ {n n'} {Θ : FKindCtx n} {ℓ : FKind} (Θ' : FKindCtx n') →
--   FKjudg Θ' ℓ → FTySubst (Θ' ++ Θ) (ℓ ∷ Θ)
-- idTensorSubst [] A = λ {zero → {!!} ; (suc i) → FtyvarJ i}
-- idTensorSubst (ℓ' ∷ Θ') A = {!!}

-- typing context over kinding context
FTypCtx : ∀ {n} (Θ : FKindCtx n) → ℕ → Type
FTypCtx Θ m = Vec (FType Θ) m


-- can weaken each type in Γ : FTypeCtx Θ m by a single type var
wknTypCtx : ∀ {n m} {Θ : FKindCtx n} {ℓ : FKind} →
  FTypCtx Θ m → FTypCtx (ℓ ∷ Θ) m
wknTypCtx [] = []
wknTypCtx (τ ∷ Γ) = wknType τ ∷ wknTypCtx Γ

-- or by a whole kinding context
wknTypCtxFull : ∀ {n n' m} {Θ : FKindCtx n} (Θ' : FKindCtx n') →
  FTypCtx Θ m → FTypCtx (Θ' ++ Θ) m
wknTypCtxFull [] A = A
wknTypCtxFull (A ∷ Θ') B = wknTypCtx (wknTypCtxFull Θ' B)



-- typing derivations
-- do I care about weakening?
data FTypJudg : ∀ {n m} (Θ : FKindCtx n) (Γ : FTypCtx Θ m) → FType Θ → Type where
  Fvar :  ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} →
            (i : Fin m) → FTypJudg Θ Γ (lookup i Γ)
  Fλ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} →
       {A B : FType Θ} →
         -- Θ | Γ , x:A ⊢ e : B  THEN  Θ | Γ ⊢ λx.e : A → B
         FTypJudg Θ ( A ∷ Γ ) B → FTypJudg Θ Γ (A ⟶ B)
  _Fof_ : ∀ {n m m'} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {Γ' : FTypCtx Θ m'} →
           {A B : FType Θ} →
             -- Θ|Γ⊢ f :A→B AND Θ|Γ'⊢ a:A THEN Θ|Γ,Γ'⊢ fa:B
             FTypJudg Θ Γ (A ⟶ B) → FTypJudg Θ Γ' A → FTypJudg Θ (Γ' ++ Γ) B
  FΛ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {ℓ : FKind} {τ : FType (ℓ ∷ Θ)}  →
      (FTypJudg (ℓ ∷ Θ) (wknTypCtx Γ) τ)   →   FTypJudg Θ Γ (F∀ ℓ τ)
  -- can apply "cumulatively", ie type variable with low enough Ulevel? (see "Finitely Stratified Polymorphism" - Leivant )
  -- _Fat_ : ∀ {n n' m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {Θ' : FKindCtx n'} {ℓ : FKind} {τ : FType (ℓ ∷ Θ)} →
  --            FTypJudg Θ Γ (F∀ ℓ τ) → (opand : FKjudg Θ' ℓ) → FTypJudg (Θ' ++ Θ) (wknTypCtxFull Θ' Γ) (substType (substForTyApp opand) τ)
{-
old application rules: contexts did not grow while synthesis but equational thy needed weakening.
  _Fof_ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} →
           {A B : FType Θ} →
             -- Θ|Γ⊢ f :A→B AND Θ|Γ⊢ a:A THEN Θ|Γ⊢ fa:B
             FTypJudg Θ Γ (A ⟶ B) → FTypJudg Θ Γ A → FTypJudg Θ Γ B
  _Fat_ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {ℓ : FKind} {τ : FType (ℓ ∷ Θ)} →
             FTypJudg Θ Γ (F∀ ℓ τ) → (opand : FKjudg Θ ℓ) → FTypJudg Θ Γ (substType (substForTyApp opand) τ)
-}




-- EXAMPLES
-- the church unit type
FChurchUnit : FType []
FChurchUnit = F∀ zero (Ftyvar zero ⟶ Ftyvar zero)

-- we give FChurchUnit in signature to help infer useless stuff
-- FpolymIdDer : FTypJudg [] [] FChurchUnit
-- FpolymIdDer = theTDer (FΛ _ (Fλ _ (Fvar zero)))

-- -- FpolymId : FTerm [] []
-- -- FpolymId = mkFTerm FpolymIdDer

-- FpolymId : FTypJudg [] [] FChurchUnit
-- FpolymId = FΛ (Fλ (Fvar zero))


-- -- eta expansion of FpolymId
-- -- todo: admissible weakening for terms, for both tm vars and type vars.
-- --       enough to state βη equational thy for this initial systemF?
-- FpolymIdη : FTypJudg [] [] FChurchUnit
-- FpolymIdη = FΛ (Fλ (({!!} Fat (FtyvarJ zero)) Fof (Fvar zero)))

-- FpolymIdwkn : FTypJudg (0 ∷ []) (Ftyvar zero ∷ []) FChurchUnit
-- FpolymIdwkn = ?


-- eta expansion of FpolymId
-- FpolymIdηDer : FTypJudg [] [] FChurchUnit
-- FpolymIdηDer = theTDer (FΛ _ (Fλ _ ({!!} Fof (FvarJ zero))))






-- -- a well typed term over ctx Θ | Γ
-- record FTerm {n m} (Θ : FKindCtx n) (Γ : FTypCtx Θ m) : Type where
--   constructor mkFTerm
--   field
--     { theType } : FType Θ
--     theTDer : FTypJudg Θ Γ theType
-- open FTerm


-- Fvar : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} →
--          Fin m → FTerm Θ Γ
-- Fvar i = mkFTerm (FvarJ i)

-- Fλ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} (A : FType Θ) →
--        FTerm Θ (A ∷ Γ) → FTerm Θ Γ
-- Fλ A openTm = mkFTerm (FλJ (openTm .theTDer))

-- _Fof_ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {A B : FType Θ} →
--           FTypJudg Θ Γ (A ⟶ B) → FTypJudg Θ Γ A → FTerm Θ Γ
-- _Fof_ fder tder = mkFTerm (FTmAppJ fder tder)

-- FΛ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} (ℓ : FKind) →
--        FTerm (ℓ ∷ Θ) (wknTypCtx Γ) → FTerm Θ Γ
-- FΛ ℓ openTm = mkFTerm (FΛJ (openTm .theTDer))

-- _Fat_ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypCtx Θ m} {ℓ : FKind} {τ : FType (ℓ ∷ Θ)} →
--           FTypJudg Θ Γ (F∀ ℓ τ) → FKjudg Θ ℓ → FTerm Θ Γ
-- _Fat_ fder Ader = mkFTerm (FTyAppJ fder Ader)


-- -- example: void church encoding ∅ ⊢ (∀(α : *₀). α) : *₁
-- FChurchVoid' : FType' [] (star 1)
-- FChurchVoid' = F∀' (Fsvar' {Θ = [ star 0 ]} zero)

-- -- example: unit church encoding ∅ ⊢ ∀(α : *₀). α → α : *₁
-- FChurchUnit' : FType' [] (star 1)
-- FChurchUnit' = F∀' ((Fsvar' {Θ = [ star 0 ]} zero) ⟶' (Fsvar' {Θ = [ star 0 ]} zero))

-- FChurchUnit : FType []
-- FChurchUnit = mkFType (star 1) FChurchUnit'


-- Fstar : ∀ {n} {Θ : FKindCtx n} → ℕ  → FType Θ
-- Fstar ℓ = mkFType
--           (suc ℓ)
--           (Fstar' ℓ)

-- _⟶_ : ∀ {n} {Θ : FKindCtx n} → FType Θ → FType Θ → FType Θ
-- _⟶_ A B = mkFType
--            (star (max (A .theKind) (B .theKind)))
--            (A .theKindingDer ⟶' B .theKindingDer)

-- F∀ : ∀ {n} {Θ : FKindCtx n} (ℓ : FKind) →
--        FType ([ star ℓ ] ++ Θ) → FType Θ
-- F∀ ℓ T = mkFType
--           (star (max (suc ℓ) (T .theKind)))
--           (F∀' (T .theKindingDer))

-- -- weakening a well kinded type
-- Fswk : ∀ {n} {Θ : FKindCtx n} (ℓ : FKind) →
--            FType Θ → FType ([ star ℓ ] ++ Θ)
-- Fswk ℓ τ = mkFType
--            (τ .theKind) (Fswk' (τ .theKindingDer))

-- Fs-esubst :  ∀ {n : ℕ} {Θ : FKindCtx n} {ℓ : FKind} →
--                FType' Θ (star ℓ) → FType ([ star ℓ ] ++ Θ) →
--                FType Θ
-- Fs-esubst Ader τ = mkFType
--                    (τ .theKind)
--                    (Fs-esubst' Ader (τ .theKindingDer))






-- -- wknKindTypeCtx : ∀ {n m} {Θ : FKindCtx n} (ℓ : FKind) →
-- --                    FTypeCtx Θ m → FTypeCtx ([ star ℓ ] ++ Θ) m
-- -- wknKindTypeCtx ℓ Γ = map (Fswk ℓ) Γ





-- -- FChurchUnit : *₁ is probably the simplest type of this calculus being inhabited
-- -- there are indeed no ground types O : *₀.
-- -- We give the canonical inhabitant ∅|∅ ⊢ Λ α . λ a . a   :  ∀(α : *0). α → α.
-- Fpolymid : FTerm [] [] FChurchUnit
-- Fpolymid = FΛ (Fλ  (Fvar zero)) 
-- -- let thing = (mkFType (star 0) (Fsvar' zero))
-- --            in
             

-- -- there is also its eta expansion!
-- -- not possible with current broken esubst-based kinding judgment. TODO: define a substitution function converting telescope of type valuations.
-- Fpolymidη : FTerm [] [] FChurchUnit
-- Fpolymidη = FΛ (Fλ {!FTyApp Fpolymid  !})

{- OLD JUNK
-- Now whats a typing context, over a given kinding ctx? Θ | Γ = ... xi : Ai : *ℓ(i) ...
-- its an ordered set of proofs that Ai : *ℓ(i)
-- due to the heterogeneous types we can not pack this into a vec anymore :(
record FTypeCtx {n m : ℕ} (Θ : FKindCtx n) : Type where
  field
    -- sctx : FKindCtx n        -- kinding ctx Θ = ... αi : *ℓᵢ
    svec : Vec FKind m       -- kinds S of current typing context. Γ = ... xi : Ai : S ...
    wkinded : ∀ (i : Fin m) → FType' Θ (lookup i svec) -- each Ai in Γ is a well kinded type.

  ∅ctx : FTypeCtx Θ
  ∅ctx = record { svec = []
                ; wkinded = λ i → ⊥.rec (¬Fin0 i) }

  -- first arg is an implicit Γ : FTypeCtx Θ
  ctx-append : (ℓA : FKind) (A : FType' Θ (star ℓA)) → FTypeCtx Θ
  ctx-append ℓA A = record { svec = [ star ℓA ] ++ svec
                           ; wkinded = this }
    where
    this : (i : Fin (suc m)) → FType' Θ (lookup i (star (star ℓA) ∷ svec))
    this zero = A
    this (suc i) = wkinded i
open FTypeCtx


-- def of typing judg Θ | Γ ⊢ a : A
data FTerm : ∀ {n m} (Θ : FKindCtx n) (Γ : FTypeCtx {m = m} Θ) (ℓA : FKind) → FType' Θ (star ℓA) → Type where
  Fvar :  ∀ {n m} {Θ : FKindCtx n} {Γ : FTypeCtx {m = m} Θ} →
            (i : Fin m) → FTerm Θ Γ (lookup i (Γ .svec )) (Γ .wkinded i)
  Fλ : ∀ {n m} {Θ : FKindCtx n} {Γ : FTypeCtx {m = m} Θ} (ℓA : FKind) (A : FType' Θ (star ℓA)) →
       (ℓB : FKind) (B : FType' Θ (star ℓB)) →
         -- Θ | Γ , x:A ⊢ e : B  THEN  Θ | Γ ⊢ λx.e : A → B
         FTerm Θ (ctx-append Γ ℓA A) ℓB B → FTerm Θ Γ (star (max ℓA ℓB)) (A ⟶ B)

-}
