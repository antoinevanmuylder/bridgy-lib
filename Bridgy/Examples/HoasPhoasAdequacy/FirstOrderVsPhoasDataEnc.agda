{-

See last theorem

-}
{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}



module Bridgy.Examples.HoasPhoasAdequacy.FirstOrderVsPhoasDataEnc where

open import Bridgy.Core.BridgePrims

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (flip)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Vec
open import Cubical.Data.Nat -- (hiding Fin)
open import Cubical.Data.Nat.Order hiding (_≤_ ; ≤-trans ; ≤-refl ; _<'_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.FinData renaming (rec to frec)
open import Cubical.Data.Empty
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Functions.FunExtEquiv


open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Rules renaming (app to appROTT)
open import Bridgy.ROTT.Param

open import Bridgy.Examples.HoasPhoasAdequacy.LambdaDefs
open import Bridgy.Examples.HoasPhoasAdequacy.RecursiveStrictOrder
open import Bridgy.Examples.HoasPhoasAdequacy.VecLemmas







module ProofReprod where
  {-
  1) (∀ V. V^j → PhoasD V) → { tn : PhoasD ℕ | each fv is <j }
  2) { tn : PhoasD ℕ | each fv is <j } → Lam j
  3) easy : Lam j → (∀ V. V^j → PhoasD V)
  -}




  toPhoasenc : ∀ j → Lam j → ∀ V → Vec V j → PhoasD V
  toPhoasenc j (var v) = λ V env → vvar (lookup v env)
  toPhoasenc j (app u w) = λ V env → vapp (toPhoasenc j u V env) (toPhoasenc j w V env)
  toPhoasenc j (lam b) = λ V env → vlam λ v → toPhoasenc (suc j) b V (v ∷ env)


  -- Results of applying binary param for a term
  --   t : ∀V → Vec V j → PhoasD V
  module BinParamCalls where

    -- V : Type ⊨ Vec V j → PhoasD V
    PhoasEnc-dNRG : (j : ℕ) → DispNRG ℓ-zero (TypeNRG ℓ-zero)
    PhoasEnc-dNRG j =
      →Form _ _ (Vecn-dNRG' j) PhoasD-dNRG'




    -- t ²@ (toℕ : Finj→ℕ) ²@ (δFin related to δ)
    auxparam : (j : ℕ) (t : ∀ V → Vec V j → PhoasD V) →
      [PhoasD]₂ (Fin j) ℕ (λ fj n → toℕ fj ≡ n) (t (Fin j) (δFin j)) (t ℕ (δℕ j))
    auxparam j t =
      param (TypeNRG ℓ-zero) (PhoasEnc-dNRG j) t (Fin j) ℕ (λ fj n → toℕ fj ≡ n) (δFin j) (δℕ j)
        -- : Vecn-dNRG' j ⦅ δFin j , δℕ j ⦆# (λ fj n → toℕ fj ≡ n)
        (invEq (VecHetRel1AsLookup j (δFin j) (δℕ j)) (sameLookupsδ j))

    -- t ²@ (toℕ : Fin(n+j)→ℕ) ²@ (revδF related to revδℕ)
    auxparam-rev : (n j : ℕ) (t : ∀ V → Vec V j → PhoasD V) →
      [PhoasD]₂ (Fin (n + j)) ℕ (λ fj n → toℕ fj ≡ n) (t (Fin (n + j)) (revδF n j)) (t ℕ (revδℕ j))
    auxparam-rev n j t =
      param (TypeNRG ℓ-zero) (PhoasEnc-dNRG j) t (Fin (n + j)) ℕ (λ fj n → toℕ fj ≡ n) (revδF n j) (revδℕ j)
      (invEq (VecHetRel1AsLookup j (revδF n j) (revδℕ j)) (sameLookupsRev n j))

    -- some binary param call for a term t : ∀ V → PhoasD V
    auxparam-noenv : (t : ∀ V → PhoasD V) (j : ℕ) → [PhoasD]₂ (Fin j) ℕ (λ fj n → toℕ fj ≡ n) (t (Fin j)) (t ℕ)
    auxparam-noenv t j = param (TypeNRG ℓ-zero) PhoasD-dNRG' t (Fin j) ℕ (λ fj n → toℕ fj ≡ n)

  open BinParamCalls

  


  -- toPhoasenc defined at the beginning
  module 2Maps where

    trick0 : ∀ j n (tf : PhoasD (Fin (n + j))) (tn : PhoasD ℕ) (trel : [PhoasD]₂ (Fin (n + j)) ℕ (λ fnj n → toℕ fnj ≡ n) tf tn) →
      [PhoasD]₁ ℕ (flip _<''_ (n + j)) tn
    trick0 j n (vlam f0) (vlam f1) trel =
      λ v vlt →
        trick0 j n
          (f0 (<''ToFin (n + j) (v , vlt))) (f1 v)
          (trel (<''ToFin (n + j) (v , vlt)) v (toℕ-<''ToFin (n + j) v vlt))
    trick0 j n (vvar v0) (vvar v1) trel =
      subst (λ blk → blk <'' (n + j)) trel (toℕRemainsLt (n + j) v0)
    trick0 j n (vapp u0 w0) (vapp u1 w1) trel =
      trick0 j n u0 u1 (trel .fst) ,
      trick0 j n w0 w1 (trel .snd)

    descope₁ : (j : ℕ) (t : ∀ V → Vec V j → PhoasD V) → PhoasD ℕ
    descope₁ j t = t ℕ (revδℕ j)

    descope₂ : (j : ℕ) (t : ∀ V → Vec V j → PhoasD V) → ∀ n → [PhoasD]₁ ℕ (flip _<''_ (n + j)) (t ℕ (revδℕ j))
    descope₂ j t n =
      trick0 j n
        (t (Fin (n + j)) (revδF n j)) -- need (j-1,..,0 : Fin n+j)
        (t ℕ (revδℕ j))
        -- requires (j-1,..,0 : Fin n+j) related  to (j-1,..,0 : ℕ)
        (auxparam-rev n j t)
    

    -- rescope
    --
    -- tnr is supposed to be a t ℕ (revδℕ j)
    -- i.e., tnr = t ℕ [j-1, ..., 1, 0]
    rescope : (tnr : PhoasD ℕ) (j : ℕ) {- (env : Vec ℕ j) -} (hyp : ∀ n → [PhoasD]₁ ℕ (flip _<''_ (n + j)) tnr)  → Lam j
    rescope (vvar v) j hyp = var (<''ToFin j (j ∸ (suc v) , ∸-compl v j (hyp 0))) --vvar v ↦ var j (j - v+1)
    rescope (vapp u w) j hyp = app (rescope u j λ n → hyp n .fst) ((rescope w j λ n → hyp n .snd))
    rescope (vlam f) j hyp =
      lam (rescope (f j) (suc j) λ n →
      subst (λ blk → [PhoasD]₁ ℕ (flip _<''_ blk) (f j)) (sym (+-suc n j)) --just a subst
      (hyp (suc n) j (j<''sucn+j j n)))

    
    -- t:  ∀ V (env : Vec V j) (N : U) (vvar : V → N) (vapp : N² → N) (vlam : (V → N) → N). N
    toLam : ∀ j → (t : ∀ V → Vec V j → PhoasD V) → Lam j
    toLam j t = rescope (t ℕ (revδℕ j)) j (descope₂ j t)

    -- def seems flawed for open terms
    rescopeAlt : (j : ℕ) (tnd : PhoasD ℕ) (tck : ∀ n → [PhoasD]₁ ℕ (λ v → v <'' (n + j)) tnd) →
                   Lam j
    rescopeAlt j (vvar v) tck =
      var (<''→Fin j v (tck 0))
    rescopeAlt j (vapp u w) tck = app (rescopeAlt j u (λ n → tck n .fst)) (rescopeAlt j w (λ n → tck n .snd))
    rescopeAlt j (vlam f) tck =
      lam (rescopeAlt (suc j) (f j) λ n →
        subst (λ blk → [PhoasD]₁ ℕ (λ v → v <'' blk) (f j)) (sym (+-suc n j))
        (tck (suc n) j (j<''sucn+j j n)))

    rescopecong : ∀ j (tnr0 tnr1 : PhoasD ℕ) (tnreq : tnr0 ≡ tnr1)
      (hyp0 : ∀ n → [PhoasD]₁ ℕ (flip _<''_ (n + j)) tnr0) (hyp1 : ∀ n → [PhoasD]₁ ℕ (flip _<''_ (n + j)) tnr1)
      (hypeq : ∀ n → PathP (λ i → [PhoasD]₁ ℕ (flip _<''_ (n + j)) (tnreq i)) (hyp0 n) (hyp1 n)) →
      rescope tnr0 j hyp0 ≡ rescope tnr1 j hyp1
    rescopecong j tnr0 trn1 tnreq hyp0 hyp1 hypeq =
      λ i → rescope (tnreq i) j (λ n → hypeq n i)


    -- some testing

    progNom1 : ∀ (V : Type) → Vec V 2 → PhoasD V
    progNom1 = λ V env → vvar (lookup one env)

    -- x2 x1 x0 ⊢ λ xm1. x1 $ λ xm2. (xm1 x2) xm2
    progPhoasenc : ∀ V → Vec V 3 → PhoasD V
    progPhoasenc V env = 
      let
        x : Fin 3 → PhoasD V
        x k = vvar (lookup k env)
      in
      vlam (λ xm1 → vapp (x one) (vlam λ xm2 → vapp (vapp (vvar (xm1)) (x two)) (vvar xm2)))
    progLam : Lam 3
    progLam =
      lam {n = 3}
        (app {n = 4} (var {n = 4} two) (lam {n = 4}
          (app {n = 5} (app {n = 5} (var {n = 5} one) (var {n = 5} four)) (var {n = 5} zero))))
    progtest : toLam 3 progPhoasenc ≡ progLam
    progtest = refl
    progtest2 : toPhoasenc 3 progLam ≡ progPhoasenc
    progtest2 = refl


    -- progtest3 : Unit
    -- progtest3 = {!rescopeAlt 3 (progPhoasenc ℕ (δℕ 3)) ?!}




  module Roundtrips where
    open 2Maps


    Lam<= : (j : ℕ) (t : Lam j) → toLam j (toPhoasenc j t) ≡ t
    --module Lam<=Help where
    Lam<= j (var v) =
      cong var
      -- ~refl
      (flip _∙_ (<''ToFin-toℕ j v)
      (cong (<''ToFin j)
      (Σ≡Prop (λ x → <''isPropValued x j)
      ((λ i → j ∸ suc (lookups-revδℕ j v i)) ∙
      ∸lemma6 j (toℕ v) (toℕRemainsLt j v)))))
    Lam<= j (app u w) =
      cong₂ app
        (flip _∙_ (Lam<= j u)
          -- ~refl
          (rescopecong j _ _ refl _ _ λ n →
          [PhoasD]₁PresProp ℕ (λ v → v <'' (n + j)) (λ v → <''isPropValued v (n + j)) (toPhoasenc j u ℕ (revδℕ j)) _ _))
        ((flip _∙_ (Lam<= j w)
          (rescopecong j _ _ refl _ _ λ n →
          [PhoasD]₁PresProp ℕ (λ v → v <'' (n + j)) (λ v → <''isPropValued v (n + j)) (toPhoasenc j w ℕ (revδℕ j)) _ _)))
    Lam<= j (lam b) =
      cong lam
      (flip _∙_ (Lam<= (suc j) b)
      -- ~refl
      (rescopecong (suc j) _ _ refl _ _ λ n →
      [PhoasD]₁PresProp ℕ (λ v → v <'' (n + suc j))
        (λ v → <''isPropValued v (n + suc j))
        (toPhoasenc (suc j) b ℕ (j ∷ revδℕ j)) _ _))





    RevEnvGraph : ∀ {V : Type} (m : ℕ) (env : Vec V m) → ℕ → V → Type
    RevEnvGraph m env k v = (km : k <'' m) → mylookup (m ∸ (suc k)) (∸-compl k m km) env ≡ v


    Phoasenc<=' : (j : ℕ) (tnr : PhoasD ℕ) (hyp : ∀ n → [PhoasD]₁ ℕ (flip _<''_ (n + j)) tnr)
                (V : Type) (env : Vec V j) (tve : PhoasD V)
                (hyp2 : ∀ n (env' : Vec V n) → PhoasD-dNRG' ⦅ tnr , tve ⦆# (RevEnvGraph (n + j) (env' ++ env))) →
                toPhoasenc j (rescope tnr j hyp) V env ≡ tve
    Phoasenc<=' j (vvar v0) hyp V env (vapp u1 w1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vvar v0) hyp V env (vlam f1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vapp u0 w0) hyp V env (vvar v1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vapp u0 w0) hyp V env (vlam f1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vlam f0) hyp V env (vvar v1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vlam f0) hyp V env (vapp u1 w1) hyp2 = rec (hyp2 0 [])
    Phoasenc<=' j (vvar v0) hyp V env (vvar v1) hyp2 =
      cong vvar
      ((my-lookup j (j ∸ (suc v0)) (∸-compl v0 j (hyp 0)) env) ∙
      hyp2 0 [] (hyp 0))
    Phoasenc<=' j (vapp u0 w0) hyp V env (vapp u1 w1) hyp2 =
      cong₂ vapp
      (Phoasenc<=' j u0
        (λ n → hyp n .fst)
        V env u1
        (λ n env' → hyp2 n env' .fst))
      (Phoasenc<=' j w0
        (λ n → hyp n .snd)
        V env w1
        (λ n env' → hyp2 n env' .snd))
    Phoasenc<=' j (vlam f0) hyp V env (vlam f1) hyp2 =
      cong vlam (funExt λ v →
      Phoasenc<=' (suc j) (f0 j)
        (λ n →
          subst (λ blk → [PhoasD]₁ ℕ (flip _<''_ blk) (f0 j)) (sym (+-suc n j)) --just a subst
          (hyp (suc n) j (j<''sucn+j j n)))
        V (v ∷ env) (f1 v)
        λ n env' →
          let
            hav = hyp2 (suc n) (vecsnoc v env') j v λ km →
              flip _∙_ (mylookup-snoc n j env' env v)
              let
                n+∸→n : n + j ∸ j ≡ n
                n+∸→n = +∸ n j

                compl→oth : PathP (λ i → n+∸→n i <'' suc (n + j)) (∸-compl j (suc (n + j)) km) ((n<''sucn+j j n))
                compl→oth =
                  (isOfHLevelPathP' {A = λ i → n+∸→n i <'' suc (n + j)} 0
                  (<''isPropValued n (suc (n + j)))
                  (∸-compl j (suc (n + j)) km)
                  (n<''sucn+j j n)
                  .fst)
              in
              λ i → mylookup (n+∸→n i) (compl→oth i) (vecsnoc v env' ++ env) 
          in
          transport (λ i → PhoasD-dNRG' ⦅ f0 j , f1 v ⦆# RevEnvGraph (+-suc n j (~ i)) (snoc-lemma n j env' env v (~ i))) --some transport
            hav)

    Phoasenc<= : (j : ℕ) (t : ∀ V → Vec V j → PhoasD V) → toPhoasenc j (toLam j t) ≡ t
    Phoasenc<= j t = funExt λ V → funExt λ env →
      Phoasenc<=' j (t ℕ (revδℕ j)) (descope₂ j t) V env (t V env)
      -- ∀ n (env' : Vec V n) → PhoasD-dNRG' ⦅ tnr , tve ⦆# (RevEnvGraph (n + j) (env' ++ env))
      λ n env' → param (TypeNRG ℓ-zero) (PhoasEnc-dNRG j) t ℕ V (RevEnvGraph (n + j) (env' ++ env)) (revδℕ j) env
        (invEq (VecHetRel1AsLookup j (revδℕ j) env) λ k km →
          _∙_
          (λ i → mylookup (rew2 n j k i) (rew3 n j k km i) (env' ++ env))
          ((mylookup-++ j n (toℕ k) (toℕRemainsLt j k) env env') ∙
          (sym (my-lookup j (toℕ k) (toℕRemainsLt j k) env)) ∙
          λ i → lookup (<''ToFin-toℕ j k i) env))
      where
        rew1 : ∀ j (k : Fin j) → (j ∸ suc (lookup k (revδℕ j))) ≡ toℕ k
        rew1 zero ()
        rew1 (suc j) zero = n∸n j
        rew1 (suc j) (suc k) =
          subst (λ blk → j ∸ blk ≡ suc (j ∸ suc blk)) (sym (lookups-revδℕ j k))
          (∸lemma j (toℕ k) (toℕRemainsLt j k))
          ∙ (cong suc (rew1 j k))

        rew2 : ∀ n j (k : Fin j) → (n + j ∸ suc (lookup k (revδℕ j))) ≡ n + (toℕ k)
        rew2 n j k =
          _∙_ 
            (∸lemma2 n j (suc (lookup k (revδℕ j)))
            (subst (λ blk → suc blk ≤ j) (sym (lookups-revδℕ j k))
            (<''→suc≤  (j ∸ suc (toℕ k)) j (∸-compl (toℕ k) j (toℕRemainsLt j k)))))
          (cong (_+_ n) (rew1 j k) )

        rew3 : ∀ n j k (km : lookup k (revδℕ j) <'' (n + j)) → PathP (λ i → (rew2 n j k i) <'' (n + j)) 
          (∸-compl (lookup k (revδℕ j)) (n + j) km)
          (<''+ n (toℕ k) j (toℕRemainsLt j k))
        rew3 = λ n j k km →
          isOfHLevelPathP' {A = λ i → (rew2 n j k i) <'' (n + j)} 0 (<''isPropValued (n + toℕ k) (n + j))
            (∸-compl (lookup k (revδℕ j)) (n + j) km) (<''+ n (toℕ k) j (toℕRemainsLt j k)) .fst

        
    Lam≃Phoasenc : ∀ j → Lam j ≃ (∀ V → Vec V j → PhoasD V)
    Lam≃Phoasenc j =
      isoToEquiv (iso
      (toPhoasenc j)
      (toLam j)
      (Phoasenc<= j)
      (Lam<= j))

  open Roundtrips public

open ProofReprod public




