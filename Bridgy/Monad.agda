{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

open import Bridgy.BridgePrims
open import Bridgy.ExtentExamples
open import Bridgy.GelExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

-- Type premonads and a commutation principle, proved by hand
module Bridgy.Monad where

record PreMnd (l : Level) : Type (ℓ-suc l) where
  field
    --action on types
    acty : Type l → Type l
    --operations
    ret : {A : Type l} → A → acty A
    bind : {A B : Type l} → acty A → (A → acty B) → acty B
open PreMnd public


-- type of logical relations btw 2 premonads M0 and M1
record PreMndLrel {l : Level} (M0 M1 : PreMnd l) : Type (ℓ-suc l) where
  field
    -- logical rel of type wrappers Type -> Type
    actyr : ∀ A0 A1 → (A0 → A1 → Type l) → M0 .acty A0 → M1 .acty A1 → Type l
    -- ret0 and ret1 must be related over actyr
    retr : ∀ A0 A1 (AA : A0 → A1 → Type l) (a0 : A0) (a1 : A1) (aa : AA a0 a1) →
      actyr A0 A1 AA (M0 .ret a0) (M1 .ret a1)
    -- same for bind
    bindr : ∀ A0 A1 AA B0 B1 BB → 
      ∀ ma0 ma1 (maa : actyr A0 A1 AA ma0 ma1) → --wrapped values are structurally related
      ∀ k0 k1 (kk : ∀ a0 a1 (aa : AA a0 a1) → (actyr B0 B1 BB) (k0 a0) (k1 a1)) → --continuations are pointwise related
      actyr B0 B1 BB (M0 .bind ma0 k0) (M1 .bind ma1 k1) --then their bind are related as well
open PreMndLrel public
      
-- whats a bridge at PreMnd? we can either start by transforming
-- PreMnd into a Sigma (see thm below), or have a custom thm making bridge
-- commute with the record type former. Bridge commutation for records can not
-- be stated generally as records are not first-class.
premnd-asΣ : {l : Level} →
  (PreMnd l)
  ≃
  ( Σ[ M ∈ (Type l → Type l) ] (∀ A → A → (M A)) × (∀ A B → M A → (A → M B) → M B) )
premnd-asΣ = isoToEquiv (iso
  (λ MM → MM .acty ,  (λ A → MM .ret) , λ A B → MM .bind)
  (λ M → record {
    acty = M .fst ;
    ret = λ {_} → M .snd .fst _ ;
    bind = λ {_ _} → M .snd .snd _ _ })
    (λ M → refl)
    λ MM → refl)

record PreMndRecOfBdg {l : Level} (M0 M1 : PreMnd l) : Type (ℓ-suc l) where
  field
    actyb : BridgeP (λ _ → Type l → Type l) (M0 .acty) (M1 .acty)
    retb : BridgeP (λ x → ∀ A → A → (actyb x) A) (λ A → M0 .ret {A = A}) (λ A → M1 .ret {A = A})
    bindb : BridgeP (λ x → ∀ A B → (actyb x) A → (A → (actyb x) B) → (actyb x) B)
                    (λ A B → M0 .bind {A = A} {B = B}) λ A B → M1 .bind {A = A} {B = B}
open PreMndRecOfBdg

-- make Bridge and the record type former for PreMnd commute
BridgeVsPreMndRecord : {l : Level} (M0 M1 : PreMnd l) →
  PreMndRecOfBdg M0 M1 ≃ BridgeP (λ _ → PreMnd l) M0 M1
BridgeVsPreMndRecord M0 M1 = isoToEquiv (iso
  (λ recMbdg x → record {
    acty = recMbdg .actyb x ;
    ret = λ {_} → recMbdg .retb x _  ;
    bind = λ {_ _} → recMbdg .bindb x _ _ })
  (λ q → record {
    actyb = λ x → q x .acty ;
    retb = λ x A → q x .ret {A = A} ;
    bindb = λ x A B → q x .bind {A = A} {B = B} })
  (λ q → refl)
  λ recMbdg → refl)


PreMndLrelEquivPreMndRecOfBdg : {l : Level} (M0 M1 : PreMnd l) →
  PreMndLrel M0 M1 ≃ PreMndRecOfBdg M0 M1
PreMndLrelEquivPreMndRecOfBdg M0 M1 = isoToEquiv (iso
  (λ θ → record {
    actyb = ΠBridgeP λ A0 A1 AA → equivFun relativity (θ .actyr _ _ (invEq relativity AA)) ;
    retb = ΠBridgeP λ A0 A1 AA → ΠBridgeP λ a0 a1 aa →
      transport (funExt⁻ (funExt⁻
          (sym (retEq (relativity {A0 = M0 .acty A0} {A1 = M1 .acty A1}) (θ .actyr A0 A1 (BridgeP (λ x₁ → AA x₁)))))
          (M0 .ret {A = A0} a0)) (M1 .ret {A = A1} a1))
      ( (θ .retr A0 A1 (invEq relativity AA) a0 a1 aa)) ;
      -- prim^gel {R = (θ .actyr A0 A1 (BridgeP (λ x₁ → AA x₁))) }
      -- (M0 .ret {A = A0} a0) (M1 .ret {A = A1} a1)
      -- (θ .retr A0 A1 (invEq relativity AA) a0 a1 aa) x  ;
    bindb = ΠBridgeP λ A0 A1 AA → ΠBridgeP λ B0 B1 BB → 
      ΠBridgeP λ ma0 ma1 maa → ΠBridgeP λ k0 k1 kk →
      λ x → {!θ .bindr A0 A1 (invEq relativity AA) B0 B1 (invEq relativity BB) ma0 ma1  !}
      })
-- λ x gl-ma gl-k → 
--       prim^gel {R = (θ .actyr B0 B1 (BridgeP (λ x₁ → BB x₁))) }
--       {!θ .bindr A0 A1 (invEq relativity AA) B0 B1 (invEq relativity BB)!}
--       {!!}
--       {!!} x })
  {!!}
  {!!}
  {!!})
