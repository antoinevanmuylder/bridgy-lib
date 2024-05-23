{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}

module HoLam where


open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Vec
open import Cubical.Data.FinData renaming (rec to frec)

open import Bridgy.Examples.LamChurch
open import Bridgy.ROTT.Judgments


------------------------------------------------------------------------
-- lemmas

asFin : ∀ n i → (i my< n ≡ true) → Fin n
asFin 0 i ctr = rec (not<0 i ctr)
asFin (suc n) 0 _ = zero
asFin (suc n) (suc i) hyp = suc (asFin n i hyp)

my<AND∸' : ∀ j → j my< (suc j) ≡ true
my<AND∸' zero = refl
my<AND∸' (suc j) = my<AND∸' j

my<Trans : ∀ i j k → (i my< j) ≡ true → (j my< k) ≡ true → (i my< k) ≡ true
my<Trans zero zero zero ctr = rec (false≢true ctr)
my<Trans zero zero (suc k) ctr = rec (false≢true ctr)
my<Trans zero (suc j) zero _ ctr = rec (false≢true ctr)
my<Trans zero (suc j) (suc k) = λ _ _ → refl
my<Trans (suc i) zero zero ctr = rec (false≢true ctr)
my<Trans (suc i) zero (suc k) ctr = rec (false≢true ctr)
my<Trans (suc i) (suc j) zero _ ctr = rec (false≢true ctr)
my<Trans (suc i) (suc j) (suc k) = my<Trans i j k


my<AND∸ : ∀ k j → ((j ∸ k) my< (suc j) ≡ true)
my<AND∸ 0 0 = refl
my<AND∸ (suc k) 0 = refl
my<AND∸ 0 (suc j) = my<AND∸' j
my<AND∸ (suc k) (suc j) = my<Trans (j ∸ k) (suc j) (suc (suc j)) (my<AND∸ k j) (my<AND∸' j)




------------------------------------------------------------------------

HoModLam' = Σ Type (λ X → ((X → X) → X) × (X → X → X))

HoModLam = Σ Type (λ X →
  (∀ n i → (i my< n ≡ true) → Vec X n → X) ×
  ((X → X) → X) ×
  (X → X → X))

FoModLam = Σ (ℕ → Type) (λ L →
  (∀ n i → (i my< n ≡ true) → L n) ×
  (∀ n → L (suc n) → L n) ×
  (∀ n → L n → L n → L n))

varHof : (H : HoModLam) → (∀ n i → (i my< n ≡ true) → Vec (H .fst) n → H .fst)
varHof H = H .snd .fst

appHof : (H : HoModLam) → H .fst → H .fst → H .fst
appHof H = H .snd .snd .snd

lamHof : (H : HoModLam) → (H .fst → H .fst) → H .fst
lamHof H = H .snd .snd .fst

famOof : (M : FoModLam) → ℕ → Type
famOof M = M .fst

varOof : (M : FoModLam) → (∀ n i → (i my< n ≡ true) → famOof M n)
varOof M = M .snd .fst

lamOof : (M : FoModLam) → (∀ n → famOof M (suc n) → famOof M n)
lamOof M = M .snd .snd .fst

appOof : (M : FoModLam) → (∀ n → famOof M n → famOof M n → famOof M n)
appOof M = M .snd .snd .snd


------------------------------------------------------------------------

-- (n i : ℕ) → (i my< n) ≡ true → Vec (H .fst) n → H .fst
toFo : HoModLam → FoModLam
toFo H =
  ((λ n → Vec (H .fst) n → H .fst)) ,
  varHof H ,
  (λ n bod env → lamHof H (λ h → bod (h ∷ env))) ,
  λ n u v env → appHof H (u env) (v env)


toHo : FoModLam → HoModLam
toHo M =
  (∀ n → famOof M n) ,
  (λ n i hyp hs → lookup (asFin n i hyp) hs ) ,
  (λ f i → lamOof M i (flip f (suc i) (aux i))) ,
  λ u v n → appOof M n (u n) (v n)
  where
    aux : ∀ (i j : ℕ) → famOof M j
    --cheating a bit. "Crucially it is always the case that j>i",  in [Atkey] "Syntax for free"  
    --the hope here is that the rhs when j<=i will never be used
    aux i 0 = lamOof M _ (varOof M 1 0 refl)  
    aux i (suc j) = varOof M (suc j) (j ∸ (suc i)) (my<AND∸ (suc i) j)


      
