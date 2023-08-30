{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-} 

open import Agda.Builtin.Cubical.Glue renaming (pathToEquiv to lineToEquiv)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

module Bridgy.MyPathToEquiv where

-- The 4 following lemmas concern a function formerly known as pathToEquiv
-- and defined using lineToEquiv (from Agda.Builtin.Cubical.Glue)
-- 
-- old name        new name       more equations
-- ----------      ------------   -------------------------------------
-- transpEquiv     pathToEquiv    no (defined using transported isEquiv)
-- pathToEquiv     mypathToEquiv  yes (defined directly)
--
-- for instance, invEq (mypathToEquiv p) : transport (λ i → p (~ i)) definitionally
--
mypathToEquiv : ∀ {l : Level} {A B : Type l} → A ≡ B → A ≃ B
mypathToEquiv p = lineToEquiv (λ i → p i)

mypathToEquivRefl : {ℓ : Level} {A : Type ℓ} → mypathToEquiv refl ≡ idEquiv A
mypathToEquivRefl {ℓ = ℓ} {A = A} = equivEq (λ i x → transp (λ _ → A) i x)

mypathToEquiv-ua : {ℓ : Level} {A B : Type ℓ} (e : A ≃ B) → mypathToEquiv (ua e) ≡ e
mypathToEquiv-ua = Univalence.au-ua mypathToEquiv mypathToEquivRefl

ua-mypathToEquiv : {ℓ : Level} {A B : Type ℓ} (p : A ≡ B) → ua (mypathToEquiv p) ≡ p
ua-mypathToEquiv = Univalence.ua-au mypathToEquiv mypathToEquivRefl
