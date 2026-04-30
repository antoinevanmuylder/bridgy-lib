{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Maybe renaming (rec to mbrec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData renaming (rec to frec)
open import Cubical.Data.Vec


-- open import Bridgy.Core.ExtentExamples
-- open import Bridgy.Core.MyPathToEquiv
-- open import Bridgy.Core.EquGraph
-- open import Bridgy.ROTT.Judgments
-- open import Bridgy.ROTT.Rules
-- open import Bridgy.ROTT.WknPresTypeFormers

open import LambdaDefs

-- From LambdaDefs:
-- [PhoasD]₁ : (V : Type) (Vdot : V → Type) → PhoasD V → Type
-- [PhoasD]₁ V Vdot (vvar v) = Vdot v
-- [PhoasD]₁ V Vdot (vapp u w) = [PhoasD]₁ V Vdot u × [PhoasD]₁ V Vdot w
-- [PhoasD]₁ V Vdot (vlam f) = ∀ v → Vdot v → [PhoasD]₁ V Vdot (f v)

-- technically the unary translation is rather this indexed data type
data [PhoasD]₁real (V : Type) (Vdot : V → Type) : PhoasD V → Type where
  vvardot : ∀ v → Vdot v → [PhoasD]₁real V Vdot (vvar v)
  vappdot : ∀ u w → [PhoasD]₁real V Vdot u → [PhoasD]₁real V Vdot w → [PhoasD]₁real V Vdot (vapp u w)
  vlamdot : ∀ (f : V → PhoasD V) → (fdot : ∀ v → Vdot v → [PhoasD]₁real V Vdot (f v)) → [PhoasD]₁real V Vdot (vlam f)


module _ (V : Type) (Vdot : V → Type) where

  toreal : ∀ (t : PhoasD V) → [PhoasD]₁ V Vdot t → [PhoasD]₁real V Vdot t
  toreal (vvar v) vdot = vvardot v vdot
  toreal (vapp a b) abdot = vappdot a b (toreal a (abdot .fst)) (toreal b (abdot .snd))
  toreal (vlam f) fdot = vlamdot f λ v vdot → toreal (f v) (fdot v vdot)

  fromreal : ∀ (t : PhoasD V) → [PhoasD]₁real V Vdot t → [PhoasD]₁ V Vdot t
  fromreal .(vvar v) (vvardot v vdot) = vdot
  fromreal .(vapp u w) (vappdot u w udot wdot) = fromreal u udot , fromreal w wdot
  fromreal .(vlam f) (vlamdot f fdot) = λ v vdot → fromreal (f v) (fdot v vdot)

  fake<= : ∀ (t : PhoasD V) (tdot : [PhoasD]₁ V Vdot t) → fromreal t (toreal t tdot) ≡ tdot
  fake<= (vvar v) tdot = refl
  fake<= (vapp a b) tdot = ≡-× (fake<= a (tdot .fst)) (fake<= b (tdot .snd))
  fake<= (vlam f) tdot = funExt λ v → funExt λ vdot →
    fake<= (f v) (tdot v vdot)

  real<= : ∀ (t : PhoasD V) (tdot : [PhoasD]₁real V Vdot t) →
    toreal t (fromreal t tdot) ≡ tdot
  real<= .(vvar v) (vvardot v vdot) = refl
  real<= .(vapp a b) (vappdot a b adot bdot) = cong₂ (vappdot a b) (real<= a (adot)) (real<= b (bdot))
  real<= .(vlam f) (vlamdot f fdot) = cong (vlamdot f) (funExt λ v → funExt λ vdot →
    real<= (f v) (fdot v vdot))

[PhoasD]₁real-≃ : (V : Type) (Vdot : V → Type) (t : PhoasD V) → [PhoasD]₁ V Vdot t ≃ [PhoasD]₁real V Vdot t
[PhoasD]₁real-≃ V Vdot t = isoToEquiv (iso
  (toreal _ _ t)
  (fromreal _ _ t)
  (real<= _ _ t)
  (fake<= _ _ t))
