{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
module OldReflexiveGraphs where

open import BridgePrims
open import GelExamples
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty

-- standard reflexive graphs are not needed for now. see later NativeReflexiveGraph module instead.
module ReflexiveGraph where

  -- a type class for reflexive graphs
  record HasRGraph {ℓ : Level} (A : Type ℓ) : Type (ℓ-suc ℓ) where
    field
      edge : A → A → Type ℓ
      grefl : (a : A) → edge a a
    -- syntax edge self a b = self ⟦ a , b ⟧    does not work in instance arg setting (problem: self)
  open HasRGraph ⦃...⦄ public

  -- smart packed version
  record RGraph {ℓ : Level} : Type (ℓ-suc ℓ) where
    constructor mkRGraph
    field
      obj : Type ℓ
      ⦃ hasrg ⦄ : HasRGraph obj -- note the spaces ⦃ ⦄



  instance
    topHasRG : HasRGraph ⊤
    topHasRG = record { edge = λ _ _ → ⊤
                         ; grefl = λ _ → tt
                         }
  topRG : RGraph
  topRG = mkRGraph ⊤

  instance
    TypeHasRG : ∀ {ℓ : Level} → HasRGraph (Type ℓ)
    TypeHasRG = record { edge = λ A B → A → B → (Type _)  ; grefl = λ A a b → a ≡ b }

  TypeRG : ∀ (ℓ : Level) → RGraph
  TypeRG ℓ = mkRGraph (Type ℓ)


  -- type can be endowed with a discrete RG structure
  -- this RG is not native!
  -- instance
  --   TypeHasRG' : ∀ {ℓ : Level} → HasRGraph (Type ℓ)
  --   TypeHasRG' = record { edge = λ A B → A ≡ B ; grefl = λ _ → refl }


  -- the left adjoint, discrete-RG functor from Type → RG
  mkDiscreteRG : ∀ {ℓ : Level} → (A : Type  ℓ) → HasRGraph A
  mkDiscreteRG A = record { edge = λ a b → a ≡ b ; grefl = λ _ → refl }

  -- the right adjoint, forgetting the edge sets from RG → Type
  forgRG : ∀ {ℓ : Level} (A : Type ℓ) {{hrgA : HasRGraph A}} → (Type ℓ)
  forgRG A = A



  -- The collection of small reflexive graphs (RGraph {ℓ = ℓ}) should be a reflexive graph itself.
  -- We first define a type of logical relations between two reflexive graphs G H : RG ℓ
  -- Such logical rels are basically the fully relational version of a functor btw categories
  record RG-logrel {ℓ} (G : Type ℓ) (H : Type ℓ) {{hrgG : HasRGraph G}} {{hrgH : HasRGraph H}} : Type (ℓ-suc ℓ) where
    field
      objrel : G → H → Type ℓ
      edgerel : ∀ (g g' : G) (h h' : H) (gh : objrel g h) (gh' : objrel g' h') → edge g g' → edge h h' → Type ℓ
      greflrel : ∀ (g : G) (h : H) → (gh : objrel g h) → edgerel g g h h gh gh (grefl g) (grefl h)

  instance
    RGHasRG : ∀ {ℓ : Level} → HasRGraph ( RGraph {ℓ = ℓ} )
    RGHasRG = record { edge = λ _@(mkRGraph G) _@(mkRGraph H) → RG-logrel G H
                     ; grefl = λ _@(mkRGraph G) →
                         record { objrel = λ g h → g ≡ h
                                ; edgerel = λ g g' h h' gh gh' gg' hh' → transport (λ i → edge (gh i) (gh' i)) gg' ≡ hh'
                                ; greflrel = λ g h gh → fromPathP λ i → grefl (gh i) } }
