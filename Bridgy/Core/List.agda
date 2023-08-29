{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}

module Bridgy.Core.List where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BridgeExamples
open import Bridgy.Core.ExtentExamples
open import Bridgy.Core.GelExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using ( ΣPath≃PathΣ ; _×_ ; ΣPathP )
open import Cubical.Data.List
open import Cubical.Foundations.Function

-- This file proves the ListvsBridgeP commutation principle.




-- We begin with a simple example of bdg commutation principle for an inductive

module WrapExample where

  data Wrap {ℓ} (A : Type ℓ) : Type ℓ where
    gv : A → Wrap A

  projw : ∀ {ℓ} {A : Type ℓ} (w : Wrap A) → A
  projw (gv a) = a

  gv-projw : ∀ {ℓ} {A : Type ℓ} w → Path (Wrap A) (gv (projw w))  w
  gv-projw (gv a) = refl

  module WrapvsBridge {ℓ} (A : Type ℓ) where

    -- STEP1: define observational similarity for the inductive of interest, by induction.
    _~Wrap_ : Wrap A → Wrap A → Type ℓ
    _~Wrap_ (gv a0) (gv a1) = BridgeP (λ _ → A) a0 a1

    -- STEP2: define loosen : bisim → Bridge by induction
    -- ~Wrap → Bridge
    loosenWrap : ∀ w0 w1 → (w0 ~Wrap w1) → BridgeP (λ _ → Wrap A) w0 w1
    loosenWrap (gv a0) (gv a1) = λ aa x → gv (aa x)

    -- this section works only for this simple Wrap inductive
    naiveTightenWrap : ∀ w0 w1 → BridgeP (λ _ → Wrap A) w0 w1 → (w0 ~Wrap w1)
    naiveTightenWrap (gv a0) (gv a1) ww =
      λ x → projw (ww x)

    -- this section proofs works only for this simple Wrap inductive
    naiveWrapvsBridge : ∀ w0 w1 → (w0 ~Wrap w1) ≃ (BridgeP (λ _ → Wrap A) w0 w1)
    naiveWrapvsBridge (gv a0) (gv a1) = isoToEquiv (iso
      (loosenWrap _ _)
      (naiveTightenWrap _ _)
      (λ ww → invEq (PathPvsBridgeP (λ _ _ → Wrap A) {a00 = gv a0} {a10 = gv a1} {a01 = gv a0} {a11 = gv a1})
        λ x → gv-projw (ww x))
        λ prf → refl)

    -- STEP3: For I inductive, x:BI, equip (primGel I I bisim x) with an I algebra structure.
    --        This is ≈equivalent to building bridges btw constructors
    -- In our case, a wrap algebra.
    -- alternate phrasing for the type is BridgeP (λ x → A → (primGel _ _ (_~Wrap_) x)) gv gv
    -- for more complex inductive, it may be necessary to rewrite such terms : (@tick x : BI) → ...
    -- as bridges, in order to specify the endpoints and gain the bridge boundary equations.
    gvx : (@tick x : BI) → A → (primGel _ _ (_~Wrap_) x)
    gvx x a =
      -- the naive thing does not work because of freshness. → use extent
      -- prim^gel {R = (_~Wrap_)} (gv a) (gv a) (λ _ → a) x
      primExtent {A = λ _ → A} {B = λ x _ → (primGel _ _ (_~Wrap_) x)}
      gv gv
      (λ a0 a1 aa y → prim^gel {R = (_~Wrap_)} (gv a0) (gv a1) aa y)
      x
      a


    -- STEP4: define I → (Gel_x bisim_I) by induction
    -- using the above I algebra structure on (Gel_x bisim_I)
    tightenWrap0 : (@tick x : BI) → Wrap A → (primGel _ _ (_~Wrap_) x)
    tightenWrap0 x (gv a) = gvx x a

    -- STEP5: apply the ""Bridge functor"" to the above arrow to get
    --        BridgeP (λ _ → I) i0 i1 → i0 bisim_I i1
      --      the codomain is path equal to BridgeP (λ x → Gel_x bisim_I) i0 i1 by relativity.
    tightenWrap : ∀ w0 w1 → (BridgeP (λ _ → Wrap A) w0 w1) → (w0 ~Wrap w1)
    tightenWrap (gv a0) (gv a1) ww = prim^ungel {R = _~Wrap_} (λ x → tightenWrap0 x (ww x))

    -- STEP6: some extent magic... part of final retract proof
    -- bdgRetAux : (@tick x : BI) → (w : Wrap A) → extent (loosen ∘ tighten) x w ≡ w
    bdgRetAux : (@tick x : BI) → (w : Wrap A) →
      (primExtent {A = λ _ → Wrap A} {B = λ _ _ → Wrap A} _ _
          (λ w0 w1 ww → loosenWrap w0 w1 (tightenWrap w0 w1 ww))
          x
          w)
      ≡
          w
    bdgRetAux x (gv a) =
      -- casing by extent to show that a fully applied bdg is extent
      primExtent
        {B = λ x a → (primExtent (λ a0 → a0) (λ a1 → a1)
                      (λ w0 w1 ww → loosenWrap w0 w1 (tightenWrap w0 w1 ww)) x (gv a))
                      ≡ gv a}
        (λ _ → refl) (λ _ → refl)
        (λ a0 a1 aa y → refl)
        x a

    -- STEP7: the other retract proof goes by refl.
    WrapvsBridge : ∀ w0 w1 → (w0 ~Wrap w1) ≃ (BridgeP (λ _ → Wrap A) w0 w1)
    WrapvsBridge (gv a0) (gv a1) = isoToEquiv (iso
      (loosenWrap (gv a0) (gv a1))
      (tightenWrap (gv a0) (gv a1))
      (λ ww → invEq (PathPvsBridgeP _ {a00 = gv a0} {a10 = gv a1} {a01 = gv a0} {a11 = gv a1}) λ x →
        (bdgRetAux x (ww x)))
      λ sim → refl)



{-

  Bdg commutation principle for lists.
  Functions that have type f : ∀ (@tick x : BI) → ...
  can be declared as bridges. this way we gain equations f bi0 = ..., f bi1 = ...
  Moreover f can be defined using bdg commutation principles (no direct reference to extent eg)

-}

ListRCover : ∀ {ℓ} {A0 A1 : Type ℓ} (R : A0 → A1 → Type ℓ) → List A0 → List A1 → Type ℓ
ListRCover R [] [] = Lift Unit
ListRCover R [] (_ ∷ _) = Lift ⊥
ListRCover R (_ ∷ _) [] = Lift ⊥
ListRCover R (a0 ∷ as0) (a1 ∷ as1) = R a0 a1 × ListRCover R as0 as1

[List_] : ∀ {ℓ} {A0 A1 : Type ℓ} (R : A0 → A1 → Type ℓ) → List A0 → List A1 → Type ℓ
[List_] R = ListRCover R



-- dependent bdg commutation pcpl for the List type former
-- see ListvsBridgeP theorem
module ListvsBridgeP {ℓ} {A0 A1 : Type ℓ} (AA : BridgeP (λ _ → Type ℓ) A0 A1) where

  -- STEP1: define heterogeneous bisimilarity for lists
  _~List_ : List A0 → List A1 → Type ℓ
  _~List_ = [List (BridgeP (λ x → AA x)) ]

  -- STEP2: define loosen : bisim → Bridge by induction
  loosenList : ∀ as0 as1 → (as0 ~List as1) → BridgeP (λ x → List (AA x)) as0 as1
  loosenList [] [] = λ _ → (λ _ → [])
  loosenList [] (_ ∷ _) = λ ctr → rec (ctr .lower)
  loosenList (_ ∷ _) [] = λ ctr → rec (ctr .lower)
  loosenList (hd0 ∷ tl0) (hd1 ∷ tl1) = λ hd-tll → λ x → (hd-tll .fst x) ∷  loosenList _ _ (hd-tll .snd) x

  -- STEP3: For I inductive, x:BI, equip (primGel I I bisim x) with an I algebra structure.
  --        This is ≈equivalent to building bridges btw constructors
  nilx : BridgeP (λ x → primGel (List A0) (List A1) (_~List_) x) [] []
  nilx x = prim^gel [] [] _ x

  consx : BridgeP (λ x → (AA x) → primGel _ _ (_~List_) x → primGel _ _ (_~List_) x) _∷_ _∷_
  consx =
    equivFun (ΠvsBridgeP) λ hd0 hd1 hdd →
    equivFun (ΠvsBridgeP) λ tl0 tl1 tll →
    λ x → prim^gel {R = _~List_} (hd0 ∷ tl0) (hd1 ∷ tl1) (hdd , prim^ungel {R = _~List_} (λ y → tll y)) x


  -- STEP4: define I → (Gel_x bisim_I), for x fixed, by induction
  tightenList0 : BridgeP (λ x → (List (AA x)) → primGel _ _ (_~List_) x) (idfun (List A0)) (idfun (List A1))
  tightenList0 x [] = nilx x
  tightenList0 x (hd ∷ tl) = consx x hd (tightenList0 x tl)

  -- STEP5: ungel step 4
  tightenList : ∀ as0 as1 → BridgeP (λ x → List (AA x)) as0 as1 → (as0 ~List as1)
  tightenList as0 as1 aas = prim^ungel (λ x → tightenList0 x (aas x))

  -- STEP6: auxiliary  proof for retract proof (see auxlisteq)
  -- we define a "dependent algebra" structure for `apred x` (x :BI fixed).
  -- then `auxlisteq : ∀ x as, apred x as` is defined by induction.
  apred : (@tick x : BI) (as : List (AA x)) → Type ℓ
  apred x as = (primExtent (idfun _) (idfun _) (λ as0 as1 → loosenList as0 as1 ∘ tightenList as0 as1) x as) ≡ as

  apred-nilx : BridgeP (λ x → apred x []) (refl) (refl)
  apred-nilx x = refl

  apred-consx : BridgeP
    (λ x → (hd : (AA x)) (tl : List (AA x)) → (apred x tl) → apred x (hd ∷ tl))
    (λ hd tl → (cong (_∷_ hd))) (λ hd tl → (cong (_∷_ hd)))
  apred-consx =
    equivFun (ΠvsBridgeP) (λ hd0 hd1 hdd →
    equivFun (ΠvsBridgeP) (λ tl0 tl1 tll x →
    (cong (_∷_ (hdd x)))))

  auxlisteq : BridgeP
    ((λ x → (as : List (AA x)) →
      (primExtent (idfun _) (idfun _) (λ as0 as1 → loosenList as0 as1 ∘ tightenList as0 as1) x as) ≡ as))
    (λ _ → refl) (λ _ → refl)
  auxlisteq x [] = apred-nilx x
  auxlisteq x (hd ∷ tl) = apred-consx x hd tl (auxlisteq x tl)

  auxsec : ∀ as0 as1 (sim : as0 ~List as1) → tightenList as0 as1 (loosenList as0 as1 sim) ≡ sim
  auxsec [] [] (lift tt) = refl
  auxsec [] (_ ∷ _) ctr = rec (ctr .lower)
  auxsec (_ ∷ _) [] ctr = rec (ctr .lower)
  auxsec (hd0 ∷ tl0) (hd1 ∷ tl1) (hdd , simtl) = ΣPathP (refl , auxsec tl0 tl1 simtl)

  ListvsBridgeP : ∀ {as0 : List A0} {as1 : List A1} → (as0 ~List as1) ≃ (BridgeP (λ x → List (AA x)) as0 as1)
  ListvsBridgeP {as0} {as1} = isoToEquiv (iso
    (loosenList as0 as1)
    (tightenList as0 as1)
    (λ aas → λ i x → auxlisteq x (aas x) i)
    (auxsec as0 as1))

open ListvsBridgeP public using ( ListvsBridgeP )

ListvsBridge : ∀ {ℓ} {A : Type ℓ} {as0 as1 : List A} →
  ( [List (BridgeP (λ _ → A)) ] as0 as1 ) ≃ (BridgeP (λ _ → List A) as0 as1)
ListvsBridge {A = A} {as0 = as0} {as1 = as1} =
  (ListvsBridgeP {A0 = A} {A1 = A} (λ x → A) {as0 = as0} {as1 = as1})
