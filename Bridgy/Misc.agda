{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}
-- -v tc.conv.term:40  -v tc.conv.pathbdg:20 -v tc.conv.atom:50 -v tc.conv.elim:25 -v tc.infer.internal:30 

module Misc where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.GelExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma using ( ΣPath≃PathΣ ; _×_ )
open import Cubical.Data.List


-- yay : ∀ {ℓ} (A  B : Type ℓ) (e : A ≃ B) (a : A) (b : B) →
--           isProp (equivFun e a ≡ b)
-- yay A B e a b p q =
--   let a',r = e .snd .equiv-proof b
--       ≡a,p = a',r .snd (a , p)
--       a,q≡ = sym (a',r .snd (a , q))
--   in
--   {!J (λ !}


-- invEq ΣPath≃PathΣ (a,q≡ ∙ ≡a,p)


-- e .snd .equiv-proof b



-- data myEq {ℓ} (A : Type ℓ) (a0 : A) : A → Set ℓ where
--   myrefl : myEq A a0 a0

-- data myEq' {ℓ} (A : Type ℓ) : A → A → Set ℓ where
--   myrefl' : (a0 : A) → myEq' A a0 a0


-- record myEd {ℓ} (A : Type ℓ) (a0 : A) : A → Type ℓ where
--   coinductive
--   field
--     myrfl : myEd A a0 a0



-- a coinduction pcpl for the Bdg type family?
-- bdg-coind : ∀ {ℓ} {A : Type ℓ}
--   (Ed : A → A → Type ℓ) (edrfl : (a0 : A) → Ed a0 a0) →
--   isContr( Σ (∀ a0 a1 → Ed a0 a1 → BridgeP (λ x → primGel A A Ed x) a0 a1)
--              (λ f → ∀ a0 → f a0 a0 (edrfl a0) ≡ (λ _ → a0)))
-- bdg-coind Ed edrfl =
--   ((λ a0 a1 e → {!λ x → prim^gel {R = Ed} a0 a1 e x!}) ,
--     {!!}) ,
--   {!!}




data Wrap {ℓ} (A : Type ℓ) : Type ℓ where
  gv : A → Wrap A

proj : ∀ {ℓ} {A : Type ℓ} (w : Wrap A) → A
proj (gv a) = a

gv-proj : ∀ {ℓ} {A : Type ℓ} w → Path (Wrap A) (gv (proj w))  w
gv-proj (gv a) = refl

module WrapvsBridge {ℓ} (A : Type ℓ) where

  _~Wrap_ : Wrap A → Wrap A → Type ℓ
  _~Wrap_ (gv a0) (gv a1) = BridgeP (λ _ → A) a0 a1

  -- ~Wrap → Bridge
  loosenWrap : ∀ w0 w1 → (w0 ~Wrap w1) → BridgeP (λ _ → Wrap A) w0 w1
  loosenWrap (gv a0) (gv a1) = λ aa x → gv (aa x)

  naiveTightenWrap : ∀ w0 w1 → BridgeP (λ _ → Wrap A) w0 w1 → (w0 ~Wrap w1)
  naiveTightenWrap (gv a0) (gv a1) ww =
    λ x → proj (ww x)

  -- not sure the proof goes through for more complex inductives
  naiveWrapvsBridge : ∀ w0 w1 → (w0 ~Wrap w1) ≃ (BridgeP (λ _ → Wrap A) w0 w1)
  naiveWrapvsBridge (gv a0) (gv a1) = isoToEquiv (iso
    (loosenWrap _ _)
    (naiveTightenWrap _ _)
    (λ ww → invEq (PathPvsBridgeP (λ _ _ → Wrap A) {a00 = gv a0} {a10 = gv a1} {a01 = gv a0} {a11 = gv a1})
      λ x → gv-proj (ww x))
      λ prf → refl)

  -- tightenWrap would be
  -- (BridgeP (λ _ → Wrap A) w0 w1) → (w0 ~Wrap w1)
  -- instead we define this at Gel'ed domain/codmain
  -- x:BI → (primGel _ _ (BridgeP (λ _ → Wrap A)) x) → (primGel _ _ (_~Wrap_) x)
  -- By 1 relativity retract proof, the domain is Wrap A.
  -- hence we must build tightenWrap0 : x:BI → Wrap A → (primGel _ _ (_~Wrap_) x) by induction
  -- hence we want a Wrap algebra for (primGel _ _ (_~Wrap_) x) 

  gvx : (@tick x : BI) → A → (primGel _ _ (_~Wrap_) x)
  gvx x a =
    -- the naive thing does not work because of freshness. → use extent
    -- prim^gel {R = (_~Wrap_)} (gv a) (gv a) (λ _ → a) x
    primExtent {A = λ _ → A} {B = λ x _ → (primGel _ _ (_~Wrap_) x)}
    gv gv
    (λ a0 a1 aa y → prim^gel {R = (_~Wrap_)} (gv a0) (gv a1) aa y)
    x
    a

  -- simply speaking gvx is a bridge btw the gv and gv constructors.
  gvx' : BridgeP (λ x → A → (primGel _ _ (_~Wrap_) x)) gv gv
  gvx' x a =
    -- the naive thing does not work because of freshness. → use extent
    -- prim^gel {R = (_~Wrap_)} (gv a) (gv a) (λ _ → a) x
    primExtent {A = λ _ → A} {B = λ x _ → (primGel _ _ (_~Wrap_) x)}
    gv gv
    (λ a0 a1 aa y → prim^gel {R = (_~Wrap_)} (gv a0) (gv a1) aa y)
    x
    a 


  -- those two are defined by induction
  tightenWrap0 : (@tick x : BI) → Wrap A → (primGel _ _ (_~Wrap_) x)
  tightenWrap0 x (gv a) = gvx' x a

  tightenWrap : ∀ w0 w1 → (BridgeP (λ _ → Wrap A) w0 w1) → (w0 ~Wrap w1)
  tightenWrap (gv a0) (gv a1) ww = prim^ungel {R = _~Wrap_} (λ x → tightenWrap0 x (ww x))

  -- bdgRetAux : (@tick x : BI) → (w : Wrap A) → 

  -- WrapvsBridge : ∀ w0 w1 → (w0 ~Wrap w1) ≃ (BridgeP (λ _ → Wrap A) w0 w1)
  -- WrapvsBridge (gv a0) (gv a1) = isoToEquiv (iso
  --   (loosenWrap (gv a0) (gv a1))
  --   (tightenWrap (gv a0) (gv a1))
  --   (λ ww → {!!})
  --   {!!})



ListRCover' : ∀ {ℓ} (A0 A1 : Type ℓ) (R : A0 → A1 → Type ℓ) → List A0 → List A1 → Type ℓ
ListRCover' A0 A1 R [] [] = Lift Unit
ListRCover' A0 A1 R [] (_ ∷ _) = Lift ⊥
ListRCover' A0 A1 R (_ ∷ _) [] = Lift ⊥
ListRCover' A0 A1 R (a0 ∷ as0) (a1 ∷ as1) = R a0 a1 × ListRCover' A0 A1 R as0 as1

module BridgeAtList {ℓ} {A : Type ℓ} where

  -- as0 [ListRCover A] as1 iff as0, as1 have similar structure and
  -- we have bdgs between each entries of the list
  _~List_ : List A → List A → Type ℓ
  _~List_ = ListRCover' A A (BridgeP (λ _ → A))

  loosenList : ∀ as0 as1 → as0 ~List as1 → BridgeP (λ _ → List A) as0 as1
  loosenList [] [] = λ _ → (λ _ → [])
  loosenList [] (_ ∷ _) = λ ctr → rec (ctr .lower)
  loosenList (_ ∷ _) [] = λ ctr → rec (ctr .lower)
  loosenList (hd0 ∷ tl0) (hd1 ∷ tl1) = λ hd-tll → λ x → (hd-tll .fst x) ∷  loosenList _ _ (hd-tll .snd) x


  naiveTightenList : ∀ as0 as1 → BridgeP (λ _ → List A) as0 as1 → (as0 ~List as1)
  naiveTightenList [] [] = λ _ → lift tt
  naiveTightenList [] (hd ∷ tl) q = {!!}
  naiveTightenList _ _ = {!!}


--   -- The bridge at Type corresponding to the above relation λ as0 as1 → as0 [_~List_ A] as1
--   -- asBdg : BridgeP (λ _ → Type ℓ) (List A) (List A)
--   -- asBdg = λ x → primGel (List A) (List A) (_~List_) x

--   -- nil "constructor" for primGel _ _ _~List_ x
--   nilx : (@tick x : BI) → primGel _ _ (_~List_) x
--   nilx x = prim^gel [] [] _ x

--   -- cons "constructor" for primGel _ _ (_~List_) x
--   consx : (@tick x : BI) →
--           (primGel A A (BridgeP (λ _ → A)) x) → -- "hd"
--           (primGel (List A) (List A) (_~List_) x) → -- "tl"
--           (primGel (List A) (List A) (_~List_) x)
--   consx x ghd gtl =  -- ghd, gtl implicitly depend on x
--     {!!}

--     -- primExtent
--     -- {A = λ x → primGel A A (BridgeP (λ _ → A)) x}
--     -- {B = λ x a → primGel (List A) (List A) (_~List_) x} {!!} {!!}
--     --     -- goal is now reduced to (hd:A) (gtl: Gel_x _~List_) → Gel_x _~List_
--     --     (λ hd0 hd1 ghdd y →
--     --     {!primExtent
--     --     {A = λ y → primGel _ _ _~List_ y}
--     --     {B = λ y t → primGel _ _ _~List_ y} ? ?
--     --     ?
--     --     x
--     --     gtl!})
--     -- x
--     -- ghd




--   -- -- we obtain a function Bridge_ListA ? ? → _~List_ ? ?
-- --   -- by ungelling tighten0
-- --   tighten0 :  List A → (@tick x : BI) → primGel (List A) (List A) _~List_ x
-- --   tighten0 [] x = prim^gel [] [] _ x
-- --   -- the encoding of the (hd ∷ _) function on (primGel _ _ (_~List_) x)    (for hd, x fixed).
-- --   -- ie we seek a "hd-consing" function (primGel _ _ (_~List_) x) → (primGel _ _ (_~List_) x)
-- --   -- It is obtained by first building a bdg btw hd‌∷_ and hd∷ _ (with extent) and second x to this bdg.
-- --   tighten0 (hd ∷ tl) x =
-- --     primExtent {A = λ x → primGel (List A) (List A) _~List_ x} {B = λ x a → primGel (List A) (List A) _~List_ x}
-- --      (λ atl → hd ∷ atl)
-- --      (λ atl → hd ∷ atl)
-- --      (λ ts0 ts1 tss → λ y → prim^gel {R = _~List_} (hd ∷ ts0) (hd ∷ ts1) ( (λ _ → hd) , prim^ungel {R = _~List_} (λ z → tss z) ) y )
-- --      x
-- --      (tighten0 tl x)

-- --   ListvsBridge0 : ∀ as0 as1 → _~List_ as0 as1 ≃ BridgeP (λ _ → List A) as0 as1
-- --   ListvsBridge0 as0 as1 = isoToEquiv (iso
-- --     (loosen as0 as1)
-- --     (λ q → {!prim^ungel {R = _~List_} (λ x → tighten0 (q x) x)!}) {!!} {!!})

-- -- --  y → prim^gel {R = _~List_} (hd ∷ tl) (hd ∷ tl) ( (λ _ → hd) , {!prim^ungel {R = _~List_} (λ z → tss z)!} ) y
-- -- -- prim^ungel {R = _~List_} (λ z → tss z)
-- -- -- primExtent {A = λ _ → List A} {B = λ x _ → primGel (List A) (List A) _~List_ x}
-- -- --                            (λ _ → hd ∷ tl) (λ _ → hd ∷ tl)

-- --   -- nil nil case.
-- --   loosenNilNil : _~List_ [] [] → BridgeP (λ _ → List A) [] []
-- --   loosenNilNil _ = λ _ → []



-- --   -- BI-indexed family of "constructors"


-- --   -- consx : (@tick x : BI) (hd : A) (tl : List A) → asBdg x
-- --   -- consx x hd tl = {!prim^gel!}

-- --   -- listTighten : (@tick x : BI) → List A → primGel (List A) (List A) (_~List_) x
-- --   -- listTighten x [] = prim^gel [] [] _ x
-- --   -- listTighten x (hd ∷ tl) = {!primExtent {A = λ _ → A} {B = λ x _ → primGel (List A) (List A) _~List_ x}
-- --   --                             !}

-- --   -- primExtent : ∀ {ℓA ℓB : Level} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) (a : A x) → Type ℓB}
-- --   --              (N0 : (a0 : A bi0) → B bi0 a0)
-- --   --              (N1 : (a1 : A bi1) → B bi1 a1)
-- --   --              (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1))
-- --   --              (@tick r : BI) (M : A r) →
-- --   --              B r M

