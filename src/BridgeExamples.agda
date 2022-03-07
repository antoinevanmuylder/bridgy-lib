{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-} -- -v tc.constr:60 -v tc.conv:50 -v tc.cover.iapply:40 -v tc.iapply:40 -v tc.conv.face:40 -v tc.conv.bridgeface:40 -v conv.forall:40
module BridgeExamples where

open import BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_×_)
open import Agda.Builtin.Unit

------------------------------------------------------------------------
-- cubical lemmas
------------------------------------------------------------------------

switchEquivEq : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (I : A ≃ B)
                (a : A) (b : B) → (I .fst a ≡ b) → (invEq I b ≡ a)
switchEquivEq I a b prf = sym (sym (retEq I a) ∙ cong (invEq I) prf)


------------------------------------------------------------------------
-- about bridges
------------------------------------------------------------------------

-- module testCubicalInterval {ℓ} {A : (i : I) → Type ℓ} {a0 : A i0} {a1 : A i1}
--                            {B : Type ℓ} {b0 b1 : B} where

--   mk-path : (f : (i : I) → A i)  → PathP A (f i0) (f i1)
--   mk-path f i = {!!}

module PlayBridgeP {ℓ} {A : (@tick x : BI) → Type ℓ} {a0 : A bi0} {a1 : A bi1}
                   {B : Type ℓ} {b0 b1 : B} where

  -- INTRO RULE
  -- need f : (i:BI) → A i such that p 0 = a0,  p 1 = a1 definitionally.
  mk-bridge : (f : (@tick i : BI) → A i) → BridgeP A (f bi0) (f bi1)
  mk-bridge f = λ i → f i


  mmk : (f : (@tick i : BI) → A i) → BridgeP A (f bi0) (f bi1)
  mmk f x = f x

  -- -- endpoints failure:
  -- fail-cstbridge : BridgeP (λ i → Bool) false true
  -- fail-cstbridge = λ i → false


  -- ELIM RULE
  destr-bdg : (P : BridgeP A a0 a1) (@tick r : BI) → A r
  destr-bdg P r = P r

  -- -- affineness cstr:
  -- no-destr-bdg : (@tick r : BI) (P : BridgeP A a0 a1) → A r
  -- no-destr-bdg r P = P r

  -- BOUNDARY rule
  boundary-bdg : (p : BridgeP (λ i → B) b0 b1) → p bi0 ≡ b0
  boundary-bdg p = λ i → b0

  -- ETA COMPUTATION RULE
  eta-bdg : (p : BridgeP (λ r → A r) a0 a1) → p ≡ (λ r → p r)
  eta-bdg p i = p

  -- ~BETA COMPUTATION RULE. cannot easily state it internally
  beta-bdg : (f : (@tick i : BI) → A i) (@tick r : BI) → mk-bridge f r ≡ f r
  beta-bdg f r j = f r

-- below, even if B is a cartesian Pi type (which is unsound to assume),
-- λ k → p k k does not typecheck.
-- module BridgeDiag  {ℓ} {B : (@tick i j : BI) → Type ℓ}
--                    {b00 : B bi0 bi0} {b10 : B bi1 bi0} {b01 : B bi0 bi1} {b11 : B bi1 bi1}
--                    {left : BridgeP (λ j → B bi0 j) b00 b01} {right : BridgeP (λ j → B bi1 j) b10 b11}
--                    {down : BridgeP (λ i → B i bi0) b00 b10} {up : BridgeP (λ i → B i bi1) b01 b11} where

--   -- no diag for bridge vars
--   bdg-diag : BridgeP (λ i →  BridgeP (λ j → B i j) (down i) (up i) )   left    right →
--              BridgeP (λ k → B k k) b00 b11
--   bdg-diag p = λ k → p k k

  -- p ⊢ p
  -- p , k ⊢ p                                   constraints k ∉ p                OK
  -- p : bdg-bdg-t, k : BI ⊢ p k : bdg-t         constraints k ∉ p k              hopefully affine constr gets gen
  -- p : bdg-bdg-t, k : BI ⊢ (p k) k : bdg-t     endpoint cstr
  -- p : bdg-bdg-t ⊢ λ k → p k k : bdg-t
  -- ⊢ λ p k → p k k : bdg-bdg-t → bdg-t



  
-- -- BRIDGES VS BRIDGES (relational extensionality for bridges)
-- -- the exchange rule should hold for bridge vars
module BridgeVBridge {ℓ} (BB : (@tick i j : BI) → Type ℓ) (a : (@tick i j : BI) → BB i j) where


--   -- we compare the types of λ i j → a i j and λ j i → a i j and
--   -- try to establish an equiuvalence between them

--   -- i left to right. j bottom to top
--   -- ----------
--   -- |        |
--   -- |        |
--   -- |        |
--   -- ----------


--   -- λ i j → a i j is a bridge between the left side and the right side of the above square.
  laij : BridgeP
         (λ i →  BridgeP (λ j → BB i j) (a i bi0)  (a i bi1))
         (λ j → a bi0 j)
         (λ j → a bi1 j)
  laij = λ i j → a i j

  -- λ j i → a i j is a bridge between the bottom side and the top side of the above square.
  laji : BridgeP
         (λ j →  BridgeP (λ i → BB i j) (a bi0 j)  (a bi1 j))
         (λ i → a i bi0)
         (λ i → a i bi1)
  laji = λ j i → a i j

--   -- this should work!
  exch-bdg :
   BridgeP (λ x →  BridgeP (λ y → BB x y) (a x bi0)  (a x bi1)) (λ y → a bi0 y) (λ y → a bi1 y) →
   BridgeP (λ y →  BridgeP (λ x → BB x y) (a bi0 y)  (a bi1 y)) (λ x → a x bi0) (λ x → a x bi1)
  exch-bdg p = λ y x → p x y

  exch-bdg' :
    BridgeP (λ y →  BridgeP (λ x → BB x y) (a bi0 y)  (a bi1 y)) (λ x → a x bi0) (λ x → a x bi1) → 
    BridgeP (λ x →  BridgeP (λ y → BB x y) (a x bi0)  (a x bi1)) (λ y → a bi0 y) (λ y → a bi1 y)
  exch-bdg' p = λ x y → p y x

--   -- one inverse condition of the bdg versus bdg principle
  bdgVbdg : ∀ p →  p ≡ (exch-bdg' (exch-bdg p) )
  bdgVbdg p = λ i → p

--   -- the other one:
  bdgVbdg' : ∀ p → p ≡ (exch-bdg (exch-bdg' p))
  bdgVbdg' p = λ i → p




-- BRIDGES vs PATHS
module BridgePPathP {ℓ} (A : (@tick x : BI) → I → Type ℓ)
                   {a00 : A bi0 i0} {a10 : A bi1 i0} {a01 : A bi0 i1} {a11 : A bi1 i1}
                   (left : PathP (λ i → A bi0 i) a00 a01) (right : PathP (λ i → A bi1 i) a10 a11)
                   {down : BridgeP (λ x → A x i0) a00 a10} {up : BridgeP (λ x → A x i1) a01 a11} where

  --         up x
  --       ---->-----
  --       |        |
  --left i |        |right i
  --       |        |
  --       ---->-----
  --         down x
  -- 
  --   ^ i:I
  --   |
  --   -- > x : BI

  -- to make a path between the bridges down and up, you need a bridge of paths between left and right
  -- usage bridgePPathP _A _left _right 
  bridgePPathP : BridgeP (λ x → PathP (λ i → A x i) (down x) (up x)) left right →
                 PathP (λ i → BridgeP (λ x → A x i) (left i) (right i)) down up
  bridgePPathP q = λ i x → q x i


module _ {ℓ} {A : (@tick x : BI) → Type ℓ} {a0 : A bi0} {a1 : A bi1}
                   {down up : BridgeP A a0 a1} where

  bridgePPath : BridgeP (λ x → down x ≡ up x) refl refl →
                 down ≡ up
  bridgePPath q = λ i x → q x i


module PathPBridgeP {ℓ} (A : (@tick x : BI) → I → Type ℓ)
                   {a00 : A bi0 i0} {a10 : A bi1 i0} {a01 : A bi0 i1} {a11 : A bi1 i1}
                   {left : PathP (λ i → A bi0 i) a00 a01} {right : PathP (λ i → A bi1 i) a10 a11}
                   (down : BridgeP (λ x → A x i0) a00 a10) (up : BridgeP (λ x → A x i1) a01 a11) where

  --         up x
  --       ---->-----
  --       |        |
  --left i |        |right i
  --       |        |
  --       ---->-----
  --         down x
  -- 
  --   ^ i:I
  --   |
  --   -- > x : BI

  pathPBridgeP : PathP (λ i → BridgeP (λ x → A x i) (left i) (right i)) down up →
                 BridgeP (λ x → PathP (λ i → A x i) (down x) (up x)) left right
                 
  pathPBridgeP p = λ x i → p i x



  
  -- -- λ r i → a r i is a bridge between paths
  -- lari : BridgeP
  --        (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1))
  --        (λ i → a bi0 i)
  --        (λ i → a bi1 i)
  -- lari = λ r i → a r i

  
  -- -- λ i r → a r i is a path between bridges
  -- lair : PathP
  --        (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i))
  --        (λ r → a r i0)
  --        (λ r → a r i1)
  -- lair = λ i r → a r i

  -- bdgPath-to-pathBdg :
  --   BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) →
  --   PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1)
  -- bdgPath-to-pathBdg bp = λ i r → bp r i

  -- pathBdg-to-bdgPth :
  --   PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1) →
  --   BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i)
  -- pathBdg-to-bdgPth = λ pb → λ r i → pb i r

  -- -- one inverse condition of bdg versus path principle
  -- bridgevPath : ∀ bp → PathP
  --                       (λ _ → BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) )
  --                       bp (pathBdg-to-bdgPth (bdgPath-to-pathBdg bp))
  -- bridgevPath bp = λ x → bp

  -- -- the other one
  -- pathvBridge  : ∀ pb → pb ≡ bdgPath-to-pathBdg ( pathBdg-to-bdgPth pb )
  -- pathvBridge pb = λ i → pb


                  

module _ {ℓ} {A : (@tick x : BI) → Type ℓ} {new0 old0 : A bi0} {new1 old1 : A bi1} where

  change-endpoints : (p0 : new0 ≡ old0) (p1 : new1 ≡ old1) →
                     BridgeP A new0 new1 → BridgeP A old0 old1
  change-endpoints p0 p1 bdg = transport (λ i → BridgeP A (p0 i) (p1 i)) bdg

module _ {ℓA ℓB} (A : (@tick x : BI) → Type ℓA) (B : (@tick x : BI) → Type ℓB)
                      (a0 : A bi0) (a1 : A bi1) where

  change-line : ( nat : (@tick x : BI) → A x → B x ) → (BridgeP A a0 a1) →
              BridgeP B (nat bi0 a0) (nat bi1 a1)
  change-line nat q = λ x → nat x (q x)


module _ {ℓ} (A : (@tick x : BI) → Type ℓ) (B : (@tick x : BI) → Type ℓ)
                      (a0 : A bi0) (a1 : A bi1) where

  change-line-path : ∀ (b0 : B bi0) (b1 : B bi1) ( nat : (@tick x : BI) → A x ≡ B x )
    (nat0 : transport (nat bi0) a0 ≡ b0) (nat1 : transport (nat bi1) a1 ≡ b1) → 
    (BridgeP A a0 a1) ≡ BridgeP B b0 b1
  change-line-path b0 b1 nat nat0 nat1 =
    λ i → BridgeP (λ x → nat x i) (toPathP {A = λ i → nat bi0 i} (nat0) i) ((toPathP {A = λ i → nat bi1 i} (nat1) i))


module _ {ℓA ℓB} (A : (@tick x : BI) → Type ℓA) (B : (@tick x : BI) → Type ℓB)
                      (a0 : A bi0) (a1 : A bi1) (b0 : B bi0) (b1 : B bi1)
                      ( nat : (@tick x : BI) → A x → B x )
                      (nat0 : nat bi0 a0 ≡ b0) (nat1 : nat bi1 a1 ≡ b1)  where

  change-line' : BridgeP A a0 a1 → BridgeP B b0 b1
  change-line' q = change-endpoints nat0 nat1 (change-line A B a0 a1 nat q)

-- module _ {ℓA ℓB} (A : (@tick x : BI) → Type ℓA) (B : (@tick x : BI) → Type ℓB)
--                       (a0 : A bi0) (a1 : A bi1) (b0 : B bi0) (b1 : B bi1)
--                       ( nat : (@tick x : BI) → A x → B x )
--                       (nat0 : nat bi0 a0 ≡ b0) (nat1 : nat bi1 a1 ≡ b1)  where

--   change-line-equiv : BridgeP A a0 a1 ≃ BridgeP B a0 a1


module _ {ℓA ℓB} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) → A x → Type ℓB}
                {o : Σ (A bi0) (B bi0)} {s : Σ (A bi1) (B bi1)} where

  ΣBridgeP : Σ[ q ∈ BridgeP A (fst o) (fst s) ] BridgeP (λ x → B x (q x)) (snd o) (snd s)
         → BridgeP (λ x → Σ (A x) (B x)) o s
  ΣBridgeP  = λ (qbase , qover) → λ x → (qbase x , qover x)

  ΣvsBridgeP : ( Σ[ q ∈ BridgeP A (fst o) (fst s) ] BridgeP (λ x → B x (q x)) (snd o) (snd s) )
               ≃
               BridgeP (λ x → Σ (A x) (B x)) o s
  ΣvsBridgeP = isoToEquiv (iso
               ΣBridgeP
               (λ q → ((λ x → fst (q x)) , λ x → snd (q x)))
               (λ q → bridgePPath λ x → refl)
               λ (qbase , qover) → refl)


module _ {ℓ} {P : (@tick x : BI) → Type ℓ} (isp : (@tick x : BI) → isProp (P x)) {p0 : P bi0} {p1 : P bi1} where

  affineToBridgeP : ( (@tick x : BI) → P x ) → BridgeP P p0 p1
  affineToBridgeP f = subst2 (BridgeP P) (isp bi0 (f bi0) p0) (isp bi1 (f bi1) p1) λ x → f x


-- module _ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} {a0 a1 : A} {b0 b1 : B} where

--   -- we dont use the Σ pcpl as it contains useless transport in our case
--   ×vsBridgeP : BridgeP (λ _ → A) a0 a1 × BridgeP (λ _ → B) b0 b1 ≃ BridgeP (λ _ → A × B) (a0 , b0) (a1 , b1)
--   ×vsBridgeP = isoToEquiv (iso
--                  (λ (aa , bb) → λ x → (aa x , bb x))
--                  (λ q → ( (λ x → fst (q x)) , λ x → snd (q x)))
--                  (λ q → refl)
--                  λ (aa , bb) → refl)

module _ {ℓA ℓB} {A : (@tick x : BI) → Type ℓA} {B : (@tick x : BI) → Type ℓB}
         {a0 : A bi0} {a1 : A bi1} {b0 : B bi0} {b1 : B bi1} where

  -- we dont use the Σ pcpl as it contains useless transport in our case
  ×vsBridgeP : BridgeP A a0 a1 × BridgeP B b0 b1 ≃ BridgeP (λ x → A x × B x) (a0 , b0) (a1 , b1)
  ×vsBridgeP = isoToEquiv (iso
                 (λ (aa , bb) → λ x → (aa x , bb x))
                 (λ q → ( (λ x → fst (q x)) , λ x → snd (q x)))
                 (λ q → refl)
                 λ (aa , bb) → refl)
