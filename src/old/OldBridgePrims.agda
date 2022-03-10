{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce -v tc.conv.gel:40 -v tc.conv.atom:50 #-}
module BridgePrims where

-- this is a reproduction of test/Succeed/LaterPrims.agda and-or Agda.Primitive.Cubical
-- We add a few examples too.

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU)
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

------------------------------------------------------------------------
-- CH internal param primitives
------------------------------------------------------------------------

{-# BUILTIN BRIDGEINTERVAL BI  #-}  -- BI : LockU

{-# BUILTIN BIZERO    bi0 #-}
{-# BUILTIN BIONE     bi1 #-}

-- I is treated as the type of booleans.
-- {-# COMPILE JS i0 = false #-}
-- {-# COMPILE JS i1 = true  #-}


postulate
  BridgeP : ∀ {ℓ} (A : (@tick x : BI) → Set ℓ) → A bi0 → A bi1 → Set ℓ

{-# BUILTIN BRIDGEP        BridgeP     #-}


primitive
  primExtent : ∀ {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB}
               (N0 : (a0 : A bi0) → B bi0 a0)
               (N1 : (a1 : A bi1) → B bi1 a1)
               (NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1))
               (@tick r : BI) (M : A r) →
               B r M

primitive
  primGel : ∀ {ℓ} (A0 A1 : Set ℓ) (R : A0 → A1 → Set ℓ) (@tick r : BI) → Set ℓ


-- caution: R is implicit but can not be inferred from the following args
primitive
  prim^gel : ∀ {ℓ} {A0 A1 : Set ℓ} {R : A0 → A1 → Set ℓ}
               (M0 : A0) (M1 : A1) (P : R M0 M1) (@tick r : BI) →
               primGel A0 A1 R r


primitive
  prim^ungel : ∀ {ℓ} {A0 A1 : Set ℓ} {R : A0 → A1 → Set ℓ}
               (absQ : (@tick x : BI) → primGel A0 A1 R x) →
               R (absQ bi0) (absQ bi1)


------------------------------------------------------------------------
-- about bridges
------------------------------------------------------------------------

module PlayBridgeP {ℓ} {A : (@tick x : BI) → Set ℓ} {a0 : A bi0} {a1 : A bi1}
                   {B : Set ℓ} {b0 b1 : B} where

  -- INTRO RULE
  -- need f : (i:BI) → A i such that p 0 = a0,  p 1 = a1 definitionally.
  mk-bridge : (f : (@tick i : BI) → A i) → BridgeP A (f bi0) (f bi1)
  mk-bridge f = λ i → f i

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
-- module BridgeDiag  {ℓ} {B : (@tick i j : BI) → Set ℓ}
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
module BridgeVBridge {ℓ} (BB : (@tick i j : BI) → Set ℓ) (a : (@tick i j : BI) → BB i j) where


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




-- -- BRIDGES vs PATHS
module BridgeVPath {ℓ} {A : (@tick r : BI) → I → Set ℓ} {a : (@tick r : BI) (i : I) → A r i} where
  
  -- λ r i → a r i is a bridge between paths
  lari : BridgeP
         (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1))
         (λ i → a bi0 i)
         (λ i → a bi1 i)
  lari = λ r i → a r i

  
  -- λ i r → a r i is a path between bridges
  lair : PathP
         (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i))
         (λ r → a r i0)
         (λ r → a r i1)
  lair = λ i r → a r i

  bdgPath-to-pathBdg :
    BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) →
    PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1)
  bdgPath-to-pathBdg bp = λ i r → bp r i

  pathBdg-to-bdgPth :
    PathP (λ i →  BridgeP (λ r → A r i) (a bi0 i)  (a bi1 i)) (λ r → a r i0) (λ r → a r i1) →
    BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i)
  pathBdg-to-bdgPth = λ pb → λ r i → pb i r

  -- one inverse condition of bdg versus path principle
  bridgevPath : ∀ bp → PathP
                        (λ _ → BridgeP (λ r →  PathP (λ i → A r i) (a r i0)  (a r i1)) (λ i → a bi0 i) (λ i → a bi1 i) )
                        bp (pathBdg-to-bdgPth (bdgPath-to-pathBdg bp))
  bridgevPath bp = λ x → bp

  -- the other one
  pathvBridge  : ∀ pb → pb ≡ bdgPath-to-pathBdg ( pathBdg-to-bdgPth pb )
  pathvBridge pb = λ i → pb



------------------------------------------------------------------------
-- extent primitive
------------------------------------------------------------------------


module PlayExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB}
                  (N0 : (a0 : A bi0) → B bi0 a0) (N1 : (a1 : A bi1) → B bi1 a1) where
  
  -- we wish to show bridge-funext: an equivalence btw the two foll. types
  -- pointwise is a retract thanks to extent beta rule
  -- related is a retract thanks to extent eta rule
  pointwise = (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)

  related = BridgeP (λ x → (a : A x) → B x a) N0 N1

  -- bridge-funext, hard direction
  bf-hard : pointwise → related
  bf-hard NN = λ r M → primExtent N0 N1 NN r M


  bf-easy : related -> pointwise
  bf-easy p = λ a0 a1 aa x → p x (aa x)


  pointwise-retract : (H : pointwise) -> H ≡ bf-easy (bf-hard H)
  pointwise-retract H i = H
  -- TODO: issue #2 on my fork: when computing under lambdas, types of vars are forgotten which messes up the fv analysis
  -- try C-u C-u C-C C-t the target type

  -- related-retract : (q : related) -> q ≡ bf-hard ( bf-easy q )
  -- related-retract q i = λ r → {!!}



module BetaExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB}
               {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1}
               {NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)}
               {M' : (@tick j : BI) → A j} {@tick r : BI} where


  extent-beta : primExtent {A = A} {B = B} N0 N1 NN r (M' r) ≡ NN (M' bi0) (M' bi1) (λ j → M' j) r
  extent-beta i = NN (M' bi0) (M' bi1) ( λ j → M' j) r
  
  -- try C-c C-n this. extent only fails to reduce because of issue #2
  -- the semi freshness check r ~∉ M' r fails but it should pass.
  -- when issue #2 is solved this should work
  extent-beta' : B r (M' r)
  extent-beta' = primExtent {A = A} {B = B} N0 N1 NN r (M' r)


  

module NotSemiFreshExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB}
               {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1}
               {NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)}
               {@tick r : BI} {b : Bool} {M' : Bool → A r} where

  -- try C-c C-n this
  -- this one should indded not reduce because r is not semifresh for M' b since M' b contains
  -- b which is a timefull r-later.
  -- However the reason why it does not reduce here is issue #2: r itself is wronlgy 
  -- considered a timefull r-later
  -- I think that if issue #2 gets fixed, this will still not reduce, as expected 
  not-sfresh-M : B r (M' b)
  not-sfresh-M = primExtent {A = A} {B = B} N0 N1 NN r (M' b)


module NotFreshExtent {ℓA ℓB : Level} {A : (@tick x : BI) → Set ℓA} {B : (@tick x : BI) (a : A x) → Set ℓB}
               {@tick r : BI}
               {N0 : (a0 : A bi0) → B bi0 a0} {N1 : (a1 : A bi1) → B bi1 a1}
               {NN : (a0 : A bi0) (a1 : A bi1) (aa : BridgeP A a0 a1) → BridgeP (λ x → B x (aa x)) (N0 a0) (N1 a1)}
               {M : A r} where

  -- N0 N1 NN are supposed to be apart from r in the type of primExtent
  -- but in the above context nothing guarantees that they are
  -- not-fresh-NN : B r M
  -- not-fresh-NN = primExtent {A = A} {B = B} N0 N1 NN r M


    
-- ------------------------------------------------------------------------
-- -- Gel Types
-- ------------------------------------------------------------------------



module PlayGel {ℓ} {A0 A1 : Set ℓ} {R : A0 → A1 → Set ℓ} where

  -- BOUNDARY for Gel type
  boundary0-Gel : primGel A0 A1 R bi0 ≡ A0
  boundary0-Gel i = A0

  boundary1-Gel : primGel A0 A1 R bi1 ≡ A1
  boundary1-Gel i = A1


  -- BOUNDARY for gel
  boundary0-gel : (M0 : A0) (M1 : A1) (P : R M0 M1) → prim^gel {R = R} M0 M1 P bi0 ≡ M0
  boundary0-gel M0 M1 P i = M0

  boundary1-gel : (M0 : A0) (M1 : A1) (P : R M0 M1) → prim^gel {R = R} M0 M1 P bi1 ≡ M1
  boundary1-gel M0 M1 P i = M1


  -- BETA RULE for Gel
  ungel-gel : (M1 : A1) (M0 : A0) (P : R M0 M1) →
    prim^ungel {R = R} ( λ x → prim^gel {R = R} M0 M1 P x ) ≡ P
  ungel-gel M1 M0 P i = P


  -- ETA for Gel
  eta-Gel : (Q : (@tick x : BI) → primGel A0 A1 R x) (@tick r : BI )  → 
    Q r ≡ prim^gel {R = R} (Q bi0) (Q bi1) (prim^ungel {R = R} Q) r
  eta-Gel Q r i = Q r



module Relativity {ℓ} {A0 A1 : Set ℓ} where

  to-rel : BridgeP (λ x → Set ℓ) A0 A1    →    (A0 → A1 → Set ℓ)
  to-rel C = λ a0 a1 → BridgeP (λ x → C x) a0 a1

  to-bridge : (A0 → A1 → Set ℓ)    →    BridgeP (λ x → Set ℓ) A0 A1
  to-bridge R = λ x → primGel A0 A1 R x

  -- wip
  -- rel-retract : ∀ (R : A0 → A1 → Set ℓ) → to-rel (to-bridge R) ≡ R
  -- rel-retract R i a0 a1 = {!!}

