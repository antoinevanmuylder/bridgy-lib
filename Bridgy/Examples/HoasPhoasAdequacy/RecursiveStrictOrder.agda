{-# OPTIONS --cubical --bridges --guarded --no-fast-reduce #-}

module Bridgy.Examples.HoasPhoasAdequacy.RecursiveStrictOrder where

open import Bridgy.Core.BridgePrims
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (_≤_ ; ≤-trans ; ≤-refl ; _<'_)
open import Cubical.Data.FinData renaming (rec to frec)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

_+'_ : ℕ → ℕ → ℕ
_+'_ m 0 = m
_+'_ m (suc n) = suc (m + n)

_+''_ : ℕ → ℕ → ℕ
_+''_ m 0 = m
_+''_ m (suc n) = suc (m +'' n)


+'≡+ : ∀ m n → m +' n ≡ m + n
+'≡+ zero zero = refl
+'≡+ zero (suc n) = cong ℕ.suc refl
+'≡+ (suc m) zero = cong ℕ.suc (sym (+-zero m))
+'≡+ (suc m) (suc n) = cong ℕ.suc (sym (+-suc m n))

0+''n : ∀ n →  (0 +'' n) ≡ n
0+''n zero = refl
0+''n (suc n) = cong ℕ.suc (0+''n n)

+''≡+ : ∀ m n → m +'' n ≡ m + n
+''≡+ zero zero = refl
+''≡+ zero (suc n) = cong ℕ.suc (0+''n n)
+''≡+ (suc m) zero = cong ℕ.suc (sym (+-zero m))
+''≡+ (suc m) (suc n) = cong ℕ.suc ((+''≡+ (suc m) n) ∙ sym (+-suc m n))


≤'+ : ∀ n j → j ≤' (n + j)
≤'+ zero zero = z≤
≤'+ zero (suc j) = s≤s (≤'+ 0 j)
≤'+ (suc n) zero = z≤
≤'+ (suc n) (suc j) =
  s≤s
  let aux = ≤'+ (suc n) j in
  transport (λ i → j ≤' (+-suc n j (~ i))) aux


≤'-refl : ∀ x →  x ≤' x
≤'-refl 0 = z≤
≤'-refl (suc x) = s≤s (≤'-refl x)

_<''_ : ℕ → ℕ → Type
_<''_ n 0 = ⊥
_<''_ 0 (suc n) = Unit
_<''_ (suc m) (suc n) = _<''_ m n

<''→≤' : ∀ x y → x <'' y → x ≤' y
<''→≤' zero (suc y) hypx = z≤
<''→≤' (suc x) (suc y) hypx = s≤s (<''→≤' x y hypx)

≤→<'' : ∀ x y → x ≤ y → x <'' (suc y)
≤→<'' zero zero hyp = tt
≤→<'' zero (suc y) hyp = tt
≤→<'' (suc x) (suc y) hyp = ≤→<'' x y hyp

<''→suc≤ : ∀ x y (hyp : x <'' y) → (suc x) ≤ y
<''→suc≤ zero (suc y) hyp = tt
<''→suc≤ (suc x) (suc y) hyp = <''→suc≤ x y hyp




<''isPropValued : ∀ x y → isProp (x <'' y)
<''isPropValued x zero = isProp⊥
<''isPropValued zero (suc y) = isPropUnit
<''isPropValued (suc x) (suc y) = <''isPropValued x y


x<''sucx : ∀ x → x <'' (suc x)
x<''sucx 0 = tt
x<''sucx (suc x) = x<''sucx x


<''trans : ∀ x y z → x <'' y → y <'' z → x <'' z
<''trans zero zero zero = λ ctr → rec ctr
<''trans zero zero (suc z) = λ ctr → rec ctr
<''trans zero (suc y) zero = λ _ ctr → rec ctr
<''trans zero (suc y) (suc z) = λ _ _ → tt
<''trans (suc x) zero zero = λ ctr → rec ctr
<''trans (suc x) zero (suc z) = λ ctr → rec ctr
<''trans (suc x) (suc y) zero = λ _ ctr → rec ctr
<''trans (suc x) (suc y) (suc z) = λ xy yz → <''trans x y z xy yz


¬suc≤'0 : ∀ y → (suc y ≤' 0 → ⊥)
¬suc≤'0 y = ¬-<'-zero

<''wktrans : ∀ x y z → x <'' y → y ≤' z → x <'' z
<''wktrans zero zero zero = λ ctr → rec ctr
<''wktrans zero zero (suc z) = λ ctr → rec ctr
<''wktrans zero (suc y) zero = λ _ ctr →  ¬suc≤'0 y ctr
<''wktrans zero (suc y) (suc z) = λ _ _ → tt
<''wktrans (suc x) zero zero = λ ctr → rec ctr
<''wktrans (suc x) zero (suc z) = λ ctr → rec ctr
<''wktrans (suc x) (suc y) zero = λ _ ctr → ¬suc≤'0 y ctr
<''wktrans (suc x) (suc y) (suc z) xy  (s≤s pf) = <''wktrans x y z xy pf

j<''sucn+j : ∀ j n → j <'' suc (n + j)
j<''sucn+j zero zero = tt
j<''sucn+j zero (suc n) = tt
j<''sucn+j (suc j) zero = x<''sucx j
j<''sucn+j (suc j) (suc n) =
  let aux = j<''sucn+j j (suc n) in
  transport (λ i → j <'' (cong suc (sym (+-suc n j)) i)) aux

n<''sucn+j : ∀ j n → n <'' suc (n + j)
n<''sucn+j zero zero = tt
n<''sucn+j zero (suc n) =
  <''wktrans n (suc n) (suc (n + 0)) (x<''sucx n)
  (s≤s (subst (λ blk → n ≤' blk) (sym (+-zero n)) (≤'-refl n)))
n<''sucn+j (suc j) zero = tt
n<''sucn+j (suc j) (suc n) = n<''sucn+j (suc j) n

<''+ : ∀ n x y (hyp : x <'' y) → (n + x) <'' (n + y)
<''+ zero zero zero hyp = rec hyp
<''+ zero zero (suc y) hyp = tt
<''+ zero (suc x) zero hyp = rec hyp
<''+ zero (suc x) (suc y) hyp = hyp
<''+ (suc n) zero zero hyp = rec hyp
<''+ (suc n) zero (suc y) hyp = <''+ n 0 (suc y) tt
<''+ (suc n) (suc x) zero hyp = rec hyp
<''+ (suc n) (suc x) (suc y) hyp = <''+ n (suc x) (suc y) hyp

FinTo<'' : ∀ j → Fin j → Σ ℕ (λ k → k <'' j)
FinTo<'' zero ()
FinTo<'' (suc j) zero = 0 , tt
FinTo<'' (suc j) (suc k) = FinTo<'' j k .fst , <''trans (FinTo<'' j k .fst) j (suc j) (FinTo<'' j k .snd) (x<''sucx j)

<''ToFin : ∀ j → Σ ℕ (λ k → k <'' j) → Fin j
<''ToFin (suc j) (zero , prf) = zero
<''ToFin (suc j) (suc k , prf) = suc (<''ToFin j (k , prf))

<''→Fin : ∀ j k (hyp : k <'' j) → Fin j
<''→Fin zero zero hyp = rec hyp
<''→Fin zero (suc k) hyp = rec hyp
<''→Fin (suc j) zero hyp = zero
<''→Fin (suc j) (suc k) hyp = suc (<''→Fin j k hyp)

stupidLemma : ∀ j k (hyp : k <'' j) →
  <''→Fin j k hyp ≡ <''ToFin j (k , hyp)
stupidLemma (suc j) zero hyp = refl
stupidLemma (suc j) (suc k) hyp = cong Fin.suc (stupidLemma j k hyp)

toℕ-<''ToFin : ∀ j k (hypk : k <'' j) → toℕ (<''ToFin j (k , hypk)) ≡ k
toℕ-<''ToFin (suc j) zero hypk = refl
toℕ-<''ToFin (suc j) (suc k) hypk = cong ℕ.suc (toℕ-<''ToFin j k hypk)

toℕRemainsLt : ∀ j (k : Fin j) → toℕ k <'' j
toℕRemainsLt zero ()
toℕRemainsLt (suc j) zero = tt
toℕRemainsLt (suc j) (suc k) = toℕRemainsLt j k

<''ToFin-toℕ : ∀ j (k : Fin j) → (<''ToFin j (toℕ k , toℕRemainsLt j k)) ≡ k
<''ToFin-toℕ zero ()
<''ToFin-toℕ (suc j) zero = refl
<''ToFin-toℕ (suc j) (suc k) = cong suc (<''ToFin-toℕ j k)




Fin→toℕ<'' : ∀ j (k : Fin j) → toℕ k <'' j
Fin→toℕ<'' zero ()
Fin→toℕ<'' (suc j) zero = tt
Fin→toℕ<'' (suc j) (suc k) = Fin→toℕ<'' j k

<''Dec : ∀ m n → Dec (m <'' n)
<''Dec zero zero = no rec
<''Dec zero (suc n) = yes tt
<''Dec (suc m) zero = no rec
<''Dec (suc m) (suc n) = <''Dec m n



≤'-lemma1  : ∀ n → suc n ≤' suc (n + 0)
≤'-lemma1 zero = s≤s z≤
≤'-lemma1 (suc n) = s≤s (≤'-lemma1 n)



∸-compl : ∀ v j → v <'' j → (j ∸ (suc v)) <'' j
∸-compl zero (suc j) hyp = x<''sucx j
∸-compl (suc v) (suc j) hyp = <''trans (j ∸ suc v) j (suc j) (∸-compl v j hyp) (x<''sucx j)


∸lemma1 : ∀ m n  (hypn : n <'' suc m) →  suc m ∸ n ≡ suc (m ∸ n)
∸lemma1 zero zero hypn = refl
∸lemma1 (suc m) zero hypn = refl
∸lemma1 (suc m) (suc n) hypn = ∸lemma1 m n hypn

∸lemma : ∀ j k (hypk : k <'' j) →
  j ∸ (j ∸ suc k) ≡ suc (j ∸ suc (j ∸ suc k))
∸lemma 0 k hypk = rec hypk
∸lemma (suc j) 0 _ = (+∸ 1 j) ∙ λ i → suc (n∸n j (~ i))
∸lemma (suc j) (suc k) hypk =
  _∙_
  (∸lemma1 j (j ∸ suc k) (<''trans (j ∸ suc k) j (suc j) (∸-compl k j hypk) (x<''sucx j))) 
  (cong ℕ.suc
    refl)

∸lemma2 : ∀ n j m (hypm : m ≤ j) → (n + j) ∸ m ≡ n + (j ∸ m)
∸lemma2 zero (suc j) zero hypm = refl
∸lemma2 zero (suc j) (suc m) hypm = refl
∸lemma2 (suc n) (suc j) zero hypm = refl
∸lemma2 zero zero zero hypm = refl
∸lemma2 (suc n) zero zero hypm = refl
∸lemma2 (suc n) (suc j) (suc m) hypm =
  _∙_ (∸lemma2 n (suc j) m (≤-trans {k = m} {m = j} {n = suc j} hypm (n≤k+n {k = 1} j) ))
  (flip _∙_ (+-suc n (j ∸ m)) (cong (_+_ n)
  (∸lemma1 j m (≤→<'' m j hypm))))

∸lemma4 : ∀ j k → (j ∸ k) ≤ j
∸lemma4 zero zero = tt
∸lemma4 zero (suc k) = tt
∸lemma4 (suc j) zero = ≤-refl j
∸lemma4 (suc j) (suc k) = ≤-trans {k = (j ∸ k)} {m = j} {n = (suc j)} (∸lemma4 j k) (n≤k+n {k = 1} j)

∸lemma3 : ∀ j (v : Fin j) → j ∸ (j ∸ toℕ v) ≡ toℕ v
∸lemma3 zero ()
∸lemma3 (suc j) zero = n∸n j
∸lemma3 (suc j) (suc v) =
  _∙_ (∸lemma2 1 j (j ∸ toℕ v)
    (∸lemma4 j (toℕ v)))
  (cong ℕ.suc (∸lemma3 j v))

∸lemma5 : ∀ j (v : Fin (suc j)) → j ∸ (j ∸ toℕ v) ≡ toℕ v
∸lemma5 zero zero = refl
∸lemma5 (suc j) zero = n∸n j
∸lemma5 (suc j) (suc v) =
  _∙_ (∸lemma2 1 j (j ∸ toℕ v) ((∸lemma4 j (toℕ v))))
  (cong ℕ.suc (∸lemma5 j v))

∸lemma6 : ∀ j k (hyp : k <'' j) →
  j ∸ suc (j ∸ (suc k)) ≡ k
∸lemma6 (suc j) zero hyp = n∸n j
∸lemma6 (suc j) (suc k) hyp = (∸lemma j k hyp) ∙ cong ℕ.suc (∸lemma6 j k hyp)

∸lemma7 : ∀ n v → (n ∸ v) <'' suc n
∸lemma7 n 0 = x<''sucx n
∸lemma7 0 (suc v) = tt
∸lemma7 (suc n) (suc v) = <''trans (n ∸ v) (suc n) (suc (suc n)) (∸lemma7 n v) (x<''sucx n)

∸lemma8 : ∀ n j v → (n + suc j ∸ suc v) <'' (n + suc j)
∸lemma8 zero zero zero = tt
∸lemma8 zero zero (suc v) = tt
∸lemma8 zero (suc j) zero = x<''sucx j
∸lemma8 zero (suc j) (suc v) = ∸lemma7 (suc j) (suc v)
∸lemma8 (suc n) zero zero = x<''sucx (n + 1)
∸lemma8 (suc n) zero (suc v) = ∸lemma7 (n + 1) (suc v)
∸lemma8 (suc n) (suc j) zero = x<''sucx (n + (suc (suc j)))
∸lemma8 (suc n) (suc j) (suc v) = ∸lemma7 (n + (suc (suc j))) (suc v)

