{-# OPTIONS --cubical --type-in-type --rewriting #-}

open import Primitives
open import TypeSystem
open import Relation

module SystemFParam where

open import Primitives
open import Agda.Primitive hiding (i0 ; i1)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)


Vec : ∀ {ℓ} (A : Set ℓ) (n : ℕ) → Set ℓ
Vec A n = Fin n → A

lookup : ∀ {ℓ n} {A : Set ℓ} → Fin n → Vec A n → A
lookup i vs = vs i

∅ : ∀ {ℓa} {A : Set ℓa} → Vec A 0
∅ ()

_∷v_ : ∀ {ℓa} {n :{#} _} {A :{#} Set ℓa} → A → Vec A n → Vec A (suc n)
(x ∷v xs) = λ { zero → x ; (suc i) → xs i}

vecpure : ∀ {ℓ} {A : Set ℓ} {n} → A → Vec A n
vecpure x i = x

vecmap : ∀ {ℓa ℓb n} {A : Set ℓa} {B : Set ℓb} (f : A → B) → Vec A n → Vec B n
vecmap f xs i = f (xs i)

-- data _≡_ {ℓa} {A : Set ℓa} (x : A) : A → Set where
--   refl : x ≡ x

-- subst : ∀ {ℓa ℓm} {A : Set ℓa} {a b : A} (M : A → Set ℓm) →
--        a ≡ b → M a → M b
-- subst M refl ma = ma


subst₂ : ∀ {ℓa ℓb ℓm} {A :{#} Set ℓa} {B :{#} Set ℓb} {a₁ a₂ :{#} A} {b₁ b₂ :{#} B} (M :{#} A → B → Set ℓm) →
        a₁ ≡ a₂ → b₁ ≡ b₂ → M a₁ b₁ → M a₂ b₂
subst₂ M eq₁ eq₂ mab₁ = subst (M _) eq₂ (subst (λ a → M a _) eq₁ mab₁)

--postulate
extensionality : ∀ {ℓa ℓb} {A :{#} Set ℓa} {B :{#} A → Set ℓb} {f g :{#} (x : A) → B x} → (∀ y → f y ≡ g y) → f ≡ g
extensionality = funext


-- record Lift₁ (X : Set) : Set₁ where
--   constructor lift₁
--   field unlift₁ : X

-- record Lift₂ (X : Set₁) : Set₂ where
--   constructor lift₂
--   field unlift₂ : X

-- record Σ {ℓa ℓb} (A : Set ℓa) (B : A → Set ℓb) : Set (ℓa ⊔ ℓb) where
--   constructor _,_
--   field fst : A
--         snd : B fst

-- syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

data Type (n : ℕ) : Set where
  tvar : Fin n → Type n
  _⟶_ : Type n → Type n → Type n
  tall : Type (suc n) → Type n

idType : Level → Type 0
idType ℓ = tall (tvar zero ⟶ tvar zero)

⌊_⌋ₒ : ∀ {n} → Type n → Vec Set n → Set
⌊ tvar x ⌋ₒ ρ = lookup x ρ
⌊ τ₁ ⟶ τ₂ ⌋ₒ ρ = ⌊ τ₁ ⌋ₒ ρ → ⌊ τ₂ ⌋ₒ ρ
⌊ tall τ ⌋ₒ ρ =  (A :{ # } Set) → ⌊ τ ⌋ₒ (A ∷v ρ)

depCons : ∀ {n :{#} _} (T : Vec Set (suc n)) → T zero → (∀ x → T (suc x)) → (∀ x → T x)
depCons T v vs zero = v
depCons T v vs (suc x) = vs x

_⇒_ : ∀ {ℓA ℓB} {A0 A1 : Set ℓA} → (Ar : A0 → A1 → Set) →
        {B0 B1 : Set ℓB} → (Br : B0 → B1 → Set) →
        (A0 → B0) → (A1 → B1) → Set
_⇒_ Ar Br f₀ f₁ = ∀ a0 a1 (ar : Ar a0 a1) → (Br (f₀ a0) (f₁ a1))

⌊_⌋ᵣ : ∀ {n} (τ : Type n) →
     (ρ₀ : Vec Set n) →
     (ρ₁ : Vec Set n) →
     (ρᵣ : ∀ (x : Fin n) → ρ₀ x → ρ₁ x → Set) →
     ⌊ τ ⌋ₒ ρ₀ → ⌊ τ ⌋ₒ ρ₁ → Set
⌊ tvar x ⌋ᵣ ρ₀ ρ₁ ρᵣ = ρᵣ x
⌊ τ₀ ⟶ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ = ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ ⇒ ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ
⌊ tall τ ⌋ᵣ ρ₀ ρ₁ ρᵣ v₀ v₁ = ∀ τ₀ τ₁ (τᵣ : τ₀ → τ₁ → Set) → ⌊ τ ⌋ᵣ (τ₀ ∷v ρ₀) (τ₁ ∷v ρ₁) (depCons (λ x → (τ₀ ∷v ρ₀) x → (τ₁ ∷v ρ₁) x → Set) τᵣ ρᵣ) (v₀ τ₀) (v₁ τ₁)

postulate
  -- ANDREAS: non-fishy
  uip : ∀{ℓA} {A :{#} Set ℓA} {a b :{#} A} → {e e' :{#} a ≡ b} → e ≡ e'

subst-id : ∀ {a p} {A :{#} Set a} (P :{#} A → Set p) {x :{#} A} →
           (eq : x ≡ x) → (v : P x) → subst P eq v ≡ v
subst-id P eq v = cong (λ eq' → subst P eq' v) ((eq ≡ refl _) ∋ uip)


funBuildPath : ∀ {ℓA ℓB}
  (A0 A1 :{#} Set ℓA) →
  (Ar :{#} A0 → A1 → Set) →
  (B0 B1 :{#} Set ℓB) →
  (Br :{#} B0 → B1 → Set) →
  (f0 : A0 → B0) (f1 : A1 → B1) →
  (fr : (Ar ⇒ Br) f0 f1) →
  (i :{#} 𝕀) → / Ar / i → / Br / i
funBuildPath A0 A1 Ar B0 B1 Br f0 f1 fr i ac = mweld
                                               ((λ{ a01r → push Br i
                                                                (f0 (fst (fst a01r)))
                                                                (f1 (snd (fst a01r)))
                                                                (fr _ _ (snd a01r))
                                                 }))
                                               (λ { ((i ≣ i0) = p⊤) → f0
                                                 ; ((i ≣ i1) = p⊤) → f1
                                                 })
                                               ac

funUsePath : ∀ {ℓA ℓB}
  (A0 A1 :{#} Set ℓA) →
  (Ar :{#} A0 → A1 → Set) →
  (B0 B1 :{#} Set ℓB) →
  (Br :{#} B0 → B1 → Set) →
  (fc : (i :{#} 𝕀) → / Ar / i → / Br / i) →
  (Ar ⇒ Br) (fc i0) (fc i1)
funUsePath A0 A1 Ar B0 B1 Br fc a0 a1 ar = pull Br (λ i → fc i (push Ar i a0 a1 ar))

aprelpath : ∀ {ℓA ℓB}
              {A0 A1 :{#} Set ℓA} →
              (Ar :{#} A0 → A1 → Set) →
              {B0 B1 :{#} Set ℓB} →
              (Br :{#} B0 → B1 → Set) →
              (i :{#} 𝕀) →
              (frel : / Ar ⇒ Br / i) →
              (argrel : / Ar / i) →
              / Br / i
aprelpath Ar Br i frel argrel =
  mweld {C = λ _ → / Br / i}
         (λ fgr →
            mweld {C = λ _ → / Br / i}
                  (λ abr → push Br i _ _ (snd fgr _ _ (snd abr)))
                  (λ { ((i ≣ i0) = p⊤) → fst (fst fgr)
                      ; ((i ≣ i1) = p⊤) → snd (fst fgr)
                      }) argrel
         )
         (λ { ((i ≣ i0) = p⊤) → λ f₀ → f₀ argrel
            ; ((i ≣ i1) = p⊤) → λ f₁ → f₁ argrel})
         frel

postulate
  weldTgt : ∀{ℓ} {φ :{#} _} {A B :{#} Set ℓ} {T :{#} Partial (Set ℓ) φ} {f :{¶} PartialP φ (λ o → B → T o)}
    → (A → Weld B φ T f) → (Weld (A → B) φ (λ o → A → T o) (λ o g → f o ∘ g))

mweldFun : {la₁ lb₁ la₂ lb₂ la₃ lb₃ : Level}
           {A₁ :{#} Set la₁} {A₂ :{#} Set la₂} {A₃ :{#} Set la₃} {φ :{#} 𝕀 → Prop}
           {T₁ :{#} (i :{#} 𝕀) → Partial (Set lb₁) (φ i)} {f₁ :{¶} (i :{#} 𝕀) → PartialP (φ i) (λ .o → A₁ → T₁ i o)}
           {T₂ :{#} (i :{#} 𝕀) → Partial (Set lb₂) (φ i)} {f₂ :{¶} (i :{#} 𝕀) → PartialP (φ i) (λ .o → A₂ → T₂ i o)}
           {T₃ :{#} (i :{#} 𝕀) → Partial (Set lb₃) (φ i)} {f₃ :{¶} (i :{#} 𝕀) → PartialP (φ i) (λ .o → A₃ → T₃ i o)}
           (qA : (gT : (i :{#} 𝕀) → PartialP (φ i) (λ .o → T₁ i o → T₂ i o)) →
             (gA : A₁ → A₂) →
             (∀ (i :{#} 𝕀) a₁ → PartialP (φ i) (λ .o → gT i o (f₁ i o a₁) ≡ f₂ i o (gA a₁))) →
             A₃)
           (qT : (i :{#} 𝕀) → PartialP (φ i) (λ .o → (t : T₁ i o → T₂ i o) → T₃ i o))
           (i :{#} 𝕀) → (gW : Weld A₁ (φ i) (T₁ i) (f₁ i) → Weld A₂ (φ i) (T₂ i) (f₂ i)) →
           Weld A₃ (φ i) (T₃ i) (f₃ i)
mweldFun = {!!}
  --a general implementation of mweldFun is impossible because Agda cannot unify the neutral proposition φ i with p⊤.
    
mweldFun' : {la₁ lb₁ la₂ lb₂ la₃ lb₃ : Level}
           {A₁ :{#} Set la₁} {A₂ :{#} Set la₂} {A₃ :{#} Set la₃}
           {T₁ :{#} (i :{#} 𝕀) → Partial (Set lb₁) (i ≣ i0)} {f₁ :{¶} (i :{#} 𝕀) → PartialP (i ≣ i0) (λ .o → A₁ → T₁ i o)}
           {T₂ :{#} (i :{#} 𝕀) → Partial (Set lb₂) (i ≣ i0)} {f₂ :{¶} (i :{#} 𝕀) → PartialP (i ≣ i0) (λ .o → A₂ → T₂ i o)}
           {T₃ :{#} (i :{#} 𝕀) → Partial (Set lb₃) (i ≣ i0)} {f₃ :{¶} (i :{#} 𝕀) → PartialP (i ≣ i0) (λ .o → A₃ → T₃ i o)}
           (qA : (gT : (i :{#} 𝕀) → PartialP (i ≣ i0) (λ .o → T₁ i o → T₂ i o)) →
             (gA : A₁ → A₂) →
             (∀ (i :{#} 𝕀) a₁ → PartialP (i ≣ i0) (λ .o → gT i o (f₁ i o a₁) ≡ f₂ i o (gA a₁))) →
             A₃)
           (qT : (i :{#} 𝕀) → PartialP (i ≣ i0)(λ .o → (t : T₁ i o → T₂ i o) → T₃ i o))
           (i :{#} 𝕀) → (gW : Weld A₁ (i ≣ i0) (T₁ i) (f₁ i) → Weld A₂ (i ≣ i0) (T₂ i) (f₂ i)) →
           Weld A₃ (i ≣ i0) (T₃ i) (f₃ i)
mweldFun' {A₁ = A₁}{A₂}{A₃}{T₁}{f₁}{T₂}{f₂}{T₃}{f₃} qA qT i gW =
         mweld {φ = (i ≣ i0)}
           (λ g → weld {φ = (i ≣ i0)}
                        (qA (λ{j ((j ≣ i0) = p⊤) → {!!}})
                            {!!}
                            {!!}
                        ))
           {!!}
           wg
  where
    wg : Weld (Weld A₁ (i ≣ i0) (T₁ i) (f₁ i) → A₂) (i ≣ i0)
         (λ .o → Weld A₁ (i ≣ i0) (T₁ i) (f₁ i) → T₂ i o) (λ .o g → (f₂ i o) ∘ g)
    wg = weldTgt {φ = (i ≣ i0)} gW

-- not true?
absrelpath : ∀ {ℓA ℓB}
               {A0 A1 :{#} Set ℓA} →
               (Ar :{#} A0 → A1 → Set) →
               {B0 B1 :{#} Set ℓB} →
               (Br :{#} B0 → B1 → Set) →
               (i :{#} 𝕀) →
               (frel : / Ar / i → / Br / i) →
               / Ar ⇒ Br / i
absrelpath {ℓA} {ℓB }{A0} {A1} Ar {B0} {B1} Br =
  mweldFun h₁ h₂
  where
    φ :{#} (i : 𝕀) → Prop
    φ i = ((i ≣ i0) ∨ (i ≣ i1))

    TA :{#} (i :{#} 𝕀) → Partial (Set ℓA) (φ i)
    TA i ((i ≣ i0) = p⊤) = A0
    TA i ((i ≣ i1) = p⊤) = A1

    fa : (i :{#} 𝕀) → PartialP (φ i) (λ o → Σ[ c,d ∈ A0 × A1 ] Ar (fst c,d) (snd c,d) → TA i o)
    fa i ((i ≣ i0) = p⊤) = fst ∘ fst
    fa i ((i ≣ i1) = p⊤) = snd ∘ fst

    TB :{#} (i :{#} 𝕀) → Partial (Set ℓA) (φ i)
    TB i ((i ≣ i0) = p⊤) = B0
    TB i ((i ≣ i1) = p⊤) = B1

    fb : (i :{#} 𝕀) → PartialP (φ i) (λ o → Σ[ c,d ∈ B0 × B1 ] Br (fst c,d) (snd c,d) → TB i o)
    fb i ((i ≣ i0) = p⊤) = fst ∘ fst
    fb i ((i ≣ i1) = p⊤) = snd ∘ fst

    -- h₁ : (vp : (i :{#} 𝕀) → PartialP (φ i) (λ o → TA i o → TB i o)) →
    --      (vf : Σ[ c,d ∈ A0 × A1 ] Ar (fst c,d) (snd c,d) →
    --                 Σ[ c,d ∈ B0 × B1 ] Br (fst c,d) (snd c,d)) →
    --      (comm : (i :{#} 𝕀) (argf : _) →
    --        PartialP (φ i) (λ o → vp i o (fa i o argf) ≡ fb i o (vf argf))) →
    --      Σ[ c,d ∈ (A0 → B0) × (A1 → B1) ] (Ar ⇒ Br) (fst c,d) (snd c,d)
    h₁ : (vp : (i :{#} 𝕀) → PartialP (φ i) (λ o → TA i o → TB i o)) →
         (vf : Σ[ c,d ∈ A0 × A1 ] Ar (fst c,d) (snd c,d) →
                 Σ[ c,d ∈ B0 × B1 ] Br (fst c,d) (snd c,d)) →
         (vcomm : (i :{#} 𝕀)
                   (a₁ : Σ[ c,d ∈ A0 × A1 ] Ar (fst c,d) (snd c,d)) →
                   PartialP (φ i) (λ o →
                                     vp i o (fa i o a₁) ≡ _)) → Σ _ (λ v → (Ar ⇒ Br) (fst v) (snd v))
    h₁ fp ff fcomm = [ [ fp i0 itIsOne , fp i1 itIsOne ] , rel ]
      where
        eq₁′ : (v₁ : A0) (v₂ : A1) (vᵣ : Ar v₁ v₂) → fst (fst (ff [ [ v₁ , v₂ ] , vᵣ ])) ≡ fp i0 itIsOne v₁
        eq₁′ v₁ v₂ vᵣ = sym (fcomm i0 [ [ v₁ , v₂ ] , vᵣ ] itIsOne)
        eq₁ : (((v₁ : A0) (v₂ : A1) (vᵣ : Ar v₁ v₂) → B0) ∋ (λ v₁ v₂ (vᵣ : Ar v₁ v₂) → fst (fst (ff [ [ v₁ , v₂ ] , vᵣ ])))) ≡ (λ v₁ v₂ (vᵣ : Ar v₁ v₂) → fp i0 itIsOne v₁)
        eq₁ = extensionality (λ v₁ → extensionality (λ v₂ → extensionality (λ vᵣ → eq₁′ v₁ v₂ vᵣ)))
        eq₂′ : (v₁ : A0) (v₂ : A1) (vᵣ : Ar v₁ v₂) → snd (fst (ff [ [ v₁ , v₂ ] , vᵣ ])) ≡ fp i1 itIsOne v₂
        eq₂′ v₁ v₂ vᵣ = sym (fcomm i1 [ [ v₁ , v₂ ] , vᵣ ] itIsOne)
        eq₂ : (((v₁ : A0) (v₂ : A1) (vᵣ : Ar v₁ v₂) → B1) ∋ (λ v₁ v₂ (vᵣ : Ar v₁ v₂) → snd (fst (ff [ [ v₁ , v₂ ] , vᵣ ])))) ≡ (λ v₁ v₂ (vᵣ : Ar v₁ v₂) → fp i1 itIsOne v₂)
        eq₂ = extensionality (λ v₁ → extensionality (λ v₂ → extensionality (λ vᵣ → eq₂′ v₁ v₂ vᵣ)))
        rel′ : ∀ v₁ v₂ (vᵣ : Ar v₁ v₂) → Br (fst (fst (ff [ [ v₁ , v₂ ] , vᵣ ]))) (snd (fst (ff [ [ v₁ , v₂ ] , vᵣ ])))
        rel′ v₁ v₂ vᵣ = snd (ff [ [ v₁ , v₂ ] , vᵣ ])
        rel : (Ar ⇒ Br) (fp i0 itIsOne) (fp i1 itIsOne)
        rel = subst₂ (λ x y → ∀ v₁ v₂ (vᵣ : Ar v₁ v₂) → Br (x v₁ v₂ vᵣ) (y v₁ v₂ vᵣ)) eq₁ eq₂ rel′

    h₂ : (i :{#} 𝕀) → PartialP (φ i) (λ o → (TA i o → TB i o) → (TA i o → TB i o))
    h₂ i o x = x


connection : ∀ {n} (ρ₀ : Vec Set n) → (ρ₁ : Vec Set n) →
             (ρᵣ : ∀ x → ρ₀ x → ρ₁ x → Set) →
             (x : Fin n) → (i : 𝕀) → Set
connection ρ₀ ρ₁ ρᵣ x = / ρᵣ x /

⌊_⌋∁ : ∀ {n} (τ : Type n) →
     (ρ₀ : Vec Set n) →
     (ρ₁ : Vec Set n) →
     (ρᵣ : ∀ (x : Fin n) → ρ₀ x → ρ₁ x → Set) →
     𝕀 → Set
⌊ τ ⌋∁ ρ₀ ρ₁ ρᵣ i = ⌊ τ ⌋ₒ (λ x → connection ρ₀ ρ₁ ρᵣ x i)

test : ∀ {n} (τ : Type n) → (ρ₀ :{#} Vec Set n) → (ρ₁ :{#} Vec Set n) →
       (ρᵣ :{#} ∀ x → ρ₀ x → ρ₁ x → Set) →
       ∀ i → / ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i → ⌊ τ ⌋∁ ρ₀ ρ₁ ρᵣ i
test′ : ∀ {n} (τ : Type n) → (ρ₀ :{#} Vec Set n) → (ρ₁ :{#} Vec Set n) →
       (ρᵣ :{#} ∀ x → ρ₀ x → ρ₁ x → Set) →
       ∀ i → ⌊ τ ⌋∁ ρ₀ ρ₁ ρᵣ i → / ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
test (tvar x) ρ₀ ρ₁ ρᵣ i pf = pf
test (τ₀ ⟶ τ₁) ρ₀ ρ₁ ρᵣ i pf v =
  test τ₁ ρ₀ ρ₁ ρᵣ i h′
  where
    h : / ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
    h = test′ τ₀ ρ₀ ρ₁ ρᵣ i v

    h′ : / ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
    h′ = aprelpath (⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ) (⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ) i pf h
test (tall τ) ρ₀ ρ₁ ρᵣ i pf A = test τ (A ∷v ρ₀) (A ∷v ρ₁) ρᵣ′ {!i!} {!!}
  where
    ρᵣ′ :{#} ∀ x → (A ∷v ρ₀) x → (A ∷v ρ₁) x → Set
    ρᵣ′ zero = _≡_
    ρᵣ′ (suc x) = ρᵣ x

    pf′ : {!!}
    pf′ = {!pf!}
test′ (tvar x) ρ₀ ρ₁ ρᵣ i pf = pf
test′ (τ₀ ⟶ τ₁) ρ₀ ρ₁ ρᵣ i pf =
  absrelpath (⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ) (⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ) i h
  where pf′ : ⌊ τ₀ ⌋∁ ρ₀ ρ₁ ρᵣ i → ⌊ τ₁ ⌋∁ ρ₀ ρ₁ ρᵣ i
        pf′ = pf

        h : / ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i → / ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
        h x = test′ τ₁ ρ₀ ρ₁ ρᵣ i (pf (test τ₀ ρ₀ ρ₁ ρᵣ i x))
test′ (tall τ) ρ₀ ρ₁ ρᵣ i pf = {!!}

par-con-to-rel : ∀ {n :{#} _} (τ : Type n) → (ρ₀ : Vec Set n) → (ρ₁ : Vec Set n) →
                 (ρᵣ : ∀ x → ρ₀ x → ρ₁ x → Set) →
                 (v∁ : (i :{#} 𝕀) → ⌊ τ ⌋∁ ρ₀ ρ₁ ρᵣ i) →
                 ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ (v∁ b0) (v∁ b1)
par-rel-to-con : ∀ {n :{#} _} (τ : Type n) → (ρ₀ : Vec Set n) → (ρ₁ : Vec Set n) →
                 (ρᵣ : ∀ x → ρ₀ x → ρ₁ x → Set) →
                 ∀ v₀ v₁ → ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ v₀ v₁ →
                 (i :{#} 𝕀) → ⌊ τ ⌋∁ ρ₀ ρ₁ ρᵣ i
par-rel-to-con-b0 : ∀ {n :{#} _} (τ : Type n) → (ρ₀ : Vec Set n) → (ρ₁ : Vec Set n) →
                 (ρᵣ : ∀ x → ρ₀ x → ρ₁ x → Set) →
                 ∀ v₀ v₁ → (vᵣ : ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ v₀ v₁) →
                 par-rel-to-con τ ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ b0 ≡ v₀
par-rel-to-con-b1 : ∀ {n :{#} _} (τ : Type n) → (ρ₀ : Vec Set n) → (ρ₁ : Vec Set n) →
                 (ρᵣ : ∀ x → ρ₀ x → ρ₁ x → Set) →
                 ∀ v₀ v₁ → (vᵣ : ⌊ τ ⌋ᵣ ρ₀ ρ₁ ρᵣ v₀ v₁) →
                 par-rel-to-con τ ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ b1 ≡ v₁


par-con-to-rel (tvar x) ρ₀ ρ₁ ρᵣ v∁ = pull (ρᵣ x) v∁
par-con-to-rel (τ₀ ⟶ τ₁) ρ₀ ρ₁ ρᵣ f∁ v₀ v₁ vᵣ =
  -- funUsePath (⌊ τ₀ ⌋ₒ ρ₀) (⌊ τ₀ ⌋ₒ ρ₁) (⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ)
  --            (⌊ τ₁ ⌋ₒ ρ₀) (⌊ τ₁ ⌋ₒ ρ₁) (⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ) h
  -- where
  --   h′ : (i :{#} 𝕀) →
  --        (a : Σ[ c,d ∈ ⌊ τ₀ ⌋ₒ ρ₀ × ⌊ τ₀ ⌋ₒ ρ₁ ] ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ (fst c,d) (snd c,d)) →
  --        / ⌊ τ₁ ⌋ᵣ (λ z → ρ₀ z) (λ z → ρ₁ z) ρᵣ / i
  --   h′ = {!!}
 
  --   h : (i :{#} 𝕀) →
  --       / ⌊ τ₀ ⌋ᵣ (λ z → ρ₀ z) (λ z → ρ₁ z) ρᵣ / i →
  --       / ⌊ τ₁ ⌋ᵣ (λ z → ρ₀ z) (λ z → ρ₁ z) ρᵣ / i
  --   h i x = mweld {A = Σ[ c,d ∈ _ × _ ] ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ (fst c,d) (snd c,d)}
  --                 {T = (λ { ((i ≣ i0) = p⊤) → ⌊ τ₀ ⌋ₒ ρ₀
  --                         ; ((i ≣ i1) = p⊤) → ⌊ τ₀ ⌋ₒ ρ₁
  --                         })}
  --                 {C = λ _ → / ⌊ τ₁ ⌋ᵣ (λ z → ρ₀ z) (λ z → ρ₁ z) ρᵣ / i}
  --                  (h′ i)
  --                  (λ { ((i ≣ i0) = p⊤) → f∁ b0
  --                     ; ((i ≣ i1) = p⊤) → f∁ b1
  --                     }) x
  -- {!res!}
  -- where
  --   f∁′ : (i :{#} 𝕀) → ⌊ τ₀ ⌋∁ ρ₀ ρ₁ ρᵣ i → ⌊ τ₁ ⌋∁ ρ₀ ρ₁ ρᵣ i
  --   f∁′ = f∁

  --   path : (i :{#} 𝕀) → / ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i → / ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
  --   path i arg = {!!}

  --   res : (a0 : ⌊ τ₀ ⌋ₒ ρ₀) (a1 : ⌊ τ₀ ⌋ₒ ρ₁) →
  --           ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ a0 a1 → ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ (path i0 a0) (path i1 a1)
  --   res = funUsePath (⌊ τ₀ ⌋ₒ ρ₀) (⌊ τ₀ ⌋ₒ ρ₁) (⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ)
  --                    (⌊ τ₁ ⌋ₒ ρ₀) (⌊ τ₁ ⌋ₒ ρ₁) (⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ) path
  res'
  where
    arg : (i :{#} 𝕀) → ⌊ τ₀ ⌋∁ ρ₀ ρ₁ ρᵣ i
    arg i = par-rel-to-con τ₀ ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ i

    arg-b0 : arg b0 ≡ v₀
    arg-b0 = par-rel-to-con-b0 τ₀ ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ

    arg-b1 : arg b1 ≡ v₁
    arg-b1 = par-rel-to-con-b1 τ₀ ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ

    res : ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ (f∁ b0 (arg b0)) (f∁ b1 (arg b1))
    res = par-con-to-rel τ₁ ρ₀ ρ₁ ρᵣ (λ i → f∁ i (arg i))

    res' : ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ (f∁ b0 v₀) (f∁ b1 v₁)
    res' = subst₂ (λ w₀ w₁ → ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ (f∁ b0 w₀) (f∁ b1 w₁)) arg-b0 arg-b1 res

par-con-to-rel {n} (tall τ) ρ₀ ρ₁ ρᵣ v∁ τ₀ τ₁ τᵣ =
  subst₂ (⌊ τ ⌋ᵣ (τ₀ ∷v ρ₀) (τ₁ ∷v ρ₁) _) v∁′≡v∁-b0 v∁′≡v∁-b1 h
  where
    ρ₀′ : Vec Set (suc n)
    ρ₀′ = τ₀ ∷v ρ₀
    ρ₁′ : Vec Set (suc n)
    ρ₁′ = τ₁ ∷v ρ₁
    ρᵣ′ : ∀ x → lookup x ρ₀′ → lookup x ρ₁′ → Set
    ρᵣ′ = depCons (λ x → (τ₀ ∷v ρ₀) x → (τ₁ ∷v ρ₁) x → Set) τᵣ ρᵣ

    eq′ : (i :{#} 𝕀) → ∀ x → (connection ρ₀′ ρ₁′ ρᵣ′ x i) ≡ (/ τᵣ / i ∷v (λ x → connection ρ₀ ρ₁ ρᵣ x i)) x
    eq′ i zero = refl _
    eq′ i (suc x) = refl _

    eq : (i :{#} 𝕀) → (λ x → connection ρ₀′ ρ₁′ ρᵣ′ x i) ≡ (/ τᵣ / i ∷v (λ x → connection ρ₀ ρ₁ ρᵣ x i))
    eq i = extensionality (eq′ i)

    v∁″ : (i :{#} 𝕀) → ⌊ τ ⌋ₒ (/ τᵣ / i ∷v (λ x → connection ρ₀ ρ₁ ρᵣ x i))
    v∁″ i = v∁ i (/ τᵣ / i)

    v∁′ : (i :{#} 𝕀) → ⌊ τ ⌋ₒ (λ x → connection ρ₀′ ρ₁′ ρᵣ′ x i)
    v∁′ i = subst ⌊ τ ⌋ₒ (sym (eq i)) (v∁″ i)

    v∁′≡v∁-b0 : v∁′ b0 ≡ v∁ b0 τ₀
    v∁′≡v∁-b0 = subst-id ⌊ τ ⌋ₒ (sym (eq b0)) (v∁ b0 τ₀)

    v∁′≡v∁-b1 : v∁′ b1 ≡ v∁ b1 τ₁
    v∁′≡v∁-b1 = subst-id ⌊ τ ⌋ₒ (sym (eq b1)) (v∁ b1 τ₁)

    h : ⌊ τ ⌋ᵣ ρ₀′ ρ₁′ ρᵣ′ (v∁′ b0) (v∁′ b1)
    h = par-con-to-rel τ ρ₀′ ρ₁′ ρᵣ′ v∁′

par-rel-to-con (tvar x) ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ i = push (ρᵣ x) i _ _ vᵣ
par-rel-to-con (τ₀ ⟶ τ₁) ρ₀ ρ₁ ρᵣ f₀ f₁ fᵣ = {!!}
  where
    fᵣ′ : (i :{#} 𝕀) → / ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i → / ⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ / i
    fᵣ′ = funBuildPath (⌊ τ₀ ⌋ₒ ρ₀) (⌊ τ₀ ⌋ₒ ρ₁) (⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ)
                       (⌊ τ₁ ⌋ₒ ρ₀) (⌊ τ₁ ⌋ₒ ρ₁) (⌊ τ₁ ⌋ᵣ ρ₀ ρ₁ ρᵣ) f₀ f₁ fᵣ

    vᵣ : {!⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ (v∁ b0) (v∁ b1)!}
    vᵣ = {!v∁!}

    res : (i :{#} 𝕀) → ⌊ τ₀ ⌋∁ ρ₀ ρ₁ ρᵣ i → ⌊ τ₁ ⌋∁ ρ₀ ρ₁ ρᵣ i
    res i v∁ = par-rel-to-con τ₁ ρ₀ ρ₁ ρᵣ (f₀ {!v∁!}) (f₁ {!!}) (fᵣ {!!} {!!} {!!}) i

    -- res : (i :{#} 𝕀) → ⌊ τ₀ ⌋∁ ρ₀ ρ₁ ρᵣ i → ⌊ τ₁ ⌋∁ ρ₀ ρ₁ ρᵣ i
    -- res = {!!}

-- {!mweld {A = Σ[ c,d ∈ _ × _ ] ⌊ τ₀ ⌋ᵣ ρ₀ ρ₁ ρᵣ (fst c,d) (snd c,d)}
--                   {T = (λ { ((i ≣ i0) = p⊤) → ⌊ τ₀ ⌋ₒ ρ₀
--                           ; ((i ≣ i1) = p⊤) → ⌊ τ₀ ⌋ₒ ρ₁
--                           })}
--                  {C = λ _ → ⌊ τ₁ ⌋∁ ρ₀ ρ₁ ρᵣ i}
--                  (λ cdr → par-rel-to-con τ₁ ρ₀ ρ₁ ρᵣ
--                                          (f₀ (fst (fst cdr))) (f₁ (snd (fst cdr)))
--                                          (fᵣ (fst (fst cdr)) (snd (fst cdr)) (snd cdr)) i)
--                  (λ { ((i ≣ i0) = p⊤) → ?
--                     ; ((i ≣ i1) = p⊤) → ?
--                     })
--                  !}
      -- par-rel-to-con τ₁ ρ₀ ρ₁ ρᵣ (f₀ {!!}) (f₁ {!!}) (fᵣ {!!} {!!} {!!}) i
par-rel-to-con (tall τ) ρ₀ ρ₁ ρᵣ v₀ v₁ vᵣ i = {!!}

par-rel-to-con-b0 = {!!}
par-rel-to-con-b1 = {!!}

parametricity : ∀ (τ : Type 0) → (f : ⌊ τ ⌋ₒ ∅) → ⌊ τ ⌋ᵣ ∅ ∅ (λ ()) f f
parametricity τ f = subst₂ (⌊ τ ⌋ᵣ ∅ ∅ (λ ())) f′-b0 f′-b1 h
  where
    f′ : (i :{#} 𝕀) → ⌊ τ ⌋ₒ (λ x → connection ∅ ∅ (λ ()) x i)
    f′ i = subst ⌊ τ ⌋ₒ (extensionality (λ ())) f

    f′-b0 : f′ b0 ≡ f
    f′-b0 = subst-id ⌊ τ ⌋ₒ (extensionality (λ ())) f

    f′-b1 : f′ b1 ≡ f
    f′-b1 = subst-id ⌊ τ ⌋ₒ (extensionality (λ ())) f

    h : ⌊ τ ⌋ᵣ ∅ ∅ (λ ()) (f′ b0) (f′ b1)
    h = par-con-to-rel τ ∅ ∅ (λ ()) f′

-- simple test to see if the object and relational interpretations make sense.
τid : Type 0
τid = tall (tvar zero ⟶ tvar zero)

⌊τid⌋ₒ = ⌊ τid ⌋ₒ (λ ())
⌊τid⌋ᵣ = ⌊ τid ⌋ᵣ ∅ ∅ (λ ())
