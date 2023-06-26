{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-} 

module Bridgy.PreMonoid where

open import Bridgy.BridgePrims
open import Bridgy.BridgeExamples
open import Bridgy.ExtentExamples
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Bridgy.NRGRelRecord
open import Bridgy.GelExamples
open import Bridgy.MyPathToEquiv
open import Bridgy.HPropHSetNRG
-- open import Bridgy.TypePreMnd


-- -- The reflexive graph of premonoids
-- PreMon : ∀ (l : Level) → Type (ℓ-suc l)
-- PreMon l = Σ (Type l) (λ A → A × (A → A → A))


-- PreMonNRG : ∀ (l : Level) → NRGraph (ℓ-suc l)
-- PreMonNRG l = record {
--   nrg-cr = PreMon l ;
--   nedge = λ M0 M1 → Σ (M0 .fst → M1 .fst → Type l)
--             (λ MM → (MM (M0 .snd .fst) (M1 .snd .fst)) ×
--               (∀ m0 m1 (mm : MM m0 m1) n0 n1 (nn : MM n0 n1) → MM (M0 .snd .snd m0 n0) (M1 .snd .snd m1 n1))) ;
--   nativ =
--     λ M0 M1 → flip compEquiv ΣvsBridgeP
--     (Σ-cong-equiv relativity λ MM →
--     flip compEquiv ×vsBridgeP
--     (≃-× ( mypathToEquiv (funExt⁻ (funExt⁻ (sym (retEq relativity MM)) (M0 .snd .fst)) (M1 .snd .fst)) )
--     (flip compEquiv ΠvsBridgeP
--     (equivΠCod λ m0 → equivΠCod λ m1 →
--     equivΠ (mypathToEquiv (funExt⁻ (funExt⁻ (sym (retEq relativity MM)) m0) m1)) λ mm →
--     flip compEquiv ΠvsBridgeP
--     (equivΠCod λ n0 → equivΠCod λ n1 →
--     equivΠ ((mypathToEquiv (funExt⁻ (funExt⁻ (sym (retEq relativity MM)) n0) n1))) λ nn →
--     (mypathToEquiv (funExt⁻ (funExt⁻ (sym (retEq relativity MM)) (M0 .snd .snd m0 n0)) (M1 .snd .snd m1 n1)))))))) }

-- A : hSet ⊨  A × (A → A → A)  dnrg
hasPreMonDNRG : {l : Level} → DispNRG l (hSetNRG l)
hasPreMonDNRG = record {
  dcr = λ A → (A .fst) × (A .fst → A .fst → A .fst) ;
  dedge =
    λ A0 A1 AA → λ has0 has1 →
      ((AA (has0 .fst) (has1 .fst)) .fst) ×
      (∀ a0 a1 (aa : (AA a0 a1) .fst ) b0 b1 (bb : (AA b0 b1) .fst ) →
        (AA (has0 .snd a0 b0) (has1 .snd a1 b1) .fst))  ;
  dnativ = λ A0 A1 Abdg has0 has1 →
    flip compEquiv ×vsBridgeP
    (≃-× (idEquiv _)
    (flip compEquiv ΠvsBridgeP
    (equivΠCod λ a0 → equivΠCod λ a1 →
    equivΠ
      (idEquiv _) λ abdg →
    flip compEquiv ΠvsBridgeP
    (equivΠCod λ b0 → equivΠCod λ b1 →
    equivΠ
      (idEquiv _) λ bbdg →
    idEquiv _) ))) }


-- the NRG of premonoids Σ (A:Type) (A × A → A → A)
PreMonNRG : (l : Level) → NRGraph (ℓ-suc l)
PreMonNRG l = (hSetNRG l) # (hasPreMonDNRG)



