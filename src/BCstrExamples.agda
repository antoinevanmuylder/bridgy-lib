{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce  #-}
module BCstrExamples where

open import BridgePrims
open import Cubical.Foundations.Prelude



ψ : BCstr
ψ = bno b∨ ( (bi0 =bi1) b∨ (byes b∨ bno) )

ψ2 : BCstr
ψ2 = (bno b∨ bno) b∨ byes

indeed : BHolds ψ
indeed = BitHolds
