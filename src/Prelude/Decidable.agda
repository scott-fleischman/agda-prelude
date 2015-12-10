{-# OPTIONS --without-K #-}

module Prelude.Decidable where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Void

Decidable : ∀ ..{ℓ} (A : Set ℓ) → Set ℓ
Decidable A = 𝟘.¬ A ⊕ A
