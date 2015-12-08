{-# OPTIONS --without-K #-}

module Prelude.Decidable where

open import Agda.Primitive
open import Prelude.Coproduct
open import Prelude.Zero

Decidable : ∀ ..{ℓ} (A : Set ℓ) → Set ℓ
Decidable A = 𝟘.¬₀ A ⊕ A
