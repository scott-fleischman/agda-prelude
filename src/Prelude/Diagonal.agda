{-# OPTIONS --without-K #-}

module Prelude.Diagonal where

open import Agda.Primitive
open import Prelude.Monoidal.Product

Δ²[_]
  : ∀ ..{ℓ}
  → {A : Set ℓ}
  → A → A ⊗ A
Δ²[ a ] = (a ⊗., a)

Δ[_]
  : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀}
  → {B : Set ℓ₁}
  → A → (B → A)
Δ[ a ] _ = a
