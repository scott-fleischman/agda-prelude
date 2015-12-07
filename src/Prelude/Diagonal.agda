{-# OPTIONS --without-K #-}

module Prelude.Diagonal where

Δ[_]
  : ∀ ..{ℓ₀ ℓ₁}
  → {A : Set ℓ₀}
  → {B : Set ℓ₁}
  → A → B → A
Δ[ a ] _ = a
