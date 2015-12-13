{-# OPTIONS --without-K #-}

module Prelude.Lift where

open import Agda.Primitive

record ⊔⇑ ..{ℓ₀} ..ℓ₁ (A : Set ℓ₀) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor ι
  field
    π : A
