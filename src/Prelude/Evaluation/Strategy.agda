{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude.Path

module Prelude.Evaluation.Strategy where

module Eval where
  primitive
    primForce
      : ∀ {ℓ₀ ℓ₁}
      → {A : Set ℓ₀} {B : A → Set ℓ₁}
      → (x : A)
      → (∀ x → B x)
      → B x

    primForceLemma
      : ∀ {ℓ₀ ℓ₁}
      → {A : Set ℓ₀} {B : A → Set ℓ₁}
      → (x : A)
      → (f : ∀ x → B x)
      → primForce x f ≡ f x
