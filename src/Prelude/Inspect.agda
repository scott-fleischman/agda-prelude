{-# OPTIONS --without-K #-}

module Prelude.Inspect where

open import Agda.Primitive
open import Prelude.Path

record Inspect
  {ℓ₀ ℓ₁}
  {A : Set ℓ₀}
  {B : A → Set ℓ₁}
  (f : (a : A) → B a)
  (a : A)
  (b : B a)
  : Set (ℓ₀ ⊔ ℓ₁)
  where
  constructor [_]
  field
    φ : f a ≡ b

inspect
  : ∀ {ℓ₀ ℓ₁}
  → {A : Set ℓ₀}
  → {B : A → Set ℓ₁}
  → (f : (a : A) → B a)
  → (a : A)
  → Inspect f a (f a)
inspect f a = [ ≡.idn ]
