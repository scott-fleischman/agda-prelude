{-# OPTIONS --without-K #-}

module Prelude.Functor where

open import Agda.Primitive

record Functor ..{ℓ₀ ℓ₁}
  (F : Set ℓ₀ → Set ℓ₁) : Set (lsuc ℓ₀ ⊔ ℓ₁) where
  no-eta-equality
  field
    map : ∀ {A B} → (A → B) → (F A → F B)

open Functor ⦃ … ⦄ public
