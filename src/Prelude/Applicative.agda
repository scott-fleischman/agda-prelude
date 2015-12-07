{-# OPTIONS --without-K #-}

module Prelude.Applicative where

open import Agda.Primitive
open import Prelude.Functor
import Prelude.One as #1

record Applicative ..{ℓ₀ ℓ₁}
  (T : Set ℓ₀ → Set ℓ₁)
  ⦃ fun : Functor T ⦄
    : Set (lsuc ℓ₀ ⊔ ℓ₁) where
  infixl 1 _⊛_
  field
    pure : ∀ {A} → A → T A
    apply : ∀ {A B} → T (A → B) → (T A → T B)

  _⊛_ : ∀ {A B} → T (A → B) → (T A → T B)
  _⊛_ = apply

open Applicative ⦃ … ⦄ public
