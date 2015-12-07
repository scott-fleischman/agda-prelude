{-# OPTIONS --without-K #-}

module Prelude.Functor where

open import Agda.Primitive

module Functor where
  record # ..{ℓ₀ ℓ₁}
    (F : Set ℓ₀ → Set ℓ₁) : Set (lsuc ℓ₀ ⊔ ℓ₁) where
    no-eta-equality
    field
      map : ∀ {A B} → (A → B) → (F A → F B)

  open # ⦃ … ⦄ public

open Functor public
  renaming (# to Functor)
  hiding (module #)
  using ()
