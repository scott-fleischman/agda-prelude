{-# OPTIONS --without-K #-}

module Prelude.Functor.Indexed where

open import Agda.Primitive
open import Prelude.Families
open Fam
  using (_⊆_)

record IFunctor ..{ℓ₀ ℓ₁ ℓ₂}
  {I : Set ℓ₀}
  (F : ℘ {ℓ₁ = ℓ₁} I → ℘ {ℓ₁ = ℓ₂} I)
  : Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
  where
  no-eta-equality
  field
    imap
      : ∀ {A B}
      → (f : A ⊆ B)
      → F A ⊆ F B

open IFunctor ⦃ … ⦄ public
