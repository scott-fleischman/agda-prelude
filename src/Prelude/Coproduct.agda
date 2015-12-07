{-# OPTIONS --without-K #-}

module Prelude.Coproduct where

open import Agda.Primitive

module ⊕ where
  infix 1 _⊕_
  infix 1 [_,_]

  data _⊕_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

  [_,_] : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₀} {X : Set ℓ₁}
    → (f : A → X)
    → (g : B → X)
    → (A ⊕ B → X)
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  open import Prelude.Coproduct.Indexed public

open ⊕ public
  using (_⊕_)
  hiding (module _⊕_)
