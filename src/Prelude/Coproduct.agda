{-# OPTIONS --without-K #-}

module Prelude.Coproduct where

open import Agda.Primitive
open import Prelude.Function

module ⊕ where
  infix 1 _⊕_
  infix 1 [_,_]

  data _⊕_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

  el
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {Ψ : A ⊕ B → Set ℓ₂}
    → (k₀ : (a : A) → Ψ (inl a))
    → (k₁ : (b : B) → Ψ (inr b))
    → (∀ x → Ψ x)
  el k₀ k₁ (inl a) = k₀ a
  el k₀ k₁ (inr b) = k₁ b

  [_,_]
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {X : Set ℓ₂}
    → (f : A → X)
    → (g : B → X)
    → (A ⊕ B → X)
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  [_⊕_]
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X₀ : Set ℓ₀}
    → {X₁ : Set ℓ₁}
    → {A : Set ℓ₂}
    → {B : Set ℓ₃}
    → (f : A → X₀)
    → (g : B → X₁)
    → (A ⊕ B → X₀ ⊕ X₁)
  [ f ⊕ g ] = [ inl ⇒.<∘ f , inr ⇒.<∘ g ]

  open import Prelude.Coproduct.Indexed public

open ⊕ public
  using (_⊕_)
  hiding (module _⊕_)
