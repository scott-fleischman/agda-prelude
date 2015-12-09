{-# OPTIONS --without-K #-}

module Prelude.Coproduct where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Void

module ⊕ where
  infix 1 _⊕_
  infix 1 [_,_]

  open ⇒
    using (_<∘_)

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
  [ f ⊕ g ] = [ inl <∘ f , inr <∘ g ]

  α⇒
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊕ B) ⊕ C) ⇒ (A ⊕ (B ⊕ C))
  α⇒ = [ [ inl , inr <∘ inl ] , inr <∘ inr ]

  α⇐
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊕ B) ⊕ C) ⇐ (A ⊕ (B ⊕ C))
  α⇐ = [ inl <∘ inl , [ inl <∘ inr , inr ] ]

  β
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (A ⊕ B) ⇒ (B ⊕ A)
  β = [ inr , inl ]

  λ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟘 ⊕ A) ⇒ A
  λ⇒ = [ 𝟘.¡ , ⇒.idn ]

  λ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟘 ⊕ A) ⇐ A
  λ⇐ = inr

  ρ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊕ 𝟘) ⇒ A
  ρ⇒ = [ ⇒.idn , 𝟘.¡ ]

  ρ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊕ 𝟘) ⇐ A
  ρ⇐ = inl

  open import Prelude.Coproduct.Indexed public

open ⊕ public
  using (_⊕_)
  hiding (module _⊕_)
