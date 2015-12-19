{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Product.Indexed where

open import Agda.Primitive
open import Prelude.Display

module Π where
  infixr 0 _⊆_
  infixr 1 _⟔_
  infixr 1 _⟓_

  Π : ∀ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
  Π A B = (x : A) → B x

  syntax Π A (λ x → B) = Π[ A ∋ x ] B

  _⊆_
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂} {I : Set ℓ₀}
    → (A : I → Set ℓ₁)
    → (B : I → Set ℓ₂)
    → Set _
  A ⊆ B = ∀ {x} → A x → B x

  idn : ∀ {ℓ} {A : Set ℓ} → A → A
  idn x = x

  cmp
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
    → (g : ∀ {a} → (b : B a) → C b)
    → (f : (a : A) → B a)
    → ((a : A) → C (f a))
  (cmp g f) x = g (f x)

  seq
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
    → (f : (a : A) → B a)
    → (g : ∀ {a} → (b : B a) → C b)
    → ((a : A) → C (f a))
  seq f g = cmp g f

  _⟔_ : _
  _⟔_ = cmp

  _⟓_ : _
  _⟓_ = seq

  {-# DISPLAY cmp g f = g ᵈ.⟔ f #-}
  {-# DISPLAY seq f g = f ᵈ.⟓ g #-}

open Π public
  using (Π)
