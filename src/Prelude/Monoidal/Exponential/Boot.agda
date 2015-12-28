{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Exponential.Boot where

open import Agda.Primitive
open import Prelude.Display

infixr 0 _⇒_
infixl 0 _⇐_

_⇒_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀)
  → (B : Set ℓ₁)
  → Set (ℓ₀ ⊔ ℓ₁)
A ⇒ B = A → B

_⇐_
  : ∀ ..{ℓ₀ ℓ₁}
  → (B : Set ℓ₀)
  → (A : Set ℓ₁)
  → _
B ⇐ A = A ⇒ B

{-# DISPLAY _⇒_ A B = A ᵈ.⇒ B #-}
{-# DISPLAY _⇐_ A B = A ᵈ.⇐ B #-}

module ⇒ where
  infixr 1 _⟔_
  infixr 1 _⟓_

  idn
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A → A)
  idn x = x

  cmp
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
    → (g : B → C)
    → (f : A → B)
    → (A → C)
  (cmp g f) x = g (f x)

  seq
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
    → (f : A → B)
    → (g : B → C)
    → (A → C)
  seq f g = cmp g f

  ↻ : _
  ↻ = idn

  _⟔_ : _
  _⟔_ = cmp

  _⟓_ : _
  _⟓_ = seq

  {-# DISPLAY idn = ᵈ.↻ #-}
  {-# DISPLAY cmp g f = g ᵈ.⟔ f #-}
  {-# DISPLAY seq f g = f ᵈ.⟓ g #-}

  {-# DISPLAY ↻ = ᵈ.↻ #-}
  {-# DISPLAY _⟔_ g f = g ᵈ.⟔ f #-}
  {-# DISPLAY _⟓_ f g = f ᵈ.⟓ g #-}
