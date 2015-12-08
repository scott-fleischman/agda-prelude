{-# OPTIONS --without-K #-}

module Prelude.Function where

open import Agda.Primitive

infixr 0 _⇒_

_⇒_
  : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀)
  → (B : Set ℓ₁)
  → Set (ℓ₀ ⊔ ℓ₁)
A ⇒ B = A → B

module ⇒ where
  infixr 1 _<∘_
  infixr 1 _∘>_

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

  _<∘_ : _
  _<∘_ = cmp
  {-# DISPLAY cmp g f = g <∘ f #-}

  _∘>_ : _
  _∘>_ = seq
  {-# DISPLAY seq f g = f ∘> g #-}

  𝓎
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {R : Set ℓ₁}
    → (x : A) (k : A → R) → R
  𝓎 x k = k x
