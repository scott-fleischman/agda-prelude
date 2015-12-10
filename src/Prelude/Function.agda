{-# OPTIONS --without-K #-}

module Prelude.Function where

open import Agda.Primitive
open import Prelude.Function.Boot public
  hiding (module ⇒)
open import Prelude.Monoidal.Product

module ⇒ where
  open Prelude.Function.Boot.⇒ public

  open ⊗
    using (_,_)

  λ⇑
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (A ⊗ B → C)
    → (A → B ⇒ C)
  λ⇑ f a b = f (a , b)

  λ⇓
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (A → B ⇒ C)
    → (A ⊗ B → C)
  λ⇓ f (a , b) = f a b

  syntax λ⇓ (λ a → M) = λ⇓[ a ] M

  ap
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (A ⇒ B) ⊗ A → B
  ap (f , a) = f a
