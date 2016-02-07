{-# OPTIONS --without-K #-}

module Prelude.Decidable where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Unit
open import Prelude.Monoidal.Void

Decidable : ∀ ..{ℓ} (A : Set ℓ) → Set ℓ
Decidable A = 𝟘.¬ A ⊕ A

⟦_⟧?↑
  : ∀ ..{ℓ₀}
  → {A : Set ℓ₀}
  → (φ : Decidable A)
  → ∀ {ℓ₁}
  → Set ℓ₁
⟦ ⊕.inl _ ⟧?↑ = 𝟘↑
⟦ ⊕.inr _ ⟧?↑ = 𝟙↑

⟦_⟧?
  : ∀ ..{ℓ₀}
  → {A : Set ℓ₀}
  → (φ : Decidable A)
  → Set
⟦ φ ⟧? = ⟦ φ ⟧?↑
