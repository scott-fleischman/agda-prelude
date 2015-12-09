{-# OPTIONS --without-K #-}

module Prelude.Families where

open import Agda.Primitive
open import Prelude.Coproduct.Indexed
open import Prelude.Product.Indexed
open import Prelude.Path

Fam
  : ∀ ..{ℓ₀} ..ℓ₁
  → (A : Set ℓ₀)
  → Set _
Fam ℓ₁ A = A → Set ℓ₁

Fib
  : ∀ ..{ℓ₀} ..ℓ₁
  → (I : Set ℓ₀)
  → Set _
Fib ℓ₁ I = Σ[ Set ℓ₁ ∋ X ] (X → I)

℘ : ∀ ..{ℓ₀ ℓ₁}
  → (A : Set ℓ₀)
  → _
℘ {ℓ₁ = ℓ₁} = Fam ℓ₁
{-# DISPLAY Fam ℓ A = ℘ {ℓ} A #-}

SET/_
  : ∀ ..{ℓ₀ ℓ₁}
  → (I : Set ℓ₀)
  → _
SET/_ {ℓ₁ = ℓ₁} = Fib ℓ₁
{-# DISPLAY Fib ℓ I = SET/_ {ℓ} I #-}

module Fam where
  total
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → (Ψ : Fam ℓ₁ I)
    → Set _
  total {I = I} Ψ = Σ I Ψ

  display
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → {Ψ : Fam ℓ₁ I}
    → (total Ψ → I)
  display = Σ.fst

  map
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → {Ψ : Fam ℓ₁ I}
    → ((E : total Ψ) → Ψ (display E))
  map = Σ.snd

  inv
    : ∀ ..{ℓ₀ ℓ₁}
    → {E : Set ℓ₀}
    → {I : Set ℓ₁}
    → (p : E → I)
    → Fam _ I
  inv {E = E} p i = Σ[ E ∋ e ] (p e ≡ i)

  [_]⁻¹_ : _
  [_]⁻¹_ = inv
  {-# DISPLAY inv p i = [ p ]⁻¹ i #-}

  fib
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → Fib (ℓ₀ ⊔ ℓ₁) I
    → Fam (ℓ₀ ⊔ ℓ₁) I
  fib = inv Π.<∘ map

module Fib where
  fam
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → Fam (ℓ₁) I
    → Fib (ℓ₀ ⊔ ℓ₁) I
  fam Ψ = (Fam.total Ψ Σ., Fam.display)
