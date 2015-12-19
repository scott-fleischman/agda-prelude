{-# OPTIONS --without-K #-}

module Prelude.Families where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
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
  open Π
    using (_⟔_)

  _∈_
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → (a : A)
    → (Ψ : Fam ℓ₁ A)
    → Set ℓ₁
  a ∈ Ψ = Ψ a

  _⊆[_]_
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → (Ψ : Fam ℓ₁ A)
    → (a : A)
    → (Φ : Fam ℓ₂ A)
    → Set (ℓ₁ ⊔ ℓ₂)
  Ψ ⊆[ a ] Φ = a ∈ Ψ → a ∈ Φ

  _⊆_
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → (Ψ : Fam ℓ₁ A)
    → (Φ : Fam ℓ₂ A)
    → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
  Ψ ⊆ Φ = ∀ {x} → Ψ ⊆[ x ] Φ

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
    → ((E : total Ψ) → display E ∈ Ψ)
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
  fib = inv ⟔ map
  {-# DISPLAY inv ⟔ map = fib #-}

  Σ[_]
    : {A : Set}
    → {B : Set}
    → (f : A ⇒ B)
    → Fam lzero A ⇒ Fam lzero B
  Σ[ f ] Ψ b = ⊕.Σ[ _ ∋ a ] ((f a ≡ b) ⊗ (a ∈ Ψ))

  Π[_]
    : {A : Set}
    → {B : Set}
    → (f : A ⇒ B)
    → Fam lzero A ⇒ Fam lzero B
  Π[ f ] Ψ b = ⊗.Π[ _ ∋ a ] ((b ≡ f a) ⇒ (a ∈ Ψ))

module Fib where
  fam
    : ∀ ..{ℓ₀ ℓ₁}
    → {I : Set ℓ₀}
    → Fam (ℓ₁) I
    → Fib (ℓ₀ ⊔ ℓ₁) I
  fam Ψ = (Fam.total Ψ Σ., Fam.display)
