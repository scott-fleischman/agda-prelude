{-# OPTIONS --without-K #-}

module Prelude.Path where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Unit
open import Prelude.Natural
open import Prelude.Point

infix 0 _≡_

data _≡_ ..{ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

module ≡ where

  private
    module # where
      infixr 1 _<∘_
      infixr 1 _∘>_
      infixr 1 [_]*_
      infixl 2 _⁻¹

      pattern idn = refl

      idn*
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a : A}
        → 𝟙 ⇒ (a ≡ a)
      idn* * = idn

      {-# DISPLAY idn* _ = idn #-}

      cmp
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a b c : A}
        → ((b ≡ c) ⊗ (a ≡ b)) ⇒ (a ≡ c)
      cmp (idn ⊗., idn) = idn

      seq
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a b c : A}
        → ((a ≡ b) ⊗ (b ≡ c)) ⇒ (a ≡ c)
      seq (idn ⊗., idn) = idn

      inv
        : ∀ ..{ℓ} {A : Set ℓ} {a b : A}
        → (a ≡ b) ⇒ (b ≡ a)
      inv idn = idn

      _<∘_
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a b c : A}
        → (ρ₁ : b ≡ c)
        → (ρ₀ : a ≡ b)
        → a ≡ c
      ρ₁ <∘ ρ₀ = cmp (ρ₁ ⊗., ρ₀)
      {-# DISPLAY cmp (ρ₁ ⊗., ρ₀) = ρ₁ <∘ ρ₀ #-}

      _∘>_
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a b c : A}
        → (ρ₀ : a ≡ b)
        → (ρ₁ : b ≡ c)
        → a ≡ c
      ρ₀ ∘> ρ₁ = seq (ρ₀ ⊗., ρ₁)
      {-# DISPLAY seq (ρ₀ ⊗., ρ₁) = ρ₀ ∘> ρ₁ #-}

      _⁻¹ : _
      _⁻¹ = inv
      {-# DISPLAY inv ρ = ρ ⁻¹ #-}

      coe*
        : ∀ ..{ℓ}
        → ∀ {A : Set ℓ} {a b}
        → (Ψ : A → Set₀)
        → (ρ : a ≡ b)
        → (Ψ a ⇒ Ψ b)
      coe* Ψ idn x = x

      [_]*_
        : ∀ ..{ℓ}
        → ∀ {A : Set ℓ} {a b}
        → {Ψ : A → Set₀}
        → (ρ : a ≡ b)
        → (Ψ a ⇒ Ψ b)
      [_]*_ {Ψ = Ψ} ρ ψ = coe* Ψ ρ ψ
      {-# DISPLAY coe* Ψ ρ x = [ ρ ]* x #-}

      ap
        : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁} {a b}
        → (F : A ⇒ B)
        → ((a ≡ b) ⇒ (F a ≡ F b))
      ap F idn = idn

      _$_ : _
      _$_ = ap
      {-# DISPLAY ap f ρ = f $ ρ #-}

  module rel where
    idn
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a : A}
      → refl {a = a} ≡ refl {a = a}
    idn = #.idn

    cmp
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b c : A}
      → {ρ₀ ρ₁ : a ≡ b}
      → {σ₀ σ₁ : b ≡ c}
      → (β : σ₀ ≡ σ₁)
      → (α : ρ₀ ≡ ρ₁)
      → (σ₀ #.<∘ ρ₀) ≡ (σ₁ #.<∘ ρ₁)
    cmp #.idn #.idn = #.idn

    seq
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b c : A}
      → {ρ₀ ρ₁ : a ≡ b}
      → {σ₀ σ₁ : b ≡ c}
      → (α : ρ₀ ≡ ρ₁)
      → (β : σ₀ ≡ σ₁)
      → (ρ₀ #.∘> σ₀) ≡ (ρ₁ #.∘> σ₁)
    seq #.idn #.idn = #.idn

    inv
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b : A}
      → {ρ₀ ρ₁ : a ≡ b}
      → (α : ρ₀ ≡ ρ₁)
      → ρ₀ #.⁻¹ ≡ ρ₁ #.⁻¹
    inv #.idn = #.idn

  module coh where
    open #

    idn-λ
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b : A}
      → (ϕ : a ≡ b)
      → (idn <∘ ϕ) ≡ ϕ
    idn-λ idn = idn

    idn-ρ
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b : A}
      → (ϕ : a ≡ b)
      → (ϕ <∘ idn) ≡ ϕ
    idn-ρ idn = idn

    cmp-α
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b c d : A}
      → (ρ₀ : a ≡ b)
      → (ρ₁ : b ≡ c)
      → (ρ₂ : c ≡ d)
      → ((ρ₂ <∘ ρ₁) <∘ ρ₀) ≡ (ρ₂ <∘ (ρ₁ <∘ ρ₀))
    cmp-α idn idn idn = idn

    seq-α
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b c d : A}
      → (ρ₀ : a ≡ b)
      → (ρ₁ : b ≡ c)
      → (ρ₂ : c ≡ d)
      → (ρ₀ ∘> (ρ₁ ∘> ρ₂)) ≡ ((ρ₀ ∘> ρ₁) ∘> ρ₂)
    seq-α idn idn idn = idn

    inv-λ
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b : A}
      → (ϕ : a ≡ b)
      → (ϕ ⁻¹ <∘ ϕ) ≡ idn
    inv-λ idn = idn

    inv-ρ
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → {a b : A}
      → (ϕ : a ≡ b)
      → (ϕ <∘ ϕ ⁻¹) ≡ idn
    inv-ρ idn = idn

    coe-coh
      : ∀ ..{ℓ}
      → ∀ {A : Set ℓ}
      → (Ψ : A → Set₀)
      → ∀ {a b}
      → {ρ₀ ρ₁ : a ≡ b}
      → (σ : ρ₀ ≡ ρ₁)
      → {ψ : Ψ a}
      → coe* Ψ ρ₀ ψ ≡ coe* Ψ ρ₁ ψ
    coe-coh Ψ idn = idn

    coe-idn
      : ∀ ..{ℓ}
      → ∀ {A : Set ℓ}
      → (Ψ : A → Set₀)
      → ∀ {a}
      → {ψ : Ψ a}
      → coe* {a = a} Ψ idn ≡ ⇒.idn
    coe-idn Ψ = idn

    coe-cmp
      : ∀ ..{ℓ}
      → ∀ {A : Set ℓ}
      → (Ψ : A → Set₀)
      → ∀ {a b c}
      → (ρ₁ : b ≡ c)
      → (ρ₀ : a ≡ b)
      → {ψ : Ψ a}
      → coe* Ψ (ρ₁ <∘ ρ₀) ψ ≡ (coe* Ψ ρ₁ ⇒.<∘ coe* Ψ ρ₀) ψ
    coe-cmp Ψ idn idn = idn

    coe-inv-λ
      : ∀ ..{ℓ}
      → ∀ {A : Set ℓ}
      → (Ψ : A → Set₀)
      → ∀ {a b}
      → (ρ : a ≡ b)
      → {ψ : Ψ a}
      → coe* Ψ (ρ ⁻¹ <∘ ρ) ψ ≡ coe* Ψ idn ψ
    coe-inv-λ Ψ = coe-coh Ψ Π.<∘ inv-λ

    coe-inv-ρ
      : ∀ ..{ℓ}
      → ∀ {A : Set ℓ}
      → (Ψ : A → Set₀)
      → ∀ {a b}
      → (ρ : a ≡ b)
      → {ψ : Ψ b}
      → coe* Ψ (ρ <∘ ρ ⁻¹) ψ ≡ coe* Ψ idn ψ
    coe-inv-ρ Ψ = coe-coh Ψ Π.<∘ inv-ρ

  open # public

  ind#
    : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {a : A}
    → (Φ : (b : A) → a ≡ b → Set ℓ₁)
    → (ϕ : Φ a idn)
    → ((b : A) (ψ : a ≡ b) → Φ b ψ)
  ind# Φ ϕ b idn = ϕ

  ind
    : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀}
    → (Φ : (a b : A) → a ≡ b → Set ℓ₁)
    → (ϕ : (a : A) → Φ a a idn)
    → ((a b : A) (ψ : a ≡ b) → Φ a b ψ)
  ind Φ ϕ a = ind# (Φ a) (ϕ a)

  loop : ∀ ..{ℓ} → Pt ℓ → Pt ℓ
  Pt.type (loop xs) = Pt.base xs ≡ Pt.base xs
  Pt.base (loop xs) = idn

  loop# : ∀ ..{ℓ} → Nat → Pt ℓ → Pt ℓ
  loop# ze xs = xs
  loop# (su n) xs = loop# n (loop xs)
