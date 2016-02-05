{-# OPTIONS --without-K #-}

module Prelude.Signature where

open import Agda.Primitive
open import Prelude.Families
open import Prelude.Functor
  using (Functor)
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Diagonal
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Unit
open import Prelude.Monoidal.Void
open import Prelude.Path

module Sig where
  infixr 0 Σ◃
  infixr 0 Π◃

  record Sig : Set₁ where
    no-eta-equality
    constructor _◃_
    field
      op : Set₀
      ar : (ϑ : op) → Set₀
  open Sig public

  _-_ : ∀ ..{ℓ₀ ℓ₁} (X : Set ℓ₀) (x : X) → Set _
  _-_ {ℓ₁ = ℓ₁} X x = Σ[ X ∋ y ] 𝟘↑.¬_ {ℓ = ℓ₁} (x ≡ y)

  κ◃ : Set → Sig
  κ◃ A = A ◃ Δ.ʲ[ 𝟘 ]
  {-# DISPLAY _◃_ A Δ[ 𝟘 ] = κ◃ A #-}

  _+◃_ : (⊢Σ₀ ⊢Σ₁ : Sig) → Sig
  (𝒪₀ ◃ 𝔄₀) +◃ (𝒪₁ ◃ 𝔄₁) = (𝒪₀ ⊕ 𝒪₁) ◃ ⊕.[ 𝔄₀ , 𝔄₁ ]

  _×◃_ : (⊢Σ₀ ⊢Σ₁ : Sig) → Sig
  (𝒪₀ ◃ 𝔄₀) ×◃ (𝒪₁ ◃ 𝔄₁) = (𝒪₀ ⊗ 𝒪₁) ◃ ⊗.elim λ ϑ₀ ϑ₁ → 𝔄₀ ϑ₀ ⊕ 𝔄₁ ϑ₁

  Σ◃ : (A : Set) (B : A → Sig) → Sig
  Σ◃ A B = Σ A (op Π.⟔ B) ◃ Σ.el (ar Π.⟔ B)

  Π◃ : (A : Set) (B : A → Sig) → Sig
  Π◃ A B = Π A (op Π.⟔ B) ◃ λ f → Σ[ A ∋ a ] ar (B a) (f a)

  syntax Σ◃ A (λ x → B) = Σ◃[ A ∋ x ] B
  syntax Π◃ A (λ x → B) = Π◃[ A ∋ x ] B

  _⟔◃_ : (⊢Σ₀ ⊢Σ₁ : Sig) → Sig
  (𝒪₀ ◃ 𝔄₀) ⟔◃ ⊢Σ₁ = Σ◃[ 𝒪₀ ∋ ϑ ] Π◃[ 𝔄₀ ϑ ∋ α ] ⊢Σ₁

  _⟓◃_ : (⊢Σ₀ ⊢Σ₁ : Sig) → Sig
  ⊢Σ₀ ⟓◃ (𝒪₁ ◃ 𝔄₁) = Σ◃[ 𝒪₁ ∋ ϑ ] Π◃[ 𝔄₁ ϑ ∋ α ] ⊢Σ₀

  _→◃_ : (⊢Σ₀ ⊢Σ₁ : Sig) → Set
  (𝒪₀ ◃ 𝔄₀) →◃ (𝒪₁ ◃ 𝔄₁) = Σ[ (𝒪₀ → 𝒪₁) ∋ f ] Π[ 𝒪₀ ∋ ϑ ] (𝔄₁ (f ϑ) → 𝔄₀ ϑ)

  ∂ : Sig → Sig
  ∂ (𝒪 ◃ 𝔄) = Σ 𝒪 𝔄 ◃ Σ.el λ ϑ α → 𝔄 ϑ - α

  module _ (⊢Σ : Sig) where
    infixr 2 ⟦_⟧◃

    ⟦_⟧◃ : (X : Set) → Set
    ⟦_⟧◃ X = Σ[ op ⊢Σ ∋ ϑ ] (ar ⊢Σ ϑ → X)

    pattern F◃ ϑ ρ = ϑ ▸ ρ

    map : ∀ {X Y} → (X → Y) → (⟦_⟧◃ X → ⟦_⟧◃ Y)
    map f (F◃ ϑ ρ) = F◃ ϑ (f Π.⟔ ρ)

    module _ {X} where
      infix 4 _∈_

      [_]□ : ∀ ..{ℓ} → Fam ℓ X → Fam ℓ (⟦_⟧◃ X)
      [_]□ Φ (F◃ ϑ ρ) = Π[ ar ⊢Σ ϑ ∋ α ] Φ (ρ α)

      [_]◇ : ∀ ..{ℓ} → Fam ℓ X → Fam ℓ (⟦_⟧◃ X)
      [_]◇ Φ (F◃ ϑ ρ) = Σ[ ar ⊢Σ ϑ ∋ α ] Φ (ρ α)

      _∈_ : X → Fam _ (⟦_⟧◃ X)
      x ∈ Γ = [_]◇ (x ≡_) Γ

  instance
    functor : ∀ {Σ} → Functor ⟦ Σ ⟧◃
    Functor.map (functor {Σ}) = map Σ

open Sig public
  using (Sig)
  using (_◃_)
  using (⟦_⟧◃)
  hiding (module Sig)
