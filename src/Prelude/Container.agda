module Prelude.Container where

open import Prelude.Coproduct
open import Prelude.Diagonal
open import Prelude.Families
open import Prelude.Functor
open import Prelude.One
open import Prelude.Path
open import Prelude.Product
open import Prelude.Zero

module Con where
  infixr 0 Σ◃
  infixr 0 Π◃
  infixr 9 _∘◃_

  record Con : Set₁ where
    no-eta-equality
    constructor _◃_
    field
      op : Set₀
      ar : (ϑ : op) → Set₀
  open Con public

  _-_ : ∀ ..{ℓ₀ ℓ₁} (X : Set ℓ₀) (x : X) → Set _
  _-_ {ℓ₁ = ℓ₁} X x = ⊕.Σ.[ X ∋ y ] 𝟘.¬_ {ℓ₁ = ℓ₁} (x ≡ y)

  κ◃ : Set → Con
  κ◃ A = A ◃ Δ[ 𝟘 ]

  _+◃_ : (Σ₀ Σ₁ : Con) → Con
  (𝒪₀ ◃ 𝔄₀) +◃ (𝒪₁ ◃ 𝔄₁) = (𝒪₀ ⊕ 𝒪₁) ◃ ⊕.[ 𝔄₀ , 𝔄₁ ]

  _×◃_ : (Σ₀ Σ₁ : Con) → Con
  (𝒪₀ ◃ 𝔄₀) ×◃ (𝒪₁ ◃ 𝔄₁) = (𝒪₀ ⊗ 𝒪₁) ◃ ⊗.el λ ϑ₀ ϑ₁ → 𝔄₀ ϑ₀ ⊕ 𝔄₁ ϑ₁

  Σ◃ : (A : Set) (B : A → Con) → Con
  Σ◃ A B = ⊕.Σ A (op ⊗.Π.<∘ B) ◃ ⊕.Σ.el (ar ⊗.Π.<∘ B)

  Π◃ : (A : Set) (B : A → Con) → Con
  Π◃ A B = ⊗.Π A (op ⊗.Π.<∘ B) ◃ λ f → ⊕.[ A ∋ a ] ar (B a) (f a)

  syntax Σ◃ A (λ x → B) = Σ◃[ A ∋ x ] B
  syntax Π◃ A (λ x → B) = Π◃[ A ∋ x ] B

  _∘◃_ : (Σ₀ Σ₁ : Con) → Con
  (𝒪 ◃ 𝔄) ∘◃ Σ =
    Σ◃[ 𝒪 ∋ ϑ ] Π◃[ 𝔄 ϑ ∋ α ] Σ

  _→◃_ : (Σ₀ Σ₁ : Con) → Set
  (𝒪₀ ◃ 𝔄₀) →◃ (𝒪₁ ◃ 𝔄₁) =
    ⊕.Σ.[ (𝒪₀ → 𝒪₁) ∋ f ] ⊗.Π.[ 𝒪₀ ∋ ϑ ] (𝔄₁ (f ϑ) → 𝔄₀ ϑ)

  ∂ : Con → Con
  ∂ (𝒪 ◃ 𝔄) = ⊕.Σ 𝒪 𝔄 ◃ ⊕.Σ.el λ ϑ α → 𝔄 ϑ - α

  module _ (Σ : Con) where
    infixr 2 ⟦_⟧◃_

    ⟦_⟧◃_ : (X : Set) → Set
    ⟦_⟧◃_ X = ⊕.Σ.[ op Σ ∋ ϑ ] (ar Σ ϑ → X)

    pattern F◃ ϑ ρ = ϑ ⊕.Σ., ρ

    map◃ : ∀ {X Y} → (X → Y) → (⟦_⟧◃_ X → ⟦_⟧◃_ Y)
    map◃ f (F◃ ϑ ρ) = F◃ ϑ (f ⊗.Π.<∘ ρ)

    module _ {X} where
      infix 4 _∈_

      [_]□ : 𝔓.t X → 𝔓.t (⟦_⟧◃_ X)
      [_]□ Φ (F◃ ϑ ρ) = ⊗.Π.[ ar Σ ϑ ∋ α ] Φ (ρ α)

      [_]◇ : 𝔓.t X → 𝔓.t (⟦_⟧◃_ X)
      [_]◇ Φ (F◃ ϑ ρ) = ⊕.Σ.[ ar Σ ϑ ∋ α ] Φ (ρ α)

      _∈_ : X → 𝔓.t (⟦_⟧◃_ X)
      x ∈ Γ = [_]◇ (x ≡_) Γ

  instance
    functor : ∀ {Σ} → Functor ⟦ Σ ⟧◃_
    Functor.#.map functor f = ⊕.Σ.⟨ ⊗.Π.idn ⊗ ⊗.Π.cmp f ⟩

open Con public
  using (Con)
  hiding (module Con)
