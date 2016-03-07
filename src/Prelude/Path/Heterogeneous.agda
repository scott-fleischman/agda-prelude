module Prelude.Path.Heterogeneous where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Unit
open import Prelude.Path
open import Prelude.Point

infix 0 _≅_

data _≅_ ..{ℓ} {A : Set ℓ} (a : A) : {B : Set ℓ} (b : B) → Set ℓ where
    refl : a ≅ a

module ≅ where

  pattern idn = refl

  private
    module # where
      infixr 1 _⟔_
      infixr 1 _⟓_
      infixr 3 [_]*_
      infixl 2 _⁻¹

      ι
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a b : A}
        → a ≡ b
        → a ≅ b
      ι refl = refl

      set
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → {a : A}{b : B}
        → a ≅ b
        → A ≡ B
      set refl = refl

      coh
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → {a : A}{b : B}
        → (ρ : a ≅ b)
        → ≡.coe* ⇒.↻ (set ρ) a ≡ b
      coh refl = refl

      idn*
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → {a : A}
        → 𝟙 ⇒ (a ≅ a)
      idn* * = refl

      cmp
        : ∀ ..{ℓ}
        → {A B C : Set ℓ}
        → {a : A}{b : B}{c : C}
        → ((b ≅ c) ⊗ (a ≅ b)) ⇒ (a ≅ c)
      cmp (refl , refl) = refl

      seq
        : ∀ ..{ℓ}
        → {A B C : Set ℓ}
        → {a : A}{b : B}{c : C}
        → ((a ≅ b) ⊗ (b ≅ c)) ⇒ (a ≅ c)
      seq (refl , refl) = refl

      inv
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → {a : A}{b : B}
        → (a ≅ b) ⇒ (b ≅ a)
      inv refl = refl

      _⟔_
        : ∀ ..{ℓ}
        → {A B C : Set ℓ}
        → {a : A}{b : B}{c : C}
        → (ρ₁ : b ≅ c)
        → (ρ₀ : a ≅ b)
        → a ≅ c
      ρ₁ ⟔ ρ₀ = cmp (ρ₁ , ρ₀)

      _⟓_
        : ∀ ..{ℓ}
        → {A B C : Set ℓ}
        → {a : A}{b : B}{c : C}
        → (ρ₀ : a ≅ b)
        → (ρ₁ : b ≅ c)
        → a ≅ c
      ρ₀ ⟓ ρ₁ = seq (ρ₀ , ρ₁)

      _⁻¹ = inv

      ap[_]
        : ∀ ..{ℓ₀ ℓ₁}
        → {A B : Set ℓ₀}{R : Set ℓ₁}
        → {a : A}{b : B}
        → a ≅ b
        → (A → R) ⇒ (B → R)
      ap[ refl ] P x = P x

      coe*
        : ∀ ..{ℓ₀ ℓ₁}
        → {A B : Set ℓ₀}
        → {a : A}{b : B}
        → (Ψ : A → Set ℓ₁)
        → (ρ : a ≅ b)
        → (Ψ a ⇒ ap[ ρ ] Ψ b)
      coe* Ψ refl x = x

      [_]*_
        : ∀ ..{ℓ₀ ℓ₁}
        → {A B : Set ℓ₀}
        → {a : A}{b : B}
        → {Ψ : A → Set ℓ₁}
        → (ρ : a ≅ b)
        → (Ψ a ⇒ ap[ ρ ] Ψ b)
      [_]*_ {Ψ = Ψ} ρ ψ = coe* Ψ ρ ψ

      ap¹
        : ∀ ..{ℓ₀ ℓ₁}
        → {A₀ A₁ : Set ℓ₀} {B : Set ℓ₁}
        → {a₀ : A₀}{a₁ : A₁}
        → (F : A₀ ⇒ B)
        → (ρ : a₀ ≅ a₁)
        → (F a₀ ≅ ap[ ρ ] F a₁)
      ap¹ F refl = refl

      ap²
        : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
        → {A₀ A₁ : Set ℓ₀} {B₀ B₁ : Set ℓ₁} {C : Set ℓ₂}
        → {a₀ : A₀}{a₁ : A₁}
        → {b₀ : B₀}{b₁ : B₁}
        → (F : A₀ → B₀ → C)
        → (α : a₀ ≅ a₁)
        → (β : b₀ ≅ b₁)
        → F a₀ b₀ ≅ ap[ α ] (λ a → ap[ β ] (F a) b₁) a₁
      ap² F refl refl = refl

      _·_ : _
      _·_ = ap¹

      {-# DISPLAY cmp (ρ₁ , ρ₀) = ρ₁ ⟔ ρ₀ #-}
      {-# DISPLAY seq (ρ₀ , ρ₁) = ρ₀ ⟓ ρ₁ #-}
      {-# DISPLAY inv ρ = ρ ⁻¹ #-}
      {-# DISPLAY coe* Ψ ρ x = [ ρ ]* x #-}
      {-# DISPLAY ap¹ f ρ = f · ρ #-}

  module ≾ where
    cmp
      : ∀ ..{ℓ}
      → {A B C : Set ℓ}
      → {a : A}{b : B}{c : C}
      → {ρ₀ ρ₁ : a ≅ b}
      → {σ₀ σ₁ : b ≅ c}
      → (β : σ₀ ≅ σ₁)
      → (α : ρ₀ ≅ ρ₁)
      → (σ₀ #.⟔ ρ₀) ≅ (σ₁ #.⟔ ρ₁)
    cmp refl refl = refl

    seq
      : ∀ ..{ℓ}
      → {A B C : Set ℓ}
      → {a : A}{b : B}{c : C}
      → {ρ₀ ρ₁ : a ≅ b}
      → {σ₀ σ₁ : b ≅ c}
      → (α : ρ₀ ≅ ρ₁)
      → (β : σ₀ ≅ σ₁)
      → (ρ₀ #.⟓ σ₀) ≅ (ρ₁ #.⟓ σ₁)
    seq refl refl = refl

    inv
      : ∀ ..{ℓ}
      → {A B : Set ℓ}
      → {a : A}{b : B}
      → {ρ₀ ρ₁ : a ≅ b}
      → (α : ρ₀ ≅ ρ₁)
      → ρ₀ #.⁻¹ ≅ ρ₁ #.⁻¹
    inv refl = refl

  module ⊢ where
    open #

    λ⇒
      : ∀ ..{ℓ}
      → {A B : Set ℓ}
      → {a : A}{b : B}
      → (ϕ : a ≅ b)
      → (refl ⟔ ϕ) ≅ ϕ
    λ⇒ refl = refl

    ρ⇒
      : ∀ ..{ℓ}
      → {A B : Set ℓ}
      → {a : A}{b : B}
      → (ϕ : a ≅ b)
      → (ϕ ⟔ refl) ≅ ϕ
    ρ⇒ refl = refl

    α⇒
      : ∀ ..{ℓ}
      → {A B C D : Set ℓ}
      → {a : A}{b : B}{c : C}{d : D}
      → (ρ₀ : a ≅ b)
      → (ρ₁ : b ≅ c)
      → (ρ₂ : c ≅ d)
      → ((ρ₂ ⟔ ρ₁) ⟔ ρ₀) ≅ (ρ₂ ⟔ (ρ₁ ⟔ ρ₀))
    α⇒ refl refl refl = refl

    λ⁻¹
      : ∀ ..{ℓ}
      → {A B : Set ℓ}
      → {a : A}{b : B}
      → (ϕ : a ≅ b)
      → _≅_ (ϕ ⁻¹ ⟔ ϕ) {B = a ≅ a} refl
    λ⁻¹ refl = refl

    ρ⁻¹
      : ∀ ..{ℓ}
      → {A B : Set ℓ}
      → {a : A}{b : B}
      → (ϕ : a ≅ b)
      → _≅_ (ϕ ⟔ ϕ ⁻¹) {B = b ≅ b} refl
    ρ⁻¹ refl = refl

    module coe where
      coe-coh
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → (Ψ : A → Set₀)
        → {a : A}{b : B}
        → {ρ₀ ρ₁ : a ≅ b}
        → (σ : ρ₀ ≅ ρ₁)
        → {ψ : Ψ a}
        → coe* Ψ ρ₀ ψ ≅ coe* Ψ ρ₁ ψ
      coe-coh Ψ refl = refl

      coe-refl
        : ∀ ..{ℓ}
        → {A : Set ℓ}
        → (Ψ : A → Set₀)
        → {a : A}
        → {ψ : Ψ a}
        → coe* {a = a} Ψ refl ≅ ⇒.↻
      coe-refl Ψ = refl

      coe-cmp
        : ∀ ..{ℓ}
        → {A B C : Set ℓ}
        → (Ψ : A → Set₀)
        → {a : A}
        → {b : B}
        → {c : C}
        → (β : b ≅ c)
        → (α : a ≅ b)
        → (γ : a ≅ c)
        → {ψ : Ψ a}
        → coe* Ψ (β ⟔ α) ψ ≅ coe* Ψ γ ψ
      coe-cmp Ψ refl refl refl = refl

      coe-inv-λ
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → (Ψ : A → Set₀)
        → {a : A}{b : B}
        → (ρ : a ≅ b)
        → {ψ : Ψ a}
        → coe* Ψ (ρ ⁻¹ ⟔ ρ) ψ ≅ coe* Ψ refl ψ
      coe-inv-λ Ψ ρ = coe-coh Ψ (λ⁻¹ ρ)

      coe-inv-ρ
        : ∀ ..{ℓ}
        → {A B : Set ℓ}
        → (Ψ : A → Set₀)
        → {a : A}{b : B}
        → (ρ : a ≅ b)
        → {ψ : ap[ ρ ] Ψ b}
        → coe* (ap[ ρ ] Ψ) (ρ ⟔ ρ ⁻¹) ψ ≅ coe* (ap[ ρ ] Ψ) refl ψ
      coe-inv-ρ Ψ ρ = coe-coh (ap[ ρ ] Ψ) (ρ⁻¹ ρ)

  open # public

  record From {ℓ} {A B : Set ℓ} (dom : A) : Set ℓ where
    constructor [_]
    field
      {cod} : B
      π : dom ≅ cod
  syntax From {A = A} dom = dom ↘ A
  open From public

  elim
    : ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {a : A}
    → (Ψ : a ↘ A → Set ℓ₁)
    → (⊙ : Ψ [ refl ])
    → Π (a ↘ A) Ψ
  elim Ψ ⊙ [ refl ] = ⊙
