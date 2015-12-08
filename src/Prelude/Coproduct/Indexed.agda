module Prelude.Coproduct.Indexed where

open import Agda.Primitive
open import Prelude.Product.Indexed

module Σ where
  infix 0 Σ
  infix 1 ⟨_,_⟩
  infixr 1 _,_

  record Σ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : A → Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  syntax Σ A (λ x → B) = Σ[ A ∋ x ] B

  el : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀} {B : A → Set ℓ₁} {Φ : Σ A B → Set ℓ₂}
    → (k : (x : A) (y : B x) → Φ (x , y))
    → (∀ x → Φ x)
  el k (x , y) = k x y

  ⟨_,_⟩
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {X : Set ℓ₀}
    → {A : X → Set ℓ₁}
    → {B : ∀ {x} → A x → Set ℓ₂}
    → (f : (x : X) → A x)
    → (g : (x : X) → B (f x))
    → ((x : X) → Σ (A x) B)
  ⟨ f , g ⟩ x = (f x , g x)

  ⟨_⊗_⟩
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X₀ : Set ℓ₀}
    → {X₁ : X₀ → Set ℓ₁}
    → {A : Set ℓ₂}
    → {B : A → Set ℓ₃}
    → (f : X₀ → A)
    → (g : ∀ {x₀} → X₁ x₀ → B (f x₀))
    → (Σ X₀ X₁ → Σ A B)
  ⟨ f ⊗ g ⟩ = ⟨ f Π.<∘ fst , g Π.<∘ snd ⟩

open Σ public
  using (Σ)
  hiding (module Σ)
