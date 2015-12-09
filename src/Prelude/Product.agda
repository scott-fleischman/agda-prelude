{-# OPTIONS --without-K #-}

module Prelude.Product where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Unit

module ⊗ where
  record _⊗_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public

  open ⇒
    using (_<∘_)

  el
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {Ψ : A ⊗ B → Set ℓ₂}
    → (k : (x : A) (y : B) → Ψ (x , y))
    → (∀ x → Ψ x)
  el k (x , y) = k x y

  ⟨_,_⟩ : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {X : Set ℓ₀}
    → {A : Set ℓ₁}
    → {B : Set ℓ₂}
    → (f : X → A)
    → (g : X → B)
    → (X → A ⊗ B)
  ⟨ f , g ⟩ x = (f x , g x)

  ⟨_⊗_⟩
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X₀ : Set ℓ₀}
    → {X₁ : Set ℓ₁}
    → {A : Set ℓ₂}
    → {B : Set ℓ₃}
    → (f : X₀ → A)
    → (g : X₁ → B)
    → (X₀ ⊗ X₁ → A ⊗ B)
  ⟨ f ⊗ g ⟩ = ⟨ f ⇒.<∘ fst , g ⇒.<∘ snd ⟩

  α₀
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)
  α₀ = ⟨ fst <∘ fst , ⟨ snd <∘ fst , snd ⟩ ⟩

  α₁
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    →  A ⊗ (B ⊗ C) → (A ⊗ B) ⊗ C
  α₁ = ⟨ ⟨ fst , fst <∘ snd ⟩ , snd <∘ snd ⟩

  β
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (A ⊗ B) → (B ⊗ A)
  β = ⟨ snd , fst ⟩

  λ₀
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟙 ⊗ A) → A
  λ₀ = snd

  λ₁
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → A → (𝟙 ⊗ A)
  λ₁ = ⟨ 𝟙.! , ⇒.idn ⟩

  ρ₀
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊗ 𝟙) → A
  ρ₀ = fst

  ρ₁
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → A → (A ⊗ 𝟙)
  ρ₁ = ⟨ ⇒.idn , 𝟙.! ⟩

  open import Prelude.Product.Indexed public

open ⊗ public
  using (_⊗_)
  hiding (module _⊗_)
