{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Product where

open import Agda.Primitive
open import Prelude.Display
open import Prelude.Monoidal.Exponential.Boot
open import Prelude.Monoidal.Unit

module ⊗ where
  infixr 0 _,_

  record _⊗_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public

  open ⇒
    using (idn)
    using (_⟔_)
    using (_⟓_)

  elim
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {Ψ : A ⊗ B → Set ℓ₂}
    → (k : (x : A) (y : B) → Ψ (x , y))
    → (∀ x → Ψ x)
  elim k (x , y) = k x y

  -- tupling
  ⟨_,_⟩ : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {X : Set ℓ₀}
    → {A : Set ℓ₁}
    → {B : Set ℓ₂}
    → (f : X → A)
    → (g : X → B)
    → (X → A ⊗ B)
  ⟨ f , g ⟩ x = (f x , g x)

  -- functoriality
  ⟨_⊗_⟩
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X₀ : Set ℓ₀}
    → {X₁ : Set ℓ₁}
    → {A : Set ℓ₂}
    → {B : Set ℓ₃}
    → (f : X₀ → A)
    → (g : X₁ → B)
    → (X₀ ⊗ X₁ → A ⊗ B)
  ⟨ f ⊗ g ⟩ = ⟨ f ⟔ fst , g ⟔ snd ⟩

  transpose
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → {D : Set ℓ₃}
    → (A ⊗ B) ⊗ (C ⊗ D) ⇒ (A ⊗ C) ⊗ (B ⊗ D)
  transpose = ⟨ ⟨ fst ⊗ fst ⟩ , ⟨ snd ⊗ snd ⟩ ⟩

  -- associator isomorphism
  α⇒
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊗ B) ⊗ C) ⇒ (A ⊗ (B ⊗ C))
  α⇒ = ⟨ fst ⟔ fst , ⟨ snd ⟔ fst , snd ⟩ ⟩

  α⇐
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊗ B) ⊗ C) ⇐ (A ⊗ (B ⊗ C))
  α⇐ = ⟨ ⟨ fst , fst ⟔ snd ⟩ , snd ⟔ snd ⟩

  -- left unitor isomorphism
  λ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟙 ⊗ A) ⇒ A
  λ⇒ = snd

  λ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟙 ⊗ A) ⇐ A
  λ⇐ = ⟨ 𝟙.! , ⇒.idn ⟩

  -- right unitor isomorphism
  ρ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊗ 𝟙) ⇒ A
  ρ⇒ = fst

  ρ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊗ 𝟙) ⇐ A
  ρ⇐ = ⟨ ⇒.idn , 𝟙.! ⟩

  -- braiding
  β
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (A ⊗ B) ⇒ (B ⊗ A)
  β = ⟨ snd , fst ⟩

  open import Prelude.Monoidal.Product.Indexed public

  {-# DISPLAY fst p = ᵈ.fst p #-}
  {-# DISPLAY snd p = ᵈ.snd p #-}
  {-# DISPLAY _⊗_ A B = A ᵈ.ᵈ.⊗ B #-}

open ⊗ public
  using (_⊗_)
  hiding (module _⊗_)
