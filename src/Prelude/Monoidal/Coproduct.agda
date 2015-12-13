{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Coproduct where

open import Agda.Primitive
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Void

module ⊕ where
  infix 1 _⊕_
  infix 1 [_,_]

  open ⊗
    using (_,_)
    using (fst)
    using (snd)
    using (⟨_,_⟩)
    using (⟨_⊗_⟩)

  open ⇒
    using (idn)
    using (_<∘_)
    using (λ⇑)
    using (λ⇓)

  data _⊕_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

  el
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {Ψ : A ⊕ B → Set ℓ₂}
    → (k₀ : (a : A) → Ψ (inl a))
    → (k₁ : (b : B) → Ψ (inr b))
    → (∀ x → Ψ x)
  el k₀ k₁ (inl a) = k₀ a
  el k₀ k₁ (inr b) = k₁ b

  -- cotupling
  [_,_]
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {X : Set ℓ₂}
    → (f : A → X)
    → (g : B → X)
    → (A ⊕ B → X)
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  -- functoriality
  [_⊕_]
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X₀ : Set ℓ₀}
    → {X₁ : Set ℓ₁}
    → {A : Set ℓ₂}
    → {B : Set ℓ₃}
    → (f : A → X₀)
    → (g : B → X₁)
    → (A ⊕ B → X₀ ⊕ X₁)
  [ f ⊕ g ] = [ inl <∘ f , inr <∘ g ]

  -- associator isomorphism
  α⇒
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊕ B) ⊕ C) ⇒ (A ⊕ (B ⊕ C))
  α⇒ = [ [ inl , inr <∘ inl ] , inr <∘ inr ]

  α⇐
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → ((A ⊕ B) ⊕ C) ⇐ (A ⊕ (B ⊕ C))
  α⇐ = [ inl <∘ inl , [ inl <∘ inr , inr ] ]

  -- left unitor isomorphism
  λ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟘 ⊕ A) ⇒ A
  λ⇒ = [ 𝟘.¡ , ⇒.idn ]

  λ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (𝟘 ⊕ A) ⇐ A
  λ⇐ = inr

  -- right unitor isomorphism
  ρ⇒
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊕ 𝟘) ⇒ A
  ρ⇒ = [ ⇒.idn , 𝟘.¡ ]

  ρ⇐
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (A ⊕ 𝟘) ⇐ A
  ρ⇐ = inl

  -- braiding
  β
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (A ⊕ B) ⇒ (B ⊕ A)
  β = [ inr , inl ]

  -- distributor isomorphism
  δ⇒
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (A ⊗ B) ⊕ (A ⊗ C) ⇒ A ⊗ (B ⊕ C)
  δ⇒ = [ ⟨ idn ⊗ inl ⟩ , ⟨ fst , inr <∘ snd ⟩ ]

  δ⇐
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (A ⊗ B) ⊕ (A ⊗ C) ⇐ A ⊗ (B ⊕ C)
  δ⇐ = λ⇓[ a ] [ inl <∘ _,_ a , inr <∘ _,_ a ]

  open import Prelude.Monoidal.Coproduct.Indexed public

open ⊕ public
  using (_⊕_)
  hiding (module _⊕_)
