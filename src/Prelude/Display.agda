{-# OPTIONS --without-K #-}

module Prelude.Display where

module ᵈ where
  private
    record Op : Set where
      no-eta-equality

  infix 0 _→₁_
  infix 0 _→₂_
  infixr 1 _⟔_
  infixr 1 _⟓_
  infixl 2 _⁻¹
  infixr 4 _·_

  module ᵈ where
    _⊗_ : Op
    _⊗_ = record {}

    _⊕_ : Op
    _⊕_ = record {}

  ∣_∣ : Op
  ∣_∣ = record {}

  _⇒_ : Op
  _⇒_ = record {}

  _⇐_ : Op
  _⇐_ = record {}

  ↻₀ : Op
  ↻₀ = record {}

  _→₁_ : Op
  _→₁_ = record {}

  _→₂_ : Op
  _→₂_ = record {}

  _→₁₂_ : Op
  _→₁₂_ = record {}

  ↻ : Op
  ↻ = record {}

  _⁻¹ : Op
  _⁻¹ = record {}

  _·_ : Op
  _·_ = record {}

  _⟔_ : Op
  _⟔_ = record {}

  _⟓_ : Op
  _⟓_ = record {}

  _∨_ : Op
  _∨_ = record {}

  _∧_ : Op
  _∧_ = record {}

  𝟘 : Op
  𝟘 = record {}

  inl : Op
  inl = record {}

  inr : Op
  inr = record {}

  [_,_] : Op
  [_,_] = record {}

  [_⊕_] : Op
  [_⊕_] = record {}

  𝟙 : Op
  𝟙 = record {}

  * : Op
  * = record {}

  fst : Op
  fst = record {}

  snd : Op
  snd = record {}

  ⟨_,_⟩ : Op
  ⟨_,_⟩ = record {}

  ⟨_⊗_⟩ : Op
  ⟨_⊗_⟩ = record {}
