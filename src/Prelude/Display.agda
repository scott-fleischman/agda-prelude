{-# OPTIONS --without-K #-}

module Prelude.Display where

module ᵈ where
  private
    record Op : Set where

  infix 0 _→₁_
  infix 0 _→₂_
  infixr 1 _⟔_
  infixr 1 _⟓_
  infixl 2 _⁻¹
  infixr 4 _·_

  module ᵈ where
    _⊗_ : Op
    _⊗_ = _

    _⊕_ : Op
    _⊕_ = _

  ↻₀ : Op
  ↻₀ = _

  _→₁_ : Op
  _→₁_ = _

  _→₂_ : Op
  _→₂_ = _

  ↻ : Op
  ↻ = _

  _⁻¹ : Op
  _⁻¹ = _

  _·_ : Op
  _·_ = _

  _⟔_ : Op
  _⟔_ = _

  _⟓_ : Op
  _⟓_ = _

  _∨_ : Op
  _∨_ = _

  _∧_ : Op
  _∧_ = _

  fst : Op
  fst = _

  snd : Op
  snd = _

  ⟨_,_⟩ : Op
  ⟨_,_⟩ = _

  ⟨_⊗_⟩ : Op
  ⟨_⊗_⟩ = _

  inl : Op
  inl = _

  inr : Op
  inr = _

  [_,_] : Op
  [_,_] = _

  [_⊕_] : Op
  [_⊕_] = _
