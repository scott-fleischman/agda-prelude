{-# OPTIONS --without-K #-}

module Prelude.Display where

module ᵈ where
  private
    data #0 : Set where

    record #1 : Set where
      constructor #*

    module Op where
      Constant : Set
      Constant = #1

      Unary : Set
      Unary = #0 → #0

      Binary : Set
      Binary = #0 → #0 → #0

  infix 0 _→₁_
  infix 0 _→₂_
  infixr 1 _⟔_
  infixr 1 _⟓_
  infixl 2 _⁻¹
  infixr 4 _·_

  module ᵈ where
    _⊗_ : Op.Binary
    _⊗_ ()

    _⊕_ : Op.Binary
    _⊕_ ()

  ↻₀ : Op.Constant
  ↻₀ = _

  _→₁_ : Op.Binary
  _→₁_ ()

  _→₂_ : Op.Binary
  _→₂_ ()

  ↻ : Op.Constant
  ↻ = _

  _⁻¹ : Op.Unary
  _⁻¹ ()

  _·_ : Op.Binary
  _·_ ()

  _⟔_ : Op.Binary
  _⟔_ ()

  _⟓_ : Op.Binary
  _⟓_ ()

  _∨_ : Op.Binary
  _∨_ ()

  _∧_ : Op.Binary
  _∧_ ()

  fst : Op.Unary
  fst ()

  snd : Op.Unary
  snd ()

  ⟨_,_⟩ : Op.Binary
  ⟨_,_⟩ ()

  ⟨_⊗_⟩ : Op.Binary
  ⟨_⊗_⟩ ()

  inl : Op.Unary
  inl ()

  inr : Op.Unary
  inr ()

  [_,_] : Op.Binary
  [_,_] ()

  [_⊕_] : Op.Binary
  [_⊕_] ()
