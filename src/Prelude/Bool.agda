{-# OPTIONS --without-K #-}

module Prelude.Bool where

open import Agda.Primitive
open import Prelude.Monoidal.Unit
open import Prelude.Monoidal.Void

module 𝟚 where
  open import Agda.Builtin.Bool public
    renaming (Bool to 𝟚)
    renaming (false to ff)
    renaming (true to tt)

  not : 𝟚 → 𝟚
  not ff = tt
  not tt = ff

  or : (p q : 𝟚) → 𝟚
  or tt q = tt
  or p tt = tt
  or ff ff = ff

  and : (p q : 𝟚) → 𝟚
  and ff q = ff
  and p ff = ff
  and tt tt = tt

  _∨_ : _
  _∨_ = or

  _∧_ : _
  _∧_ = and

  if_then_else_
    : ∀ ..{ℓ₀}
    → {A : Set ℓ₀}
    → (φ : 𝟚)
    → (lhs rhs : A)
    → A
  if ff then lhs else rhs = lhs
  if tt then lhs else rhs = rhs

  ⟦_⟧ : ∀ ..{ℓ₀} (φ : 𝟚) → Set ℓ₀
  ⟦ ff ⟧ = 𝟘↑
  ⟦ tt ⟧ = 𝟙↑

  {-# DISPLAY or p q = p ∨ q #-}
  {-# DISPLAY and p q = p ∧ q #-}

open 𝟚 public
  hiding (module 𝟚)
  using (𝟚)
  using (ff)
  using (tt)
  using (_∧_)
  using (_∨_)
  using (if_then_else_)
