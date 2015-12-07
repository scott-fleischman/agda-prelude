{-# OPTIONS --without-K #-}

module Prelude.Fin where

open import Prelude.Coproduct
open import Prelude.Nat

module Fin where
  data Fin : (n : Nat) → Set where
    ze
      : ∀ {n}
      → Fin (su n)
    su_
      : ∀ {n}
      → (i : Fin n)
      → Fin (su n)

open Fin public
  using (Fin)
  using (ze)
  using (su_)
  hiding (module Fin)

-- #inl : ∀ {m n} (i : Fin m) → Fin (m Nat.+ n)
-- #inl ze = ze
-- #inl (su i) = su (#inl i)

-- #inr : ∀ {m n} (i : Fin n) → Fin (m Nat.+ n)
-- #inr {ze} i = i
-- #inr {su m} i = su (#inr {m} i)

-- data #⊕ {m n} : Fin (m Nat.+ n) → Set where
--   #⊕₀ : (i₀ : Fin m) → #⊕ (#inl i₀)
--   #⊕₁ : (i₁ : Fin n) → #⊕ (#inr {m} i₁)

-- #⊕-split : ∀ {m n} → (i : Fin (m Nat.+ n)) → #⊕ {m} i
-- #⊕-split {ze} i = #⊕₁ i
-- #⊕-split {su m} ze = #⊕₀ ze
-- #⊕-split {su m} (su i) with #⊕-split {m} i
-- #⊕-split {su m} (su .(#inl     i₀)) | #⊕₀ i₀ = #⊕₀ (su i₀)
-- #⊕-split {su m} (su .(#inr {m} i₁)) | #⊕₁ i₁ = #⊕₁ i₁

-- #⊕-map : ∀ {m n} → (i : Fin (m Nat.+ n)) → Fin m ⊕ Fin n
-- #⊕-map {m} i with #⊕-split {m} i
-- #⊕-map     .(#inl     i₀) | #⊕₀ i₀ = ⊕.inl i₀
-- #⊕-map {m} .(#inr {m} i₁) | #⊕₁ i₁ = ⊕.inr i₁
