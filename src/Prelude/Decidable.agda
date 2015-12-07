{-# OPTIONS --without-K #-}

module Prelude.Decidable where

open import Agda.Primitive
open import Prelude.Coproduct.Indexed as ∐
  using ()
open import Prelude.Zero

-- t : ∀ ..{ℓ} (A : Set ℓ) → Set ℓ
-- t A = (𝟘.¬⁰ A) ∐.⊕ A
