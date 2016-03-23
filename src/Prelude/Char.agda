{-# OPTIONS --without-K #-}

module Prelude.Char where

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Monoidal.Coproduct
open import Prelude.Natural
open import Prelude.Path
open import Prelude.String
open import Prelude.Unsafe

module Char where
  open import Agda.Builtin.Char public
    using (Char)
    renaming (primCharEquality to ⟦_≟_⟧)
    renaming (primCharToNat to toNat)

  open import Agda.Builtin.String public
    renaming (primShowChar to show)
    using ()

  _≟_ : (c₀ c₁ : Char) → Decidable (c₀ ≡ c₁)
  c₀ ≟ c₁ with ⟦ c₀ ≟ c₁ ⟧
  … | tt = ⊕.inr Unsafe.≡.trustMe
  … | ff = ⊕.inl void where postulate void : _

open Char public
  using (Char)
