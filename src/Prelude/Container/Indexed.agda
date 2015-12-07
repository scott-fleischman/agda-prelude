module Prelude.Container.Indexed where

open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Path
  renaming
  (t to _≡_)
open import Prelude.Functor
open import Prelude.Families
open import Prelude.One
open import Prelude.Product.Indexed
open import Prelude.Zero

record Con (S O : Set₀) : Set₁ where
  constructor _◃_⊣_
  field
    op : O → Set₀
    ar : Σ O op → Set₀
    so : Σ (Σ O op) ar → S
open Con public

module _ {S O} (Σ : Con S O) where
  ⟦_⟧◃ : (S → Set) → (O → Set)
  ⟦ ϕ ⟧◃ i =
    Σ.[ op Σ i ∋ ϑ ]
    Π.[ ar Σ (i Σ., ϑ) ∋ α ]
    ϕ (so Σ ((i Σ., ϑ) Σ., α))
