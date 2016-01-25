module Prelude.Signature.Indexed where

open import Prelude.Families
open import Prelude.Functor
open import Prelude.Path
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Unit
open import Prelude.Monoidal.Void

record Sig (S O : Set₀) : Set₁ where
  constructor _◃_⊣_
  field
    op : O → Set₀
    ar : Σ O op → Set₀
    so : Σ (Σ O op) ar → S
open Sig public

module _ {S O} (⊢Σ : Sig S O) where
  ⟦_⟧◃ : (S → Set) → (O → Set)
  ⟦ ϕ ⟧◃ i =
    Σ[ op ⊢Σ i ∋ ϑ ]
    Π[ ar ⊢Σ (i ▸ ϑ) ∋ α ]
    ϕ (so ⊢Σ ((i ▸ ϑ) ▸ α))
