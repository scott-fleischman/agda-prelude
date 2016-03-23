{-# OPTIONS --without-K #-}

module Prelude.Integer where

open import Agda.Primitive
open import Prelude.Natural

module Int where
  open import Agda.Builtin.Int public
    using (Int)
    using (pos)
    renaming (negsuc to negS)

  record ⊆ (A : Set) : Set where
    no-eta-equality
    field
      fromNeg : Nat → A
  open ⊆ ⦃ … ⦄ public
  {-# BUILTIN FROMNEG fromNeg #-}

  instance
    int⊆int : ⊆ Int
    int⊆int = record { fromNeg = λ
        { (ze) → pos 0
        ; (su n) → negS n
        }
      }

    nat⊆int : Nat.⊆ Int
    nat⊆int = record { fromNat = pos }

open Int public
  using (Int)
  using (pos)
  using (negS)
  hiding (module Int)
