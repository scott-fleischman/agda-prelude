{-# OPTIONS --without-K #-}

module Prelude.Unsafe where

open import Prelude.Path
  using (_≡_)

module Unsafe where
  private
   primitive
     primTrustMe
       : ∀ {ℓ}
       → {A : Set ℓ}
       → {x y : A}
       → x ≡ y

  module ≡ where
    trustMe
      : ∀ {ℓ}
      → {A : Set ℓ}
      → {x y : A}
      → x ≡ y
    trustMe = primTrustMe

    erase
      : ∀ {ℓ}
      → {A : Set ℓ}
      → {x y : A}
      → x ≡ y
      → x ≡ y
    erase _ = trustMe
