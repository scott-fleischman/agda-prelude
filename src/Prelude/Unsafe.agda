{-# OPTIONS --without-K #-}

module Prelude.Unsafe where

open import Prelude.Path

module Unsafe where
  private
   primitive
     primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

  trustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
  trustMe = primTrustMe

  erase : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
  erase _ = trustMe
