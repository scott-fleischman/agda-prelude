{-# OPTIONS --without-K #-}

module Prelude.Size where

open import Agda.Primitive

module Size where
  open import Agda.Builtin.Size public
    renaming (SizeU to U)
    using (Size)
    renaming (Size<_ to <_)
    using (↑_)
    renaming (ω to ∞)

open Size public
  using (Size)
