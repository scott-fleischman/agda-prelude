{-# OPTIONS --without-K #-}

module Prelude.Size where

open import Agda.Primitive

module Size where
  open import Agda.Builtin.Size public
    using (Size)
    using (↑_)
    using (_⊔ˢ_)
    renaming (SizeU to U)
    renaming (Size<_ to <_)
    renaming (ω to ∞)

open Size public
  using (Size)
  using (_⊔ˢ_)
