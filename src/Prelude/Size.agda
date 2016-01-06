{-# OPTIONS --without-K #-}

module Prelude.Size where

open import Agda.Primitive

module Size where
  {-# BUILTIN SIZEUNIV U #-}
  {-# BUILTIN SIZE Size #-}
  {-# BUILTIN SIZELT <_ #-}
  {-# BUILTIN SIZESUC ↑_ #-}
  {-# BUILTIN SIZEINF ∞ #-}

open Size public
  using (Size)
