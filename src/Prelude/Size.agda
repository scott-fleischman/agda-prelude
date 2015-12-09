{-# OPTIONS --without-K #-}

module Prelude.Size where

open import Agda.Primitive

module Size where
  {-# BUILTIN SIZEUNIV U #-}
  {-# BUILTIN SIZE t #-}
  {-# BUILTIN SIZELT <_ #-}
  {-# BUILTIN SIZESUC ↑_ #-}
  {-# BUILTIN SIZEINF ∞ #-}
