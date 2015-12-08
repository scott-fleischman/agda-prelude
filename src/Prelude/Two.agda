{-# OPTIONS --without-K #-}

module Prelude.Two where

module 𝟚 where
  data 𝟚 ..{ℓ} : Set ℓ where
    ff tt : 𝟚
  {-# BUILTIN BOOL 𝟚 #-}
  {-# BUILTIN FALSE ff #-}
  {-# BUILTIN TRUE tt #-}

  𝟚₀ : Set
  𝟚₀ = 𝟚

open 𝟚 public
  using (𝟚)
  using (𝟚₀)
  using (ff)
  using (tt)
  hiding (module 𝟚)
