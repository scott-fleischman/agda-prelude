{-# OPTIONS --without-K #-}

module Prelude.Two where

module 𝟚 where
  data 𝟚 ..{ℓ} : Set ℓ where
    ff : 𝟚
    tt : 𝟚
  {-# BUILTIN BOOL 𝟚 #-}
  {-# BUILTIN FALSE ff #-}
  {-# BUILTIN TRUE tt #-}

open 𝟚 public
  using (𝟚)
  using (ff)
  using (tt)
  hiding (module 𝟚)
