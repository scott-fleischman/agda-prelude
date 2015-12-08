{-# OPTIONS --without-K #-}

module Prelude.Point where

open import Agda.Primitive

record Pt ..(ℓ : _) : Set (lsuc ℓ) where
  coinductive
  constructor pt
  no-eta-equality
  field
    {type} : Set ℓ
    base : type
open Pt
