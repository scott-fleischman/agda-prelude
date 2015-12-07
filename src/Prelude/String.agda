{-# OPTIONS --without-K #-}

module Prelude.String where

open import Prelude.Two

postulate
  String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → 𝟚
  primShowString : String → String
