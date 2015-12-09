{-# OPTIONS --without-K #-}

module Prelude.String where

open import Agda.Primitive
open import Prelude.Bool

postulate
  String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → 𝟚
  primShowString : String → String
