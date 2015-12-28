{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Unit where

open import Agda.Primitive
open import Prelude.Display

module 𝟙↑ ..{ℓ} where
  record 𝟙 : Set ℓ where
    constructor *

  ! : ∀ ..{ℓ₀} {A : Set ℓ₀} → A → 𝟙
  ! _ = *

  instance
    trivial : 𝟙
    trivial = *

module 𝟙 where
  open 𝟙↑ {lzero} public

open 𝟙 public
  using (𝟙)
  using (*)
  hiding (module 𝟙)
open 𝟙↑ public
  using ()
  renaming (𝟙 to 𝟙↑)
  hiding (module 𝟙)

{-# DISPLAY 𝟙↑ = ᵈ.𝟙 #-}
{-# DISPLAY 𝟙 = ᵈ.𝟙 #-}
