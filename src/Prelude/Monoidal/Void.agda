{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Void where

open import Agda.Primitive

module 𝟘↑ ..{ℓ} where
  data 𝟘 : Set ℓ where

  ¬_ : ∀ ..{ℓ₀} → Set ℓ₀ → Set (ℓ₀ ⊔ ℓ)
  ¬ A = A → 𝟘

  ¡ : ∀ ..{ℓ₀} {A : Set ℓ₀} → 𝟘 → A
  ¡ ()

module 𝟘 where
  open 𝟘↑ {lzero} public

open 𝟘 public
  using (𝟘)
  hiding (module 𝟘)
open 𝟘↑ public
  using ()
  renaming (𝟘 to 𝟘↑)
  hiding (module 𝟘)
