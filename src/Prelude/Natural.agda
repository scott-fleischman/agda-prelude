{-# OPTIONS --without-K #-}

module Prelude.Natural where

open import Agda.Primitive
open import Prelude.Decidable
open import Prelude.Monoidal
  hiding (*)
open import Prelude.Path
  hiding (refl)
open import Prelude.Size

module Nat where
  infix 0 _≟_
  infix 0 _≤?_

  data Nat : Set where
    ze : Nat
    su_ : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

  record ⊆ (A : Set) : Set where
    no-eta-equality
    field
      fromNat : Nat → A
  open ⊆ ⦃ … ⦄ public
  {-# BUILTIN FROMNAT fromNat #-}

  instance
    nat⊆nat : ⊆ Nat
    nat⊆nat = record { fromNat = λ x → x }

  pred : Nat → Nat
  pred ze = ze
  pred (su n) = n

  module ≤ where
    infix 0 _≤_

    data _≤_ (m : Nat) : Nat → Set where
      stop : m ≤ m
      step : ∀ {n} (φ : m ≤ n) → m ≤ su n

    idn : ∀ {n} → n ≤ n
    idn = stop

    cmp : ∀ {m n o} → n ≤ o → m ≤ n → m ≤ o
    cmp (stop) p = p
    cmp (step q) p = step (cmp q p)

    seq : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
    seq p q = cmp q p

    z≤n : ∀ {n} → 0 ≤ n
    z≤n {ze} = stop
    z≤n {su n} = step z≤n

    s≤s : ∀ {m n} → m ≤ n → su m ≤ su n
    s≤s stop = stop
    s≤s (step φ) = step (s≤s φ)

    p≤p : ∀ {m n} → su m ≤ su n → m ≤ n
    p≤p stop = stop
    p≤p (step stop) = step stop
    p≤p (step (step φ)) = step (p≤p (step φ))
  open ≤ public
    hiding (module _≤_)
    using (_≤_)
    using (stop)
    using (step)
  open ≤

  _+_ : (m n : Nat) → Nat
  ze + n = n
  (su m) + n = su (m + n)
  {-# BUILTIN NATPLUS _+_ #-}

  _*_ : (m n : Nat) → Nat
  ze * n = ze
  (su m) * n = n + (m * n)
  {-# BUILTIN NATTIMES _*_ #-}

  _≟_ : (m n : Nat) → Decidable (m ≡ n)
  ze ≟ ze = ⊕.inr ≡.idn
  ze ≟ su n = ⊕.inl λ()
  su m ≟ ze = ⊕.inl λ()
  su m ≟ su n with m ≟ n
  su m ≟ su n | ⊕.inl k =
    ⊕.inl (k ⇒.⟔ λ φ → ≡.coe* (λ x → m ≡ pred x) φ ≡.idn)
  su m ≟ su n | ⊕.inr φ =
    ⊕.inr (≡.ap¹ su_ φ)

  _≤?_ : (m n : Nat) → Decidable (m ≤ n)
  ze ≤? n = ⊕.inr z≤n
  su m ≤? ze = ⊕.inl λ()
  su m ≤? su n with m ≤? n
  su m ≤? su n | ⊕.inl k =
    ⊕.inl (k ⇒.⟔ p≤p)
  su m ≤? su n | ⊕.inr φ =
    ⊕.inr (s≤s φ)

open Nat public
  using (Nat)
  using (ze)
  using (su_)
  hiding (module Nat)
