{-# OPTIONS --type-in-type #-}

module Structure where

open import Data.Nat
open import Prelude

record Struct (A : Set) : Set where
  field
    ℜ : {n : ℕ} → A ^ n → Set
    𝔉 : {n : ℕ} → A ^ n → A
