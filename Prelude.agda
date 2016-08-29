module Prelude where

open import Data.Nat
open import Data.Unit
open import Data.Product

_^_ : Set → ℕ → Set
A ^ zero = ⊤
-- A ^ 1 = A
A ^ suc n = A × (A ^ n)

ℜⁿ : {A B : Set} → (A → B → Set) → (n : ℕ) → (A ^ n → B ^ n → Set)
ℜⁿ r zero = λ tt tt → ⊤
ℜⁿ r (suc n) = λ { (a , aⁿ) (b , bⁿ) → r a b × (ℜⁿ r n) aⁿ bⁿ }

𝔉ⁿ : {A B : Set} → (A → B) → (n : ℕ) → (A ^ n → B ^ n)
𝔉ⁿ f zero = λ tt → tt
𝔉ⁿ f (suc n) = λ { (a , aⁿ) → f a , 𝔉ⁿ f n aⁿ }
