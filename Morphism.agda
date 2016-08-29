module Morphism where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Structure

module _ {A B : Set} (σᴬ : Struct A) (σᴮ : Struct B) where
  open Struct σᴬ renaming (ℜ to ℜᴬ ; 𝔉 to 𝔉ᴬ)
  open Struct σᴮ renaming (ℜ to ℜᴮ ; 𝔉 to 𝔉ᴮ)

  record Hom : Set where
    field
      f : A → B
      ℜ-f : {n : ℕ} → (aⁿ : A ^ n) → ℜᴬ aⁿ → ℜᴮ (𝔉ⁿ f n aⁿ)
      𝔉-f : {n : ℕ} → (aⁿ : A ^ n) → f (𝔉ᴬ aⁿ) ≡ 𝔉ᴮ (𝔉ⁿ f n aⁿ)

  record Embed : Set where
    field
      h : Hom
    open Hom h
    field
      f-inj : ∀ {x y} → f x ≡ f y → x ≡ y
      ℜ-f' : {n : ℕ} → (aⁿ : A ^ n) → ℜᴮ (𝔉ⁿ f n aⁿ) → ℜᴬ aⁿ

  record Iso : Set where
    field
      e : Embed
    open Embed e
    open Hom h
    field
      g : B → A
      g-inj : ∀ {x y} → g x ≡ g y → x ≡ y
      f-g : ∀ {x} → f (g x) ≡ x
      g-f : ∀ {x} → g (f x) ≡ x

module _ {A : Set} (σᴬ : Struct A) where
  Endo : Set
  Endo = Hom σᴬ σᴬ

  Auto : Set
  Auto = Iso σᴬ σᴬ

module Examples {A B : Set} (σᴬ : Struct A) (σᴮ : Struct B) (h : Hom σᴬ σᴮ) where
  open Struct σᴬ renaming (ℜ to ℜᴬ ; 𝔉 to 𝔉ᴬ)
  open Struct σᴮ renaming (ℜ to ℜᴮ ; 𝔉 to 𝔉ᴮ)
  open Hom h

  hrel : A → A → Set
  hrel x y = f x ≡ f y

  open import Relation.Binary

  hrel-equiv : IsEquivalence hrel
  hrel-equiv = record { refl = refl ; sym = sym ; trans = trans }

  module _ {x y : A} where
    hrel-cong : hrel x y → hrel (𝔉ᴬ (x , tt)) (𝔉ᴬ (y , tt))
    hrel-cong p = trans (𝔉-f (x , tt)) (sym (trans (𝔉-f (y , tt)) (sym (cong (λ b → 𝔉ᴮ (b , tt)) p))))
