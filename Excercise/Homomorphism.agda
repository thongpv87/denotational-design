module Homomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning



record Homo₁
    {M N : Set}
    (opₘ : M →  Set)
    (opₙ : N →  Set)
    (f : M →  N)
  : Set₁ where
  field
    homo₁ : ∀ (m : M) →  opₘ m →  opₙ (f m)

-- open Homo₀ ⦃ ... ⦄ public

-- record Homo
--     {M N : Set}
--     (_∙ₘ_ : M → M → Set)
--     (_∙ₙ_ : N → N → Set)
--     (f : M → N)
--   : Set₁ where
--   field
--     homo : ∀ (a b : M) → (a ∙ₘ b) → (f a ∙ₙ f b)

-- open Homo ⦃ ... ⦄ public

record Monoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
  field
    ∙-identityʳ : ∀ (a : A) → a ∙ e ≡ a
    ∙-identityˡ : ∀ (a : A) → e ∙ a ≡ a
    ∙-assoc : ∀ (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
open Monoid ⦃ ... ⦄ public

-- record MonoidH
--   {M N : Set}
