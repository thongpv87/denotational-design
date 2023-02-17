## Import

```agda
module Homomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
-- open import Function.Base using (_∘_)
```

## Definition of epimorphism



```agda
```

## Old code

```agda
record RawMonoid {A : Set} (⊘ : A) (_∙_ : A → A → A) : Set where

open RawMonoid ⦃ ... ⦄

record Monoid {A : Set} (⊘ : A) (_∙_ : A → A → A) : Set where
  field
    ⦃ raw ⦄ : RawMonoid ⊘ _∙_

    ∙-identityʳ : ∀ (a : A) → a ∙ ⊘ ≡ a
    ∙-identityˡ : ∀ (a : A) → ⊘ ∙ a ≡ a
    ∙-assoc : ∀ (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
open Monoid ⦃ ... ⦄ public

record MonoidH
  {M : Set}
  (⊘ₘ : M)
  (_∙ₘ_ : M → M → M)
  ⦃ _ : RawMonoid ⊘ₘ _∙ₘ_ ⦄
  {N : Set}
  (⊘ₙ : N)
  (_∙ₙ_ : N → N → N)
  ⦃ _ : RawMonoid ⊘ₙ _∙ₙ_ ⦄
  (f : M → N)
  : Set where
  field
    P-⊘ : f ⊘ₘ ≡ ⊘ₙ
    P-∙ : ∀ {a b} → f (a ∙ₘ b) ≡ f a ∙ₙ f b

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
infixr 9 _∘_

-- data Injective {M N : Set} (f : M → N) : Set where
--   inj : ∀ {g h} → (f ∘ g) ≡ (f ∘ h) → g ≡ h

-- Injective : ∀ {A B : Set} → (A → B) → Set _


-- Surjective : ∀ {A B : Set} → (A → B) → Set
-- Surjective f = ∀ {g h} → (g ∘ f) ≡ (h ∘ f) → g ≡ h

postulate
  injective : {A B : Set} {g h} (f : A → B) → (f ∘ g) ≡ (f ∘ h) → g ≡ h



-- record Monoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
--   field
--     ∙-identityʳ : ∀ (a : A) → a ∙ e ≡ a
--     ∙-identityˡ : ∀ (a : A) → e ∙ a ≡ a
--     ∙-assoc : ∀ (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
-- open Monoid ⦃ ... ⦄ public

-- record CommMonoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
--   field
--     ∙-comm : ∀ (a b : A) → (a ∙ b) ≡ (b ∙ a)
--     ⦃ monoid ⦄ : Monoid e _∙_
-- open Monoid ⦃ ... ⦄ public

-- -- record Homomorphism


-- -- nullary operations homomorphism
-- record Homo₀
--     {M N : Set}
--     (eₘ : M)
--     (eₙ : N)
--     (f : M → N)
--   : Set where
--   field
--     homo₀ : eₘ → eₙ


-- -- unary operations homomorphism
-- record Homo₁
--     {M N : Set}
--     (opₘ : M → M)
--     (opₙ : N → N)
--     (f : M → N)
--   : Set₁ where
--   field
--     homo₁ : ∀ (m : M) → opₘ m → opₙ (f m)

-- -- open Homo₀ ⦃ ... ⦄ public

-- -- binary operation homomorphsim
-- record Homo₂
--     {M N : Set}
--     (_∙ₘ_ : M → M → Set)
--     (_∙ₙ_ : N → N → Set)
--     (f : M → N)
--   : Set where
--   field
--     homo : ∀ (a b : M) → (a ∙ₘ b) → (f a ∙ₙ f b)

-- open Homo ⦃ ... ⦄ public

-- record MonoidH
--   {M N : Set}
```

f (a + b) = f a * f b
f 0 = 1
