```agda
{-# OPTIONS --without-K --exact-split --safe #-}
module Foundation where
```

## Universes

This code is addapted from https://ualib.gitlab.io/Universes.html

```agda 
open import Agda.Primitive public
  using (_⊔_; Level; lsuc)
  renaming (lzero to ℓ₀
          ; Set to Type
          -- ; Level to Universe
          -- ; Setω to 𝑙ω
          )
open import Data.Product
  using ( _,_ ; ∃ ; Σ-syntax ; _×_ )
  renaming ( proj₁ to fst ; proj₂ to snd )

variable
  𝑙 𝑢 𝑣 𝑙′ 𝑢′ 𝑣′ 𝑙₁ 𝑢₁ 𝑣₁ 𝑙₂ 𝑢₂ 𝑣₂ : Level

```


## Dependent types


```agda
infix 2 ∃-syntax

∃-syntax : ∀ {A : Type 𝑢} → (A → Type 𝑣) → Type (𝑢 ⊔ 𝑣)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ∈ A ] B

Π : {A : Type 𝑢} (B : A → Type 𝑣) → Type (𝑢 ⊔ 𝑣)
Π {A = A} B = (x : A) → B x

Π-syntax = Π
infixr -1 Π-syntax
syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
```

## Equality

```agda

module _ where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq public
    using (_≡_; refl; sym; trans; cong-app)
    renaming (cong to transport)

  open Eq.≡-Reasoning public

  _·_ : {A : Type 𝑙} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  p · q = trans p q

  𝑖𝑑 : {A : Type 𝑙} → A → A
  𝑖𝑑 x = x
```

## Function extensionality

Two function may produce same output when given the same input, but they may not syntactically equal. For example, *merge sort* and *quick sort* both take a list as argument and product a sorted version of the input as the result but they are different. It's okay to think of them as the same for all intents and purposes.

We said that those functions are *extensionally equal*, since they produce the same *extenal* output when given the same input, but they are not *intensionally equal* since their *internal* definitions differ.

`f` and `g` are said to be pointwise equal provided `∀x → f x ≡ gx`

```agda
_∼_ : {A : Type 𝑙} {B : A → Type 𝑢} → Π B → Π B → Type (𝑙 ⊔ 𝑢)
f ∼ g = ∀ x → f x ≡ g x
```

*Function extensionality* is the *principle* that pointwise equal functions are *definitionally equal*; that is, `∀ f g (f ∼ g → f ≡ g)`. However, it is important to keep in mind the following fact: *function extensionality is known to be neither provable nor disprovable in Martin-Löf type theory*. It is an independent statement.

```agda
dfunext : ∀ 𝑢 𝑣 → Type (lsuc (𝑢 ⊔ 𝑣))
dfunext 𝑢 𝑣 = {A : Type 𝑢}{B : A → Type 𝑣}{f g : ∀(x : A) → B x} → (f ∼ g) → f ≡ g

happly : {A : Type 𝑢}{B : A → Type 𝑣} (f g : Π B) → f ≡ g → f ∼ g
happly _ _ refl _ = refl


is-center : (A : Type 𝑢) → A → Type 𝑢
is-center A c = (x : A) → c ≡ x

is-singleton : Type 𝑢 → Type 𝑢
is-singleton A = ∃[ c ∈ A ] is-center A c

is-subsingleton : Type 𝑢 → Type 𝑢
is-subsingleton A = (x y : A) → x ≡ y

fiber : {A : Type 𝑢} {B : Type 𝑣} (f : A → B) → B → Type (𝑢 ⊔ 𝑣)
fiber {𝑢} {𝑣} {A} f y = ∃[ x ∈ A ] (f x ≡ y)

is-equiv : {A : Type 𝑢} {B : Type 𝑣} → (A → B) → Type (𝑢 ⊔ 𝑣)
is-equiv f = ∀ y → is-singleton (fiber f y)

hfunext : ∀ 𝑢 𝑣 → Type (lsuc (𝑢 ⊔ 𝑣))
hfunext 𝑢 𝑣 = {A : Type 𝑢}{B : A → Type 𝑣} (f g : Π B) → is-equiv (happly f g)
```

## Function inversion

```agda

```
