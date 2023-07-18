Dear Conal,

It's been quite some time since we last connected, and I apologize for the delayed response. I've been quite busy recently

Regarding the exercises you sent, I don't have any questions about them, but I am interested in discussing how to apply denotational design on a real-world problem. I'll create a separate email thread for that.

In the meantime, I wanted to share with you my solutions to the exercises:

```agda
module NegativeLogic where
open import Data.Bool
open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Function.Base

private variable x y : Bool

⟦_⟧ : Bool -> Bool
⟦_⟧ = not

false′ : Bool
false′ = true

true′ : Bool
true′ = false
```
*Exercise 1.1.* Define ⟦false! ⟧ and ⟦true! ⟧, thus proving correctness of false! and true! .

```agda
⟦false′⟧ : ⟦ false′ ⟧ ≡ false
⟦false′⟧ = refl

⟦true′⟧ : ⟦ true′ ⟧ ≡ true
⟦true′⟧ = refl
```

*Exercise 1.2.* Define not’ (implementation) and ⟦not! ⟧ (correctness proof).
```agda
not′ : Bool →  Bool
not′ true = false
not′ false = true

⟦not′⟧ : ∀ x →  ⟦ not′ x ⟧ ≡ not ⟦ x ⟧
⟦not′⟧ false = refl
⟦not′⟧ true = refl
```

*Exercise 1.3.* Define _∧! _ and ⟦_∧ !_⟧.

```agda
infixr 6 _∧′_ _⟦∧′⟧_
_∧′_ : Bool → Bool → Bool
false ∧′ false = false
_ ∧′ _ = true

_⟦∧′⟧_ : ∀ x y → ⟦ x ∧′ y ⟧ ≡ ⟦ x ⟧ ∧ ⟦ y ⟧
true ⟦∧′⟧ true = refl
false ⟦∧′⟧ false = refl
false ⟦∧′⟧ true = refl
true ⟦∧′⟧ false = refl
```
*Exercise 1.4.* Likewise for disjunction.

```agda
infixr 6 _∨′_ _⟦∨′⟧_
_∨′_ : Bool → Bool → Bool
true ∨′ true = true
_ ∨′ _ = false

_⟦∨′⟧_ : ∀ x y → ⟦ x ∨′ y ⟧ ≡ ⟦ x ⟧ ∨ ⟦ y ⟧
true ⟦∨′⟧ true = refl
false ⟦∨′⟧ false = refl
false ⟦∨′⟧ true = refl
true ⟦∨′⟧ false = refl
```

*Exercise 1.5.* Likewise for exclusive-or.

```agda
infixr 6 _xor′_ _⟦xor′⟧_
_xor′_ : Bool → Bool → Bool
true xor′ true = true
false xor′ false = true
_ xor′ _ = false

_⟦xor′⟧_ : ∀ x y → ⟦ x xor′ y ⟧ ≡ ⟦ x ⟧ xor ⟦ y ⟧
true ⟦xor′⟧ true = refl
false ⟦xor′⟧ false = refl
false ⟦xor′⟧ true = refl
true ⟦xor′⟧ false = refl
```

*Exercise 1.6.* Prove that not! is its own inverse
```agda
not′-involutive : ∀ x →  ⟦ not′ (not′ x) ⟧ ≡ ⟦ x ⟧
not′-involutive x =
  begin
    (⟦ not′ (not′ x) ⟧)
    ≡⟨ ⟦not′⟧ (not′ x) ⟩
    not ⟦ not′ x ⟧
    ≡⟨ cong not (⟦not′⟧ x) ⟩
    not (not ⟦ x ⟧)
    ≡⟨ not-involutive ⟦ x ⟧ ⟩
    ⟦ x ⟧
  ∎
```

*Exercise 1.7.* Prove that _∧! _ is associative, commutative, and idempotent, as well
as other laws of a boolean algebra

```agda
∧′-assoc : ∀ x y z →  ⟦ (x ∧′ y) ∧′ z ⟧ ≡ ⟦ x ∧′ (y ∧′ z) ⟧
∧′-assoc x y z =
  begin
    ⟦ (x ∧′ y) ∧′ z ⟧
  ≡⟨ (x ∧′ y) ⟦∧′⟧ z ⟩
    ⟦ x ∧′ y ⟧ ∧ ⟦ z ⟧
  ≡⟨ cong (_∧ ⟦ z ⟧) (x ⟦∧′⟧ y) ⟩
    (⟦ x ⟧ ∧ ⟦ y ⟧) ∧ ⟦ z ⟧
  ≡⟨ ∧-assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
    ⟦ x ⟧ ∧ (⟦ y ⟧ ∧ ⟦ z ⟧)
  ≡⟨ cong (⟦ x ⟧ ∧_) (sym (y ⟦∧′⟧ z)) ⟩
    ⟦ x ⟧ ∧ ⟦ y ∧′ z ⟧
  ≡⟨ sym (x ⟦∧′⟧ (y ∧′ z)) ⟩
    ⟦ x ∧′ (y ∧′ z) ⟧
  ∎

∧′-comm : ∀ x y →  ⟦ x ∧′ y ⟧ ≡ ⟦ y ∧′ x ⟧
∧′-comm x y =
  begin
    ⟦ x ∧′ y ⟧
  ≡⟨ x ⟦∧′⟧ y ⟩
    ⟦ x ⟧ ∧ ⟦ y ⟧
  ≡⟨ ∧-comm ⟦ x ⟧ ⟦ y ⟧ ⟩
    ⟦ y ⟧ ∧ ⟦ x ⟧
  ≡⟨ sym (y ⟦∧′⟧ x) ⟩
    ⟦ y ∧′ x ⟧
  ∎

∧′-idem : ∀ x →  ⟦ x ∧′ x ⟧ ≡ ⟦ x ⟧
∧′-idem x =
  begin
    ⟦ x ∧′ x ⟧
  ≡⟨ x ⟦∧′⟧ x ⟩
    ⟦ x ⟧ ∧ ⟦ x ⟧
  ≡⟨ ∧-idem ⟦ x ⟧ ⟩
    ⟦ x ⟧
  ∎
```

```agda
⟦⟧-injective : ∀ x y →  ⟦ x ⟧ ≡ ⟦ y ⟧ →  x ≡ y
⟦⟧-injective x y p =
  begin
    x
  ≡⟨ sym (not-involutive x) ⟩
    not (not x)
  ≡⟨ cong not p ⟩
    not (not y)
  ≡⟨ not-involutive y ⟩
    y
  ∎
```


Best Regards, 

Thong
