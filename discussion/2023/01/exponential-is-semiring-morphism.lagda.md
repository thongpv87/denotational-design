> look for a pretty sense in which exponentiation is
> a semiring homomorphism. I have a homomorphism in mind, and I've not
> seen it discussed anywhere. (Lots of math gets rediscovered, though.)

Semiring `R` is set `R` together with two binary operation `(+)` and
`(*)` such that - `(R, +, 0)` is commutative monoid - `(R, *, 1)` is
monoid - `(+)` and `(*)` left and right distributive - left
distributive: `a * (b + c) = a * b + a * c` - right distributive:
`(a + b) * c = a * c + b * c` - Multiplication by `0` *annihilates*
`R`: - `0 * a = 0 = a * 0`

Let see what properties do of exponentiation do we have: - x \^ (a + b)
= x \^ a \* x \^ b - x \^ (a \* b) = (x \^ a) \^ b - x \^ (a - b) = x \^
a / x \^ b

## Todo: check scale vs addition

## Semiring of + and -

-   x + y = x + y
-   x \* y = x () y `<!-- x ^ (logₐ b) -->`{=html}
-   commutative monoid: (ℕ, + , 0)
-   (ℕ, /, 1) is monoid (x / y / z) = x
-   distributive:
    -   left: x + min (y, z) = min (x + y, x + z)
    -   right: min (x , y) + z = min (x + z, y + z)
-   multiplication by ∞ *annihilates* ℕ: a + ∞ = ∞ = ∞ + a

Now, let see what properties that (x \^*) need to satisfied to be a
tropical semiring homomorphism: - f (a + b) = f a + f b - x \^ (min (a,
b)) = min (x \^ a, x \^ b) - That's only true for (x \^*) if x ≥ 0 - f
(a \* b) = f a \* f b - x \^ (a + b) = x \^ a + x \^ b -\> this is
wrong - f 0 = 0 - f 1 = 1

## Tropical min semiring

### (ℕ+, min, +) from a semiring

-   x + y = min (x, y)
-   x \* y = x + y
-   commutative monoid: (ℕ, min , ∞)
    -   assoc: min (min (x , y), z) = min (x, min (y, z))
    -   id: min (a, ∞) = a = min (∞, a)
    -   comm: min(x, y) = min(y, x)
-   (ℕ, +, 0) is monoid, we've already known that it's also a
    commutative monoid
-   distributive:
    -   left: x + min (y, z) = min (x + y, x + z)
    -   right: min (x , y) + z = min (x + z, y + z)
-   multiplication by ∞ *annihilates* ℕ: a + ∞ = ∞ = ∞ + a

### (ℕ+, min, \*) form a semiring

-   x + y = min (x, y)
-   x \* y = x + y
-   commutative monoid: (ℕ, min , ∞) : above
-   (ℕ, \*, 1) is monoid, we know that it's also a commutative monoid
-   distributive:
    -   left: x \* min (y, z) = min (x \* y, x \* z)
    -   right: min (x , y) \* z = min (x \* z, y \* z)
-   multiplication by ∞ *annihilates* ℕ: a \* ∞ = ∞ = ∞ \* a

Now, let see what properties that (x \^*) need to satisfied to be a
tropical semiring homomorphism: - f (a + b) = f a + f b - x \^ (min (a,
b)) = min (x \^ a, x \^ b) - That's only true for (x \^*) if x ≥ 0 - f
(a \* b) = f a \* f b - x \^ (a + b) = x \^ a \* x \^ b - f 0 = 0 - x \^
∞ = ∞ (x \> 1) - f 1 = 1 - x \^ 0 = 1

## Tropical max semiring

### (ℕ, max, +) from a semiring

-   x + y = max (x, y)
-   x \* y = x + y
-   commutative monoid: (ℕ, max , -∞)
    -   assoc: max (max (x , y), z) = max (x, max (y, z))
    -   id: max (a, -∞) = a = max (-∞, a)
    -   comm: max(x, y) = max(y, x)
-   (ℕ, +, 0) is monoid, we've already known that it's also a
    commutative monoid
-   distributive:
    -   left: x + max (y, z) = max (x + y, x + z)
    -   right: max (x , y) + z = max (x + z, y + z)
-   multiplication by ∞ *annihilates* ℕ: a + -∞ = -∞ = -∞ + a

### (ℕ, max, \*) form a semiring

-   x + y = max (x, y)
-   x \* y = x \* y
-   commutative monoid: (ℕ, max , ∞) : above
-   (ℕ, \*, 1) is monoid, we know that it's also a commutative monoid
-   distributive:
    -   left: x \* max (y, z) = max (x \* y, x \* z) (x \>= 0)
    -   right: max (x , y) \* z = max (x \* z, y \* z)
-   multiplication by ∞ *annihilates* ℕ: a \* -∞ = -∞ = -∞ \* a

Now, let see what properties that (x \^*) need to satisfied to be a
tropical semiring homomorphism: - f (a + b) = f a + f b - x \^ (max (a,
b)) = max (x \^ a, x \^ b) (x \> 0) - That's only true for (x \^*) if x
≥ 0 - f (a \* b) = f a \* f b - x \^ (a + b) = x \^ a \* x \^ b - f 0 =
0 - x \^ ∞ = ∞ (x \> 1) - f 1 = 1 - x \^ 0 = 1

x \^ (a + b) = x \^ a × x \^ b x \^ (a × b) = (x \^ a) \^ b x \^ 0 = 1 x
\^ 1 = x

+: union, \[\] \*: join , universe left: a and (b or c) = (a and b) or
(a and c) right: (a or b) and c = (a and c) or (b and c) a and \[\] =
\[\]

x \^ \[\] = \[\] x \^ universe = universe

## R, or, and is semiring

R = a → bool + : or p₁ p₂ = a → (p₁ a) ∨ (p₂ a) id+ = λ \_ → false *:
and p₁ p₂ = a → (p₁ a) ∧ (p₂ a) id* = λ \_ → true

a and (b or c) = (a and b) or (a and c) (a or b) and c = (a or c) and (b
or c)

a and id+ = id+ \## x\^ x \^ (a or b) = x \^ a or x \^ b x \^ (a and b)
= x \^ a and x \^ b x \^ ⊘ = ⊘ x \^

+, ⊘ = A ∨ B \*, U = A ∧ B A ∧ ⊘ = ⊘ = ⊘ ∧ A

x\^(a + b) : A ⊂ (B ∨ C) ≡ A ⊂ B ∨ A ⊂ C x\^(a \* b) : A ⊂ (B ∧ C) ≡ A ⊂
B ∧ A ⊂ C x\^0 : A ⊂ ⊘ = ⊘ x\^1 = 1: A ⊂ U = A

> Bonus: look for a pretty sense in which exponentiation is
> a semiring homomorphism. I have a homomorphism in mind, and I've not
> seen it discussed anywhere. (Lots of math gets rediscovered, though.)

I think we can have following algebra that form a semiring and (x \^\_)
form a semiring homomorphism. - proof 1: (∨ , ⊘ , ∧ , U) form a
semiring - (∨ , ⊘) is commutative monoid - (A ∨ B) ∨ C ≡ A ∨ (B ∨ C) - A
∨ ⊘ ≡ ⊘ ≡ ⊘ ∨ A - A ∨ B ≡ B ∨ A - (∧ , U) is a (commutative) monoid - (A
∧ B) ∧ C ≡ A ∧ (B ∧ C) - A ∧ U ≡ A ≡ U ∧ A - A ∧ B ≡ B ∧ A - (∧ , ∨) is
left and right distributive - A ∧ (B ∨ C) ≡ (A ∧ B) ∨ (A ∧ C) - (A ∨ B)
∧ C ≡ (A ∧ C) ∨ (B ∧ C) - A ∧ ⊘ ≡ ⊘ ≡ ⊘ ∧ A - proof 2: `(X ^_) ≈ (_→ X)`
preserve following properties - X ⊂ (A ∨ B) ⇐ (X ⊂ A) ∨ (X ⊂ B) - X ⊂ (A
∧ B) ≡ (X \^ A) ∧ (X \^ B) - X ⊂ ⊘ ≡ ⊘ - X ⊂ U ≡ X

(\_→ X)

``` agda
open import Data.Bool
open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.PropositionalEquality.Extensionality

data set (A : Set) : Set where
  contains : (A → Bool) → set A

union : ∀ {A : Set} → set A → set A → set A
union (contains p₁) (contains p₂) = contains λ a → p₁ a ∨ p₂ a

join : ∀ {A : Set} → set A → set A → set A
join (contains p₁) (contains p₂) = contains λ a → p₁ a ∧ p₂ a

empty : ∀ {A : Set} → set A
empty = contains λ _ → false

universe : ∀ {A : Set} → set A
universe = contains λ _ → true


set≤10 : set ℕ
set≤10 = contains (_≤ᵇ 10)

set≥5  : set ℕ
set≥5 = contains (5 ≤ᵇ_)

set5≤x≤10 : set ℕ
set5≤x≤10 = join set≤10 set≥5

lookup : ∀ {A : Set} → set A → A → Bool
lookup (contains f) x = f x
```

## prove (union, empty, join, universe) is semiring

``` agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

-- union, empty is communicative monoid
union-assoc : ∀ {A : Set} → (a b c : set A) → union (union a b) c ≡ union a (union b c)
union-assoc (contains p₁) (contains p₂) (contains p₃) =
  begin
    contains (λ a → (p₁ a ∨ p₂ a) ∨ p₃ a)
    ≡⟨ λ { a → ∨-assoc (p₁ a) (p₂ a) (p₃ a) } ⟩

```
