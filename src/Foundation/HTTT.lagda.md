# Introduction

## Different between univalent mathematics and traditional, set-based mathematics.

1. The kinds of objects we take as basic.
  -  Certain things called types, or higher groupoids, rather than sets, are the primitive objects.
  -  Sets, also called 0-groupoids, are particular kinds of types.
  -  So we have more general objects as a starting point.
  -  E.g. the type ℕ of natural numbers is a set, and this is a theorem, not a definition.
  -  E.g. the type of monoids is not a set, but instead a 1-groupoid, automatically.
  -  E.g. the type of categories is a 2-groupoid, again automatically.

2. The treatment of logic.
  - Mathematical statements are interpreted as types rather than truth values.
  - Truth values are particular kinds of types, called -1-groupoids, with at most one element.
  - Logical operations are particular cases of mathematical operations on types.
  - The mathematics comes first, with logic as a derived concept.
  - E.g. when we say “and”, we are taking the cartesian product of two types, which may or may not be truth values.

3. The treatment of equality.
  - The value of an equality `x ＝ y` is a type, called the identity type, which is not necessarily a truth value.
  - It collects the ways in which the mathematical objects x and y are identified.
  - E.g. it is a truth value for elements of ℕ, as there is at most one way for two natural numbers to be equal.
  - E.g. for the type of monoids, it is a set, amounting to the type of monoid isomorphisms, automatically.
  - E.g. for the type of categories, it is a 1-groupoid, amounting to the type of equivalences of categories, again automatically.

## Contribution of type theory by Voevodsky

The main technical contributions in type theory by Voevodsky are:

- The definition of type levels in MLTT, classifying them as n-groupoids including the possibility n=∞.
- The (simple and elegant) definition of type equivalence that works uniformly for all type levels in MLTT.
- The formulation of the univalence axiom in MLTT.

Another important aspect of univalent mathematics is the presence of explicit mechanisms for distinguishing

   - *property* (e.g. an unspecified thing exists),
   - *data or structure* (e.g. a designated thing exists or is given),

which are common place in current mathematical practice (e.g. cartesian closedness of a category is a property in some sense (up to isomorphism), whereas monoidal closedness is given structure).




# A spartan Martin-Löf type theory

This is enough to do number theory, analysis, group theory, topology, category theory and more

- An empty type `𝟘`.
- A one-element type `𝟙`.
- A type of `ℕ` natural numbers.
- Type formers `+` (binary sum), `Π` (product), `Σ` (sum), `Id` (identity type).
- Universes (types of types), ranged over by `𝑼` ,`𝑽` ,`𝑾`.

## Init
```agda
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
module Foundation.HTTT where
```

## Universes
```agda
open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝑼₀
          ; Set to Type
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝑼ω
          )
-- open import Data.Product
--   using ( _,_ ; ∃ ; Σ-syntax ; _×_ )
--   renaming ( proj₁ to fst ; proj₂ to snd )

variable
  𝑼 𝑽 𝑾 𝑻 : Universe

infix  1 _̇
_̇ : (𝑼 : Universe) → _
𝑼 ̇ = Set 𝑼


𝑼₁ = 𝑼₀ ⁺
𝑼₂ = 𝑼₁ ⁺
𝑼₃ = 𝑼₂ ⁺
𝑼₄ = 𝑼₃ ⁺
```

## One type element 𝟙

```agda
data 𝟙 : 𝑼₀ ̇ where
 ⋆ : 𝟙
```

Next we want to give a mechanism to prove that all points of the type `𝟙` satisfy a given property A.

  1. The property is a function `A : 𝟙 → 𝑼` for some universe `𝑼`.
  2. The type `A(x)`, which we will write simply `A x`, doesn’t need to be a truth value. It can be any type.
  3. In MLTT, mathematical statements are types, such as `Π A : 𝟙 → 𝑼, A ⋆ → Π x : 𝟙, A x`
  4. We read this in natural language as "for any given property `A` of elements of the type `𝟙`, if `A ⋆` holds, then it follows that `A x` holds for all `x : 𝟙`".
  5. In Agda, the above type is written as `(A : 𝟙 → 𝑼 ̇ ) → A ⋆ → (x : 𝟙) → A x`. This is the type of functions with three arguments `A : 𝟙 → 𝑼 ̇` and `a : A ⋆` and `x : 𝟙` , with values in the type `A x`.
  6. A proof of a mathematical statement rendered as a type is a construction of an element of the type. In our example, we have to construct a function, which we will name 1-induction.

We do that as follows in Agda

```agda
𝟙-induction : (A : 𝟙 → 𝑼 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
```

Given a type `B` and a point `b : B`, we construct the function `𝟙 → B` that maps any given `x : 𝟙` to `b`.

```agda
𝟙-recursion : (B : 𝑼 ̇) → B → (𝟙 → B)
𝟙-recursion  B b x = 𝟙-induction (λ _ → B) b x
```

The above definition has a dual interpretation as a mathematical function, and as the statement "`B` implies (`true` implies `B`)" where 𝟙 is the type encoding the truth value `true`

The *unique* function to 𝟙 

```agda
!𝟙 : { X : 𝑼 ̇ } → X → 𝟙
!𝟙 x = ⋆
```

## The empty type 𝟘

```agda
data 𝟘 : 𝑼₀ ̇ where
```

To prove that a property of elements of the empty type holds for all elements of the empty type, we have to do nothing.

```
𝟘-induction : (A : 𝟘 → 𝑼 ̇) → (x : 𝟘) → A x
𝟘-induction A ()
```

The *unique* function from `𝟘` to any type

```agda
𝟘-recursion : (B : 𝑼 ̇) → 𝟘 → B
𝟘-recursion B x = 𝟘-induction (λ _ → B) x

!𝟘 : (A : 𝑼 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion
```

A type is empty precisely when we have a function to the empty type

```agda
is-empty : 𝑼 ̇ → 𝑼 ̇
is-empty X = X → 𝟘

¬ : 𝑼 ̇ → 𝑼 ̇
¬ = is-empty
```



## Natural number

```agda
data ℕ : 𝑼₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


ℕ-induction : (A : ℕ → 𝑼 ̇) → A 0 → ((n : ℕ) → A n → A (succ n)) → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0 = a₀
    h (succ n) = f n (h n)

ℕ-recursion : (X : 𝑼 ̇) → X → (ℕ → X → X) → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)
```

The following special case occurs often (and is related to the fact that N is the initial algebra of the functor `𝟙 + (-)`):

```agda
ℕ-iteration : (X : 𝑼 ̇) → X → (X → X) → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)
```

In official Martin-Löf type theories, we have to use the N-induction functional to define everything else with the natural numbers. But Agda allows us to define functions by structural recursion, like we defined ℕ-induction.

### Arithmetic operations

```agda
module Arithmetic where
  _+_ _×_ : ℕ → ℕ → ℕ
  infixl 20 _+_
  infixl 21 _×_

  m + n = ℕ-recursion ℕ m (λ n s → succ s) n
  m × n = ℕ-iteration ℕ 0 (m +_) n
```

```agda
module ℕ-order where
  _≤_ _≥_ : ℕ → ℕ → 𝑼₀ ̇
  _≤_ = ℕ-iteration (ℕ → 𝑼₀ ̇) (λ x → 𝟙)
    (λ f → ℕ-recursion (𝑼₀ ̇) 𝟘 (λ y P → f y))

      
  -- 0 ≤ y = 𝟙
  -- succ x ≤ 0 = 𝟘
  -- succ x ≤ succ y = x ≤ y

  _≥_ = {!!}
```
