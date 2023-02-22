Hi Conal,

I've included definition and proof for commutative monoid in the email
above. I defined as following:

A *monoid* is an algebra structure with identity and associative
properties

``` agda
record Monoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
  field
    ∙-identityʳ : ∀ (a : A) → a ∙ e ≡ a
    ∙-identityˡ : ∀ (a : A) → e ∙ a ≡ a
    ∙-assoc : ∀ (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
open Monoid ⦃ ... ⦄ public
```

A *commutative monoid* is a *monoid* with additional commutative
property: `a . b ≡ b . a`

``` agda
record CommMonoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
  field
   ∙-comm : ∀ (a b : A) → a ∙ b ≡ b ∙ a
   ⦃ monoid ⦄ : Monoid e _∙_
open CommMonoid ⦃ ... ⦄ public
```

Here, I use `⦃ monoid ⦄ : Monoid e _∙_` as instance field to represent
`Monoid` as superclass of `CommMonoid`

Given the fact that (ℕ , *+* , 0) is *monoid* that we've already proved,
we need to prove its *commutative* property as bellow:

``` agda
+-suc-swap : ∀ (m n : ℕ) → suc m + n ≡ m + suc n
+-suc-swap zero n = refl
+-suc-swap (suc m) n rewrite +-suc-swap m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n
  rewrite +-comm m n
  | +-suc-swap n m
  = refl

instance
  +-CommMonoid : CommMonoid 0 _+_
  +-CommMonoid = record
    { ∙-comm = +-comm
    }
```

Similar for (ℕ , \_*\_ 1) to be a *commutative monoid\*:

``` agda
*-zeroˡ : ∀ (n : ℕ) → 0 * n ≡ 0
*-zeroˡ n = refl
*-zeroʳ : ∀ (n : ℕ) → n * 0 ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) zero rewrite *-zeroʳ m = refl
*-comm (suc m) (suc n)
  rewrite *-comm m (suc n)
  | *-comm n (suc m)
  | *-comm m n
  | sym (+-assoc n m (n * m))
  | +-comm n m
  | +-assoc m n (n * m)
  = refl

*-CommMonoid : CommMonoid 1 _*_
*-CommMonoid = record
  { ∙-comm = *-comm
  }
```

Given `⦃ comm-monoidₘ ⦄ : CommMonoid eₘ _∙ₘ_`,
`⦃ comm-monoidₙ ⦄ : CommMonoid eₙ _∙ₙ_` that are *commutative monoid*,
and there is a *monoid morphism*
`⦃ monoidH ⦄ : MonoidH eₘ _∙ₘ_ eₙ _∙ₙ_ f` between them, then a
*commutative monoid morphism* is defined as bellow:

``` agda
record CommMonoidH
    {M N : Set} (eₘ : M) (_∙ₘ_ : M → M → M)
    (eₙ : N) (_∙ₙ_ : N → N → N)
    (f : M → N)
  : Set where
  field
    P-comm : ∀ (a b : M) → f (a ∙ₘ b) ≡ f (b ∙ₘ a)
    ⦃ comm-monoidₘ ⦄ : CommMonoid eₘ _∙ₘ_
    ⦃ comm-monoidₙ ⦄ : CommMonoid eₙ _∙ₙ_
    ⦃ monoidH ⦄ : MonoidH eₘ _∙ₘ_ eₙ _∙ₙ_ f
open CommMonoidH ⦃ ... ⦄
```

So we've already prove `(ℕ , _+_ , 0)`, `(ℕ , _*_, 1)` are `CommMonoid`,
and morphism between them is a *monoid morphism*. The proof that it's
indeed a *commutative morphism* is given as bellow

``` agda
instance
  x^-CommMonoidH-ℕ+-ℕ* : ∀ {x : ℕ} → CommMonoidH 0 _+_ 1 _*_ (x ^_)
  P-comm ⦃ x^-CommMonoidH-ℕ+-ℕ* {x} ⦄ a b
    rewrite ∙-comm ⦃ +-CommMonoid ⦄ a b
    = refl
```

The different between *commutative monoid homomorphism* and *monoid
homomorphism* is that it also preserves the *commutativity* of the
operation between two commutative monoids, while a monoid homomorphism
is a morphism that only preserves the monoid structure (operation and
identity element) between any two monoids. A *monoid homomorphism* does
*not necessarily preserve commutativity*.
