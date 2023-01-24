Dear Conal,

> Would you mind re-sending your note below (to which I’m responding) and its P.S. as Markdown?

Sure, I have created the Markdown file, but when I display it, the formatting does not look as intended.

> Wow—you’ve taken to Agda very well! I hope you’re having fun with it (as I am).

Thank you for encouraging me with Agda - I am finding it both challenging and rewarding .I am enjoying the challenge and rewards that Agda brings, and it is also intriguing to ponder on the relationship between logic, philosophy and programming while using Agda.

>  in MonoidH, what role do the instance arguments play? In other words, how do the monoid laws affect the notion of a monoid homomorphism? Likewise for semiring homomorphisms.

Thank you. I see the issue with my implementation that I didn't use any properties of the monoids to prove that (x ^\_) is a homomorphism. I think I should only use properties of (x ^\_), monoid properties of domain and codomain to prove that. I have come up with an implementation but I'm not satisfied with it:
- I'm not sure of it's correct to implement `monoidₘ` , `monoidₙ` as record field of `MonoidH` is right way to express the monoid constraint.
- I've to explicitly pass `ℕ*-monoid` instance.

<!--
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6  _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
```
Proving (ℕ , _+_ , zero) is monoid

```agda
+-identityˡ : ∀ (n : ℕ) → zero + n ≡ n
+-identityˡ n = refl

+-identityʳ : ∀ (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n) =
  begin
    suc n + zero
    ≡⟨⟩ -- _+_ definition
    suc (n + zero)
    ≡⟨ cong suc (+-identityʳ n) ⟩
    suc n
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

-- proving (ℕ , _*_, 1) is monoid

*-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityˡ n rewrite +-identityʳ n = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

-- to prove *-assoc, we need to prove *-distrib-+
*-distribʳ-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distribʳ-+ zero n p = refl
*-distribʳ-+ (suc m) n p
  rewrite *-distribʳ-+ m n p
  | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distribʳ-+ n (m * n) p
  | *-assoc m n p
  = refl

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

```
-->

```agda
record Monoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
  field
    ∙-identityʳ : ∀ (a : A) → a ∙ e ≡ a
    ∙-identityˡ : ∀ (a : A) → e ∙ a ≡ a
    ∙-assoc : ∀ (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
open Monoid ⦃ ... ⦄ public

-- proof that (ℕ, _+_ , 0) is monoid
instance
  ℕ+-monoid : Monoid 0 _+_
  ℕ+-monoid = record
    { ∙-identityʳ = +-identityʳ
    ; ∙-identityˡ = +-identityˡ
    ; ∙-assoc = +-assoc
    }

-- proof that (ℕ, _*_ , 1) is monoid
instance
  ℕ*-monoid : Monoid 1 _*_
  ℕ*-monoid = record
    { ∙-identityʳ = *-identityʳ
    ; ∙-identityˡ = *-identityˡ
    ; ∙-assoc = *-assoc
    }

record MonoidH
    {M N : Set} (eₘ : M) (_∙ₘ_ : M → M → M)
    (eₙ : N) (_∙ₙ_ : N → N → N)
    (f : M → N)
  : Set where
  field
    P-∙ : ∀ (a b : M) → f (a ∙ₘ b) ≡ f a ∙ₙ f b
    P-id : f eₘ ≡ eₙ
    ⦃ monoidₘ ⦄ : Monoid eₘ _∙ₘ_
    ⦃ monoidₙ ⦄ : Monoid eₙ _∙ₙ_
open MonoidH ⦃ ... ⦄

instance
  x^-MonoidH-ℕ+-ℕ* : ∀ {x : ℕ} → MonoidH 0 _+_ 1 _*_ (x ^_)
  P-∙ ⦃ x^-MonoidH-ℕ+-ℕ* {x} ⦄ zero b = trans (sym (∙-identityʳ (x ^ b))) refl -- FIXME: Why does this doesn't requires explicit passing instance
  P-∙ ⦃ x^-MonoidH-ℕ+-ℕ* {x} ⦄ (suc a) b
    rewrite P-∙ ⦃ x^-MonoidH-ℕ+-ℕ* {x} ⦄ a b
    | sym (∙-assoc ⦃ ℕ*-monoid ⦄ x (x ^ a) (x ^ b)) -- FIXME: And this requires?
    = refl
  P-id ⦃ x^-MonoidH-ℕ+-ℕ* ⦄ = refl

```

>  is x ^_ a commutative monoid homomorphism?

Yeah, it's a commutative monoid homomorphism. As a monoid morphism is a super class of commutative monoid morphism, I'm not sure if I represented that relation correctly in my proof.

```agda
+-suc-swap : ∀ (m n : ℕ) → suc m + n ≡ m + suc n
+-suc-swap zero n = refl
+-suc-swap (suc m) n rewrite +-suc-swap m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n
  rewrite +-comm m n
  | +-suc-swap n m
  = refl

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

record CommMonoid {A : Set} (e : A) (_∙_ : A → A → A) : Set where
  field
   ∙-comm : ∀ (a b : A) → a ∙ b ≡ b ∙ a
   ⦃ monoid ⦄ : Monoid e _∙_
open CommMonoid ⦃ ... ⦄ public

instance
  +-CommMonoid : CommMonoid 0 _+_
  +-CommMonoid = record
    { ∙-comm = +-comm
    }
  *-CommMonoid : CommMonoid 1 _*_
  *-CommMonoid = record
    { ∙-comm = *-comm
    }

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

instance
  x^-CommMonoidH-ℕ+-ℕ* : ∀ {x : ℕ} → CommMonoidH 0 _+_ 1 _*_ (x ^_)
  P-comm ⦃ x^-CommMonoidH-ℕ+-ℕ* {x} ⦄ a b
    rewrite ∙-comm ⦃ +-CommMonoid ⦄ a b
    = refl
```

>  As a first hint, I’ll just suggest re-reading the second puzzle more carefully and contrasting its wording with that of the first puzzle. I think there’s more freedom in this question than you realized.

Thank you for your suggestion to re-read the second puzzle more carefully and contrasting its wording with that of the first puzzle. I will give it more thought.

> Would you mind re-sending your note below (to which I’m responding) and **its P.S.** as Markdown?

> PS: I'm thinking that (x ^\_) similar to a → x which is a contravariant in the input type, and maybe I could use only the facts that (x ^\_) is contravariant, M and N are monoid to prove the homomorphism properties.

Regarding my P.S, it's just initial ideal. I haven't finished it yet. I thought of that because I think (x ^\_) is also a monoid morphism in Cartesian Closed category, in the sense that:

  - Function (exponential type) of a sum type is a product type of function: (A ⊎ B) → C ≃ (A → C) × (B → C)
  - There is only one function from unit of sum type: ⊗ → A ≃ 1 -- absurd function

So I think it could be the fact that exponential is homomorphism is because (x ^\_), _+_, and _*_ formed a Cartesian Closed category.

Thank you
