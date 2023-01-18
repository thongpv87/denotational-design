import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning


-- *** Prove that x ^_ is a monoid homomorphism

-- What's a monoid in Set? Given a set S, an element e ∈ S and a binary operation (_∙_) : S → S → S, (S, _∙_ , e) a monoid it satisfies following laws:
--   - associativity:  (a ∙ b) ∙ c = a ∙ (b ∙ c)
--   - left identity: e ∙ a = a
--   - right identity: a ∙ e = a
-- A monoid (homo)morphism is a monoid that preserve monoid structure. Given (M, _∙ₘ_ , eₘ) and (N, _∙ₙ_ , eₙ) that are monoid,
-- a monoid morphism h : M → N is a morphism such that:
--   ∀ (m₁ m₂ : M) → f (m₁ ∙ₘ m₂) ≡ f m₁ ∙ₙ f m₂
--   f eₘ = eₙ
-- In case of exponential on natural numbers, domain and codomain of monoid morphism are:
--   - domain monoid: (M, _+_ , 0)
--   - codomain monoid: (N, _*_, 1)
--
-- In sumary, to prove x ^_ is monoid homomorphism on natural number, we need to prove following:
--   - Prove (ℕ, _+_ , 0) and (ℕ, _*_ , 1) are monoid by prove associtivity and identity properties
--   - ∀ (x a b : ℕ) → x ^ (a + b) = (x ^ a) * (x ^ b)
--   - ∀ (x : ℕ) → x ^ 0 = 1

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6  _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- Proving (ℕ , _+_ , zero) is monoid

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
    ⦃ _ : Monoid eₘ _∙ₘ_ ⦄
    ⦃ _ : Monoid eₙ _∙ₙ_ ⦄
    : Set where
  field
    P-∙ : ∀ (a b : M) → f (a ∙ₘ b) ≡ f a ∙ₙ f b
    P-id : f eₘ ≡ eₙ


infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

^-distribˡ-+-* : ∀ (x a b : ℕ) → x ^ (a + b) ≡ x ^ a * x ^ b
^-distribˡ-+-* x zero b rewrite +-identityʳ (x ^ b) = refl
^-distribˡ-+-* x (suc a) b
   rewrite ^-distribˡ-+-* x a b
   | sym (*-assoc x (x ^ a) (x ^ b))
   = refl

instance
  x^-MonoidH-ℕ+-ℕ* : ∀ {x : ℕ} → MonoidH 0 _+_ 1 _*_ (x ^_)
  x^-MonoidH-ℕ+-ℕ* {x} = record
    { P-∙ = λ a b → ^-distribˡ-+-* x a b
    ; P-id = refl
    }


-- *** Prove that x ^_ is semiring homomorphism
-- We need proving extra natural functions properties to prove this

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

*-distribˡ-+ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*-distribˡ-+ m n p
  rewrite *-comm m (n + p)
  | *-distribʳ-+ n p m
  | *-comm n m
  | *-comm p m
  = refl


record CommMonoid {A : Set} (e : A) (_∙_ : A → A → A) ⦃ _ : Monoid e _∙_ ⦄ : Set where
  field
   ∙-comm : ∀ (a b : A) → a ∙ b ≡ b ∙ a
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

instance
  ^-Monoid : Monoid 1 _^_
  ^-Monoid = record
    { ∙-identityʳ = {!!}
    ; ∙-identityˡ = {!!}
    ; ∙-assoc = {!!}
    }

record Semiring {A : Set} (i : A) (_+_ : A → A → A) (e : A) (_*_ : A → A → A)
  ⦃ _ : Monoid i _+_ ⦄ -- FIXME: CommMonoid included Monoid constraint, how can I remove this?
  ⦃ _ : CommMonoid i _+_ ⦄
  ⦃ _ : Monoid e _*_ ⦄
  : Set where
  field
    semiring-distribʳ : ∀ (m n p : A) → ((m + n) * p) ≡ ((m * p) + (n * p))
    semiring-distribˡ : ∀ (m n p : A) → m * (n + p) ≡ (m * n) + (m * p)
    semiring-zeroʳ : ∀ (m : A) → m * i ≡ i
    semiring-zeroˡ : ∀ (m : A) → i * m ≡ i
open Semiring ⦃ ... ⦄ public

instance
  +-*-Semiring : Semiring 0 _+_ 1 _*_
  +-*-Semiring = record
    { semiring-distribʳ = *-distribʳ-+
    ; semiring-distribˡ = *-distribˡ-+
    ; semiring-zeroʳ = *-zeroʳ
    ; semiring-zeroˡ = *-zeroˡ
    }

record SemiringH
    {M N : Set}
    (iₘ : M) (_+ₘ_ : M → M → M)
    (eₘ : M) (_*ₘ_ : M → M → M)
    (iₙ : N) (_+ₙ_ : N → N → N)
    (eₙ : N) (_*ₙ_ : N → N → N)
    (f : M → N)
    ⦃ _ : Monoid iₘ _+ₘ_ ⦄
    ⦃ _ : CommMonoid iₘ _+ₘ_ ⦄
    ⦃ _ : Monoid eₘ _*ₘ_ ⦄
    ⦃ _ : Semiring iₘ _+ₘ_ eₘ _*ₘ_ ⦄
    ⦃ _ : Monoid iₙ _+ₙ_ ⦄
    ⦃ _ : CommMonoid iₙ _+ₙ_ ⦄
    ⦃ _ : Monoid eₙ _*ₙ_ ⦄
    ⦃ _ : Semiring iₙ _+ₙ_ eₙ _*ₙ_ ⦄
    : Set where
  field
    semiring-+-P : ∀ (a b : M) → f (a +ₘ b) ≡ f a +ₙ f b
    semiring-*-P : ∀ (a b : M) → f (a *ₘ b) ≡ f a *ₙ f b
    semiring-i-P : f iₘ ≡ iₙ
    semiring-e-P : f eₘ ≡ eₙ

-- instance
--   x^-SemiringH-ℕ+*-ℕ*^ : ∀ {x : ℕ} → SemiringH 0 _+_ 1 _*_ 1 _*_ 1 _^_ (x ^_)
--   x^-SemiringH-ℕ+*-ℕ*^ {x} = record
--     { semiring-+-P = ?
--     ; semiring-*-P = {!!}
--     ; semiring-i-P = {!!}
--     ; semiring-e-P = {!!}
--     }
