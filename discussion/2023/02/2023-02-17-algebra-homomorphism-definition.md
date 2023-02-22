Dear Conal,

I've *found* a definition of the homomorphism and this one is quite
interesting. But ... it's not in type theory or set theory.

### Generalization of algebraic structure definition

Regarding the idea of representing *operation* in the previous email:

> An operation μᵏ of arity k that is defined on both M and N
>
> -   μᵏₘ is the component that's defined on set M that take k parameter
>     of type M : μᵏₘ : M × M × ... × M → M
> -   Since we know that M × M × ... × M (k times) ≃ Mᵏ ≃ Fin k → M
> -   So an operation μᵏ on set M is can be defined as: μᵏₘ : (Fin k
>     → M) → M
> -   Just as you mentioned in The Essence and Origins of Functional
>     Reactive Programming talk, ℕ → M ≃ Stream M, what if we replace ℕ
>     by ℝ or arbitrary type?

We can take a few more steps:

-   Instead of definition **an operation** as `μ :: I → M`, in which `I`
    can be *any* type, we can replace by `μ :: Functor F ⇒  F M`
    (Haskell notation)
-   Algebraic structure usually has not only one but a set of
    operations. Well, we can also define that set with exactly the
    definition of `μ` above.
    -   For example:
        -   Monoid has a *pair* operation: `μ :: M × M → M` and
            `η : 1 → M`. In other word, `Monoid ≃  μ × η`

        -   Since `a → b ≃ bᵃ`, so we have:
            `Monoid ≃  μ × η ≃  (M × M)ᴹ × 1ᴹ ≃  (M × M + 1)ᴹ`

        -   We can represent `M × M + 1` or even arbitrary by `F M`

            ``` agda
            type Algebra f a = f a → a
            ```
-   So `Algebra f a` is generalized definition of algebraic structure in
    set theory. *Simple* structure such as monoid, group, ring ... are
    just special case in which number and arity of *operations* are
    finite and "discrete".

But algebraic structure in set theory also has laws in its definition.
How is it encoded in category theory definition? Let see some example:

-   A functor `F` that correspond to *monoid* is a *list monad*.
    -   `F` map identity element to `[]`
    -   `F` map `a ⊗ b` to `[a,b]`
    -   `F` map a `[a]`
    -   So we can see that there is correspondence between:
        -   `𝕖 ≃ []`
        -   `(⊗) ≃ (++)`
        -   `⊗` and `(++)` is associative
        -   `a ⊗ 𝕖 = a = 𝕖 ⊗ a ≃ xs ++ [] = xs = [] ++ xs`
        -   The list monad not only *encoded* monoid operations but also
            monoid laws nicely
    -   Example, *all* of following expressions of a monoid over set of
        integers are mapped to `[2, 3, 4]`
        -   `2 ⊗ (3 ⊗ 4)` :
            `[ [[2]] , [[3], [4]] ] → [ [2] , [3, 4] ] → [2, 3, 4]`
        -   `(2 ⊗ 3) ⊗ 4` :
            `[ [[2], [3]] , [[4]] ] → [ [2, 3] , [4] ] → [2, 3, 4]`
        -   `(2 ⊗ 3) ⊗ 𝕖 ⊗ 4` :
            `[ [[2], [3]] , [[]] [[4]] ] → [ [2, 3] , [] , [4] ] → [2, 3, 4]`
    -   Evaluator of an algebra is a morphism that map `F a → a`
        -   In case of `(ℕ, _+_, 0)`: `algebraPlus :: [ℕ] → ℕ`,
            `algebraPlus = foldr (+) 0`
        -   In case of `(ℕ, _*_, 1)`: `algebraMult : [ℕ] → ℕ`,
            `algebraMult = foldr (*) 1`
        -   Not any algebra `(ℕ, [ℕ] → ℕ)` corresponds to a monoid, only
            algebras which compatible with the *list monad* will do
            (T-algebra).
            -   For example, `fAlg = foldr (*) 2` is also an valid
                evaluator of an algebra, but that algebra does not
                correspond to any monoid
    -   Given algebra `alg :: T a → a` and *monad* `T` with
        `η :: a → T a`, `μ :: T (T a) → T a`. `alg` is compatible with
        `T` if:
        -   `alg ∘ η = idₐ`
        -   `alg ∘ μₐ = alg ∘ T alg` (`T alg` mean $fmap_T\ alg$)
        -   Because `T` is a monad, such algebra always exists. It's
            *free T-algebra* `(T a, μₐ)`.
            -   Note that the algebra evaluator is `μₐ :: T (T a) → T a`
-   A functor `T` that correspond to *communicative monoid* is a *finite
    multiset monad*.
-   That's not coincidence, *list* is *free monoid* and *finite
    multiset* is *free communicative monoid*
-   It can be generalized for [arbitrary algebraic
    structure](https://ncatlab.org/nlab/show/algebra+over+a+monad)

### Generalization of homomorphism

We've seen that the algebraic structure is correspond to algebra over a
monad. So what's correspond to homomorphism in set theory? Intuitively,
it should be a (homo)morphism which preserve structure of the domain, so
it should be a morphism between monad algebra (T-Algebra). And that's
the same one with F-algebra (homo)morphism. An *F-algebra* morphism
between `(a, f :: T a → a)` and `(b, g :: T b → b)` is morphism
`m :: a → b` such that this diagram commute `m ∘ f = g ∘ T m`.

![](bd347a4b8b3cffee44ec32f74afafeab4b93ece5.svg)

*There is a way to construct T-algebra morphism*, but I'm not sure if
it's possible to construct *all* morphism between T-algebra

-   Since `T` is monad, algebra morphism on `T` has type `T a → T b`.
    Any morphism that has type `f :: a → T b` is called a *T-Kleisli
    morphism*
    ![](4df2f5200d5b8e3152f7a2c36fe0b5467d614a33.svg)
-   Furthermore, if we have another morphism `g ::  b → T c`, we can
    compose `f` and `g` via Kleisli composition to produce arrow
    `g ∘ₜ f :: a → T c`
    ![](54b9fe02be8a28c73c850899c2473b82c5165cfd.svg)
-   *T-Kleisli morphism* and *Kleisli composition* form a *Kleisli
    category*.

Let see the a concrete example of homomorphism `(3 ^)` between
`(ℕ, +, 0)` and `(ℕ, *, 1)`.

![](91058fd52acbd5840cdff35722e9a6a6c8ee14c9.svg)

*This definition is generalized than [homomorphism definition in set
theory](https://en.wikipedia.org/wiki/Homomorphism) because it's
generalized for arbitrary algebra structure, not only the one which its
operations have form \`μ : A × A × ... × A → A*

Actually, we can easily see that *definition of homomorphism in set
theory is just a case of F-algebra morphism*. The operation preserving
property of homomorphism `h : A → B` for an operation `μ` defined on
both `A` and `B` is `h (μ₁ a₁ a₂ ... aₖ) = μ₂ (h a₁) (h a₂) ... (h aₖ)`.
If we replace `m = h`, `μ₁ = f`, `μ₂ = g` to algebra morphism commute
diagram above (`m ∘ f = g ∘ fmap m`), the operation preserving property
is just `h ∘ f = g ∘ fmap h`.

### Proving that homomorphism preserve algebra structure

Now comeback to the original problem. We need to prove that the
homomorphism preserve algebraic structure. Except, we don't need to
prove anything. It's preserved by definition. Under algebra morphism
`m :: a → b`, `(a, f :: T a → a)` is mapped to `(b, g :: T b → b)`. The
algebra structure is *encoded* in `T` which is the same for both `f` and
`g`.

This is similar to how the homomorphism in set definition preserve laws.

How do we translate this proposition? \> Given commutative monoid M, set
N and a surjective commutative monoid homomorphism f : M → N then N is
also a commutative monoid. Unfortunately, I haven't found such
correspondence.

### Free monad and monad algebra

Given an algebra structure such as *Monoid*, we can define a *base
functor* based on its operations. For example:

``` haskell
data MonoidF a 
    = EmptyF 
    | AppendF a a
```

There is a *free monad* generated from the base functor. Free algebra on
the free monad is correspond to the *raw monoid* structure that we
discussed.

From the free monad, there is an *unique* *monad morphism* to other
monad (`Free f a → m a`) if there exist *a morphism from the base
functor to the that monad* (`f x → m x`). In case of *monoid*, that
other monad can be list monad.

``` haskell
foldFree :: (Monad m) => (forall x. f x -> m x) -> Free f a -> m a
```

I think that `f x → m x` is correspond to laws of algebraic structure in
set theory.

If we see monoid expression is a *program* written in *monoid language*,
then the base functor is *grammar* of *monoid language*, the free monad
is parse tree, the interpreted monad is abstract syntax tree, algebra
morphism can *translate* to other domain (from AST to binary code,
graph, ...), and the monad algebra evaluate that.

But the algebra morphism can only translate between the same algebra
structure? Do we have something translate from less structure to more
structure?

It's quite interesting to see how far we can go with simple definition
of algebra `F a → a`. The beauty of mathematics.

I'm not sure if using algebraic structure definition in set theory has
any advantage over this definition. What's your opinions on this?

Best regards,

Thông
