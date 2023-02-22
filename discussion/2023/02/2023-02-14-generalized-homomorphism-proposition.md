Dear Conal,

Thank you for your valuable suggestion on improving the presentation of
my propositions. I have a new idea to share.

> > Proposition: Given commutative monoid M, set N and
> > a surjective commutative monoid homomorphism f : M → N, N is also
> > a commutative monoid.

> Before you get too involved in proving the propositions, first focus
> on stating them well. I find that up-front effort in stating a lemma
> well is richly rewarded in the in the lemma's proof and in all of its
> uses

> Even if "the proposition/lemma is clear" to you, what is clear is only
> your current best question. Once you write down your current question
> formally in a language as succinct and elegant as Agda, you can then
> stare at your formulation and consider it critically. Ask yourself how
> it can be re-expressed more simply and more generally and in ways that
> embody more beauty & poetry so that it delights you and illuminates
> your topics

I think it can be generalize from *commutative monoid* to arbitrary
algebraic structure. Here is definition of [Algebraic
structure](https://en.wikipedia.org/wiki/Algebraic_structure) on
Wikipedia:

> In mathematics, an algebraic structure consists of a nonempty set A
> (called the underlying set, carrier set or domain), a collection of
> operations on A (typically binary operations such as addition and
> multiplication), and a finite set of identities, known as axioms, that
> these operations must satisfy.

So beside of domain and codomain, it also has a collection of
*operations* and *finite set of identities*:

**Operations**

-   Assuming that we have two algebraic structure `M` `N` and a
    homomorphism `f : M → N` between them
-   An operation `μᵏ` of *arity* `k` that is defined on both `M` and `N`
    -   I didn't come up with this solution on my own. The idea is taken
        from: [UALib](http://ualib.org/Base.Relations.Continuous.html)
    -   `μᵏₘ` is the component that's defined on set `M` that take `k`
        parameter of type `M` : `μᵏₘ : M × M × ... × M → M`
    -   Since we know that `M × M × ... × M (k times) ≃ Mᵏ ≃ Fin k → M`
    -   So an operation `μᵏ` on set `M` is can be defined as:
        `μᵏₘ : (Fin k → M) → M`
    -   Just as you mentioned in *The Essence and Origins of Functional
        Reactive Programming* talk, `ℕ → M ≃ Stream M`, what if we
        replace `ℕ` by `ℝ` or arbitrary type?
-   Given `Mᵏ : M × M × ... × M (k times) ≃ Fin k → M`, there are two
    ways to get a result in `N`
    -   Using `μᵏₙ` to get an element in `M`, then map that to an
        element `N` via `f`
    -   Or using `f` to map each item to `N`, then using `μᵏₙ` to get
        the element in `N`
    -   ***Operation preserving* property said that a homomorphism
        should give both way the same result.**
    -   The property can be demonstrated as this commute diagram:
        `f ∘ μᵏₘ = μᵏₙ ∘ fmap f`
        ![](fff40573ff019520471b765d42ed58d86cf2d158.svg)
    -   That commute diagram remind us of *natural transformation*.
        Indeed:
        -   `(Fin k → )` is a functor
        -   `M` and `N` can be seen as objects lifted by `Id` *functor*
        -   `μᵏₘ` and `μᵏₙ` are components of *natural transformation*
            `μ` from `(Fin k → )` to `Id` functor

**Identities (laws)**

-   I haven't found a good generalization for the identities, but I
    think I have more precise details for identities definition
-   Identity is an **equality**, that mean it's a binary relationship
    between two objects that has *reflective*, *symmetric*, *transitive*
    properties. So it's similar to `≡` in Agda, not just arbitrary
    (binary) relation
-   I think algebraic structure without identities are similar to *Free
    categories* in category theory. In that sense, set of *identities*
    is correspondence to *monoid morphism* (in category theory
    definition, not monoid homomorphism) from *free monoid* to \<???\>

Here is an example of proof that homomorphism preserving associative
laws, (actually it's not only for associative laws, but any laws that
has the same *shape*), but I haven't found a generalization for
arbitrary `k` arity *operations*:

``` agda
f : M → N
μₘ : (M × M) → M
μₙ : (N × N) → N

p-laws : μₘ (μₘ a₁ a₂) a₃ ≡ μₘ a₁ (μₘ a₂ a₃) → μₙ (μₙ (f a₁) (f a₂)) (f a₃) ≡ μₙ (f a₁) (μₙ (f a₂) (f a₃))
p-laws = μₙ (μₙ (f a₁) (f a₂)) (f a₃)
  ≡⟨⟩ μₙ (f (μₘ a₁ a₂)) (f a₃)  
  ≡⟨⟩ f (μₘ (μₘ a₁ a₂) a₃)
  ≡⟨⟩ f (μₘ a₁ (μₘ a₂ a₃))
  ≡⟨⟩ μₙ (f a₁) (f (μₘ a₂ a₃))
  ≡⟨⟩ μₙ (f a₁) (μₙ (f a₂) (f a₃))
```

I will dedicate more time to this and keep you informed with regular
updates.

Best regards,

Thông
