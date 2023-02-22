Dear Conal,

Thanks you for your response. Following are my opinions on your
questions.

> How would you define a commutative monoid homomorphism? In particular,
> how does it differ from a monoid homomorphism?

Communicative monoid on set `M` is defined as bellow:

-   

    Operations
    :   Multiplication: `_×_ : M → M → M`
    :   Identity: `eₘ : M`

-   

    Laws:
    :   Associative: `(a × b) × c`
    :   Identity: `eₙ × a = a = a × eₙ`
    :   Communicative: `a × b = b × a`

Given a set `N` equiped with two operations `_+_ : N → N → N` and
`eₙ : N` (that doesn't necessary to satisfy commutative monoid laws), a
function `f : M → N` is *commutative monoid homomorphism* if it
perserves operations of *commutative monoid*, that mean it is required
to:

-   preserves multiplication operation: `f (a × b) = f a + f b`
-   preserves identity operation: `f eₘ = eₙ`

Proposition: Given *commutative monoid* `M`, set `N` and commutative
monoid homomorphism `f : M → N`, image of `M` under `f` is also a
*commutative monoid*

Proof:

-   Associativity:

    -   Assuming that we have `a, b, c ∈ M` and `f a, f b, f c ∈ N` that
        are their outputs under `f`
    -   By associative laws of `M`, we have: `(a × b) × c = a × (b × c)`
    -   Applying `f` to both sides of the equation:
        `f ((a × b) × c) = f (a × (b × c))`
    -   By multiplication preserving property of `f`, we also have:
        -   `f ((a × b) × c) = f (a × b) + f c = (f a + f b) + f c`
        -   `f (a × (b × c)) = f a + f (b × c) = f a + (f b + f c)`
    -   Replace the result from 4th step to the equation at 3rd step, we
        have: `(f a + f b) + f c = f a + (f b + f c)`
    -   So we can conclude that `_+_` is associative in image of `M`
        under `f`

-   Proof for identity and commutative laws is also similar

> What would be lost if you let homomorphisms preserve operations and
> not laws?

I think nothing is lost.

> What would be gained?

-   Simplify proof for homomorphism, no need to prove that homomorphism
    preserve laws, it's laws for free.
-   If a commutative monoid homomorphism is also epimorphism, we can
    also conclude that its codomain is also commutative monoid
-   Codomain is no longer required to be commutative monoid. Less
    constraints, more homomorphisms

Best regards,

Thông
