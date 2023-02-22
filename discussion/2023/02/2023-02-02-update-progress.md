Dear Conal,

I'm sorry for not providing an update on my progress as I haven't made
significant advancements. However, I want to let you know that I am
still dedicated to working on the problem. I'm running into a rabbit
hole while attempting to define epimorphism/surjective function in Agda.
I am now reading the first part of "The Agda Universal Algebra Library
Part 1: Foundation" to gain a better understanding and replicate the
process of defining surjective/injective functions. Once that is
complete, I will continue my efforts towards proving the proposition.

> Before you get too involved in proving the propositions, first focus
> on stating them well. I find that up-front effort in stating a lemma
> well is richly rewarded in the in the lemma's proof and in all of its
> uses

Thank you for your advice. As an engineer, I sometimes fall into the
trap of jumping into problem-solving without fully considering the issue
at hand. This often results in code that lacks reusability, contains
bugs, and only partially solves the problem, ... . It's like: "Here is
my solution for the problem. Hmm, but what problem?". I understand that
it's very important to define/understand problem correctly before trying
to solve it. I'll try to keep this in mind going forward.

Btw, please forgive me if my concern is obvious to you. Do you ask me to
focus on stating the proposition/lemma about the homomorphism more
clearly, or it's just reminding in general. Because I think the
proposition/lemma is clear to me.

> Explore the dual question: under what conditions do laws transfer from
> target to source of a homomorphism?

> There may be something interesting to find in the direction you
> started as well: is there a homomorphism-like property for which law
> transference holds even without surjectivity?

Thank you for the hints. I have an idea for that, but I haven't had
proof for it in Agda yet. I've to finish the definition of
surjective/injective function in Agda before I can prove this.

**Proposition:** Given *raw* monoid `M`, *commutative monoid* `N` and an
*injective monoid homomorphism* `f : M → N`, we can conclude that `M` is
also a `commutative monoid`

**Proof:**

-   Assoc: For any `a, b, c ∈ M`, we need to prove
    `(a + b) + c ≡ a + (b + c)`
    -   We have

              f ((a + b) + c)
              ≡ f (a + b) * f c -- f is homo
              ≡ (f a * f b) * f c -- f is homo
              ≡ f a * (f b * f c) -- (N, *) is assoc
              ≡ f a * f (b + c) -- f is homo
              ≡ f (a + (b + c)) -- f is homo

    -   Since `f` is an *injective* function `f x ≡ f y → x ≡ y`, so we
        have

            f ((a + b) + c) ≡ f (a + (b + c)) → ((a + b) +c ) ≡ (a + (b + c))
-   The proofs for *identity* and *commutative* are similar

I'll keep you updated on my progress of proving the proposition.

Best regards,

Thông
