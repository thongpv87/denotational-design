Dear Conal,

Thank you very much for your feedback. I've been getting busy recently.
I'll be back on Tue next week.

> Formalize your law transfer lemma and proof.

I've given it a try, but I got problem when try represent `Homomorphism`
in Agda. Previously, I define homomorphism as `≡` relationship but I
find that the homomorphism is only *implies* relationship, because the
map is not always epimorphism so given elements in codomain, we can not
find the element in the domain (it may not in the image of the
epimorphism). My plan is representing it as `Homo₀`, `Homo₁`, `Homo₂`
for nullary, unary, binary homomorphism, and then the monoid
homomorphism will need to have `Homo₀`, `Homo₂` as type instance
arguments or record field, such as bellow:

``` agda
-- nullary operations homomorphism

record Homo₀
    {M N : Set}
    (eₘ : M)
    (eₙ : N)
    (f : M → N)
  : Set where
  field
    homo₀ : eₘ → eₙ

-- binary operation homomorphsim
record Homo₂
    {M N : Set}
    (_∙ₘ_ : M → M → M)
    (_∙ₙ_ : N → N → N)
    (f : M → N)
  : Set where
  field
    homo₂ : ∀ (a b : M) → (a ∙ₘ b) → (f a ∙ₙ f b)
  
```

But that definition don't compile in Agda. I think Agda expect elements
in signature of `homo₀`, `homo₂` need to be a `Set`. So `eₘ`, `eₙ` need
to be a `Set` or `_∙ₘ_` `_∙ₙ_` need to return a `Set` to make Agda
compile. I'm not sure if changing that to Set make the representation of
homomorphism in Agda less precise? Do you have any recommend for better
representation of homomorphism in Agda?

> Since you are accumulating notes and code (including lemmas & proofs),
> I suggest organizing what you've done and what you will do in a GitHub
> repository, including a chronologically ordered index that links to
> the individual files. I'll leave it up to you whether to make the
> repository private (shared just with me) or public. I suggest
> including a Makefile for rendering the Markdown files to HTML (and
> later, .lagda.tex files to PDF). In this repository, we can also
> create issues for discussion and even use pull requests for detailed
> review feedback. I think we can shift most of our conversations from
> email to GitHub in this way. How do these suggestions sound to you?

Yeah, I think that's great idea. I think having conversations in Github
is quite convenience. I'll reorganize the Github repository in next week
since I'm quite busy right now. But I would prefer to keep the
repository private for several months until I've made more progress and
am ready to make it public.

Best regards,

Thông
