Dear Conal,

Sorry for late response. I think I finally understand your question.

> In your CommMonoidH class, what purpose is served by the P-comm, comm-monoidₘ and comm-monoidₙ fields? In other words, what value would be lost if you eliminated them? Likewise, in your MonoidH class, what purpose is served by the third and fourth fields (monoidₘ and monoidₙ)?

### `MonoidH` class
If `monoidₘ` is constrained, but `monoidₙ` is *not* constrainted, then even if `f` satisfied `MonoidH` property, f does not preserve identity property. Proof:

  - Given `a` in *monoidₘ*, we have: `eₘ ∙ₘ a ≡ a ≡ a ∙ₘ eₘ`
  - Applying f to each of them and then use `P-∙` property, we have:

```agda
    f a                       ≡ f a
    f (a ∙ₘ eₘ) ≡ f a ∙ₙ f eₘ ≡ f a ∙ₙ eₙ
    f (eₘ ∙ₘ a) ≡ f eₘ ∙ₙ f a ≡ eₙ ∙ₙ f a
```
  - But since `monoidₙ` is not constrained, in general `f a ∙ₙ eₙ ≢ f a ≢ eₙ ∙ₙ f a`.
  - So from single value `a` in `M`, there are there different way transform it through `f`, a faulty monoid morphism,  each each of them give a different result.

Similar with `∙-assoc` property, we might get two different results from transforming `a ∙ₘ b ∙ₘ c` through f since `(f a ∙ₙ f b) ∙ₙ f c ≢ f a ∙ₙ (f b ∙ₙ f c)`.

So that even though `f` satisfied two properties of the faulty `MonoidH`, it does not preserve monoid structure.

So what if `monoidₘ` is not constrained? In this case, `M` has no structure, so there is no point of saying that `f` preserve any structure.

### `CommMonoidH` class
Similar to `MonoidH`, given `P-comm` is proved. 

  - If `comm-monoidₘ` is not constrained, then there is no (communicative) structure to preserve. 
  - If `comm-monoidₙ` is not constrained, we can not say `f` preserve communicative properties since given `a ∙ₘ b` in `M`, we got different results `f a ∙ₙ f b ≢ f b ∙ₙ f a` after transformed by `f`.

> P.S. Please let me know if you have a preference for my emails to be rendered, raw Markdown, rendered and raw as an attachment, or some other variation.

Thanks, I have no preference and you can use any style that works best for you.

Best Regards,

Thong
