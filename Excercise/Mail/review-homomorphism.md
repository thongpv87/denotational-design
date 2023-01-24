Dear Conal,

I've reviewed homomorphism definition and I think now I understand how did I miss understood homomorphism definition.

Please correct me if I am wrong. Given:

  - Two sets, `A` and `B`
  - A morphism `f : A → B`
  - An operation `μ` of *arity* k that defined in both `A` and `B`, corresponding to `μ₁` and `μ₂`
    - `μ₁ : (a₁ a₂ ... aₖ : A) → A`
    - `μ₂ : (b₁ b₂ ... bₖ : B) → B`

`f` is a homomorphism *between* two set equipped with *the same algebraic structure* if it *preserves* structure of *operation* (not algebraic structure) `μ` if:

    - `f (μ₁ a₁ a₂ ... aₖ) = μ₂ (f a₁) (f a₂) (f a₃) ... (f aₖ)`

And if algebraic structure may have *more than one* operation, and a homomorphism is required to *preserve each operation*.
 
Now, I realized my mistakes as bellow:

> I think homomorphism, as definition, is a structure-preserving map between *two algebraic structures* of the *same type*, so:

  - I realized that homomorphism *preserve structure* of *operation*s. I *thought* it was about preserve structure of the domain. 
  - I did mention that it's *structure-preserving map between two algebraic structure*, but I understood it as *(structure-preserving map) (between two algebraic structures)*. It was like there are *normal mapping* that does not preserve structure *between two algebraic structures*, and homomorphism are the special one that does preserve structure.
  - I thought it preserve *algebraic structure* of the domain

>  Its domain and codomain *must* be the *same* algebraic structure, such as from `Monoid → Monoid`, `Ring → Ring`.

I thought the domain and codomain of the homomorphism are *two algebraic structures* (it mean both the sets and the structure equipped to the sets). Hard to explain, but I thought of algebraic structure is object in category and homomorphism is morphism in that category. For example: there is category where Monoids are object, and there are morphisms between monoid. I thought of them are homomorphism. Now I realized that, although the morphisms between monoid in category I mentioned above related to homomorphism concept, they are not homomorphism

>  - Actually, I think laws preserving is property of homomorphism. Although, logically it equals to *thus something that doesn’t preserve laws couldn’t be a homomorphism.* 
  
This was because I thought homomorphism as above, are between two algebraic structures (the set and its structure), and homomorphism preserve structure of the domain.

>  - However, I *think* *preserve laws* is *consequence* of defining the homomorphism between the same algebraic structure and preserves operation. I don't know if there is evidence for this, it's just my intuitive.

*between the same algebraic structure* - Yeah, the same as above.
   
I think my most important mistakes that I realized is that does not preserves *algebraic structures* and it's domain and codomain are only the sets, not the sets with their structures.

Thank you so much for helping me realized my missunderstanding in homomorphism. Please let me know if there's anything else that I may missunderstand.

Many thanks,

Thong
