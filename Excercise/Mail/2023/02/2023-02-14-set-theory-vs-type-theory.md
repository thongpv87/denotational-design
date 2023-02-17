Dear Conal,

I'm still working on implementing the injection/surjection definition, and I hope to have it finished within the next few days. I have been lost in the rabbit hole with set theory and type theory docs. I've learned a fews things and also realized that I had some misconception. 

Although I had heard of type theory before, I had never really studied it in depth. My understanding of types primarily came from my experience with programming languages like Haskell and Agda. I have been thinking in set theory while working with type theory in Agda and now I realized that while they have many correspondences, they are different. I haven't read too much about type theory because I'm afraid I may fall into another rabbit hole. *Please let me know if I'm mistaken about any of the following, or if there are any other common misconceptions you think I should be aware of*:

  - `x : A ≠ x ∈ A`
    - `x : A` in type theory is a *judgment*, state that `x` belong to type `A`. We can *not* negate it. In type theory, an element can only belong to one type.
    - `x ∈ A` in set theory is a *proposition*. In state that `x` belong to `A`, that may or may not true. We can assume or negate the proposition. In set theory, an element may belong to many set
  - Operations on Set (such as `∪` `∩` ͏ `⊆` `⊂`) behave different with their type operation correspondences
    - Operations on set are *intensional*, it behavior depends on intensional properties of object
      - `{a, b} ≃ {c , d}` but `{a , b} ∪ {a} ≄ {c , d} ∪ {a}`
    - Operation on type (such as `→` `×` `⊎`) are *extensional*, their behavior is *independent* on the choice of interpretation
      - `(a × b) ≃ (c × d)` and `(a × b) ⊎ a ≃ (c × d) ⊎ a`
  - Function in set theory is *set of pairs*, it does not need to be computable.
  - Function in type theory is primitive concept. A function that doesn't *function* shouldn't be called a function. 
    - I'm not sure if the function that doesn't function only related to the function that never return, or it also related to other kind of function in programming?
    - This make me think that most of function definition in main stream programming languages are not actually *function*
  - In set theory, we using predicate logic to express the axioms
  - In type theory, we can define it by using function type  to represent them. Ex: a relation between `A` and `B` is `A → B → Prop`
    - Is `Prop` has all inhabitants definitionally equal in all variants of type theory?
  - Structuralism: We can distinguish different encodings of natural numbers (or the same mathematical object) in set theory but not in type theory. 
    - I think this is very important property of type theory since it protect us from *abstraction leak*
    - I think this may also have many interesting relation in philosophy.

I've also discovered some knowledge in type theory:

  - *Aware* of [natural deduction](https://ncatlab.org/nlab/show/natural+deduction) frame work.
  - There are many kind of equality in type theory: *judgment equality*, *definitionally equal*, *propositionally equal*, *typal equality*,...
    - As my understanding, definitionally equal is best explain in [this](https://ncatlab.org/nlab/show/definitional+equality#idea). It's like they have defined by equivalent syntax.
    - Propositionally equal is `≡` that we use in Agda. It's just a *binary relation* that has *symmetric*, *reflective*, and *transitive* properties
    - I haven't read about other equalities
  - If Martin-Löf  type theory that has *propositionally equal* implies *definitionally equal*, it's an extensional type theory, otherwise it's an intensional type theory. Extensional Martin-Löf type theory does not have decidable type checking
    - Definitionally equal *implies* propositionally equal because of *reflective* property of propositionally equal
  - It's useful to think proposition as evidence in type theory rather than proposition and truth in classical logic


*I also have some questions about certain important concepts that I haven't fully understood yet*:

  - [Identity type](https://ncatlab.org/nlab/show/identity+type) it's definition is quite complicated to me to understand. What's relation/different between identity type and equality relation?
  - **There are different variants of Martin-Löf dependent type theory. How do we categorize the type theory that we are studying? What's main distinction from other variants**
    - Are we studying default type theory of Agda? Does that include Axiom K?
    - There are different [formal representation](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory#formal_presentations) of Martin-Löf dependent type theory, I wonder which is the representation for the type theory. What's the main distinction between these representations or they are just *isomorphism*?
    - I think the type theory can also be categorized as [*Intensional set level type theory*]( https://ncatlab.org/nlab/show/set-level+type+theory#idea). 
      - If that's true then I think one of the most important characteristic of the type theory as stated in the article is the distinction between definitionally equal and propositionally equal, and no two terms can be propositionally equal in more than one way (up to propositional equality).
    - Does it has any additional axiom?

Many thanks,

Thông
