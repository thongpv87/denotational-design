# Foundation

## Type theory vs set theory

### Equality

  : Propositional equality
    - `equal : (a b : A) → a ═ₐ b `
    - This has form of a propostion
    - if `a ═ₐ b`  is inhabited, we say that `a` equal to `b`
    - We can *disprove* or *assume* an equality in a hypothesis
  : Definitional equality
    - `a ≡ b : A` or `a ≡ b`
    - existing at the same level as the judgment `x : A`
    - it's helpful to think of this as meaning *equal by definition*
    - for example: `f(x) = x²` then `f 3 ≡ 3²`
    - It does not make sense to *negate* or *assume* an equality by definition
      - We can not say: "if x is equal to y by definition, then z is not equal to w by definition"


## ZFC
### Axiom
#### Axiom of extensionality
Two set are equal (are the same set) if they have the same elements

```
∀ (x y : Set) → (∀ z → z ∈ x ⇔ z ∈ y) → x ═ y
```

The converse of this axiom follows from the substitution property of equality.

If the background logic[definition needed] does not include equality `═`, `x═y` may be defined as an abbreviation for the following formula: 

```
  ∀ z [ z ∈ x ⇔ z ∈ y ] ∧ ∀ w [ x ∈ w ⇔ y ∈ w ]
```

which says that if x x and y y have the same elements, then they belong to the same sets

My comment: this is similar to extensionality of function


# Content
- Lost in set theory, type theory, homotopy type theory docs

## Misconception between type theory vs set theory
  - Differences between `x : A` and `x ∈ A`
    - In set theory, elements can belong to many set
    - In type theory, elements can only belong to one type
    - `x : A` is a judgment (static), `x ∈ A` is a proposition (dynamic)
  - Operations on Set: `∪` `∩` ͏ `⊆` `⊂`. They are not type operations
    - Operations like `∪` `∩` are intensional
    - Their behavior depends on intensional properties of object
    - `{a, b} ≃ {c , d}` but `{a , b} ∪ {a} ≄ {c , d} ∪ {a}`
  - Type operations: `A → B`, `A × B` `A ⊎ B`
    - They are extensional operations
    - Their behavior is independent on the choice of interpretation 
    - `{a, b} ≃ {c , d}` and `{a , b} ⊎ {a} ≄ {c , d} ⊎ {a}`
    - In *Intensional Type Theory*, all operations are extensional
      - In *Homotopy Type theory*, isomorphic type are equal (univalence principle)
  - Function notation in set theory is set of pairs, it does not need to be computable. In type theory is primitive concept
    - Function in type theory that doesn't *function* should'nt be called a function (halting problem)
  - Proposition as type
    - In set theory, we need to use predicate logic to express axiom
    - In type theory, it can define axiom on it own

## Concepts in type theory
- Types
  - `Π` type: can represent `A → B` `A × B`
  - `Σ` type: can represent `A × B`, `A ⨄ B`
  - *Inductive types*: `Bool` `ℕ`
- It's useful to think propostion as evidence in type theory than propostion and truth in classical logic
- In type theory, there is no evidence for:
  - Excluded middle: `A ∨ ¬ A`
  - Indirect proof: `¬¬A → A`
  - But there is evidence for `¬¬(A ∨ ¬ A)`
- Predicate logic relations are primitive concept but in Type theory, we use function `A → B → Prop` to represent relation between `A` and `B`
- Only one proof for a propostion
  - This can not be proved?
  - Uniqueless rule?
  - Extensional properties rule?

     



