# Untyped Lambda-Calculus Tests

The following tests check that the denotations of some simple untyped $\lambda$-expressions
in the abstract syntax of the [LC language] compute the expected values. In the absence of
atomic values in this language, we regard free variables as values, and apply denotations
to an arbitrary environment `ρ`.

All the `refl` proofs of the tests implicitly use the rewrite rule postulated as
a [property of recursive domains] to eliminate compositions of `unfold` and `fold`.

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests.LC where
--"hide"
  open import Notation.Domains
  open import Notation.Functions

  open import Examples.LC.Abstract-Syntax
  open import Examples.LC.Domain-Equations
  open import Examples.LC.Semantic-Functions

  open import Properties.Flat.Booleans
  open import Properties.Updates
  open import Properties.Recursion
--"/hide"
```

The following trivial abbreviations improve the readbility of AST terms in the tests:
```agda
  a = x 0
  b = x 1
  c = x 2
```
Due to potential non-injectivity of the postulated operation `⟪_⟫`,
the definition of `_[_/_]` needs to be instantiated at `D∞`
for the type-checker to resolve the `lookup-id` test:

```agda
  _[_/_]D∞ : {{Eq A}} → ⟪ (A →ˢ D∞) →ᶜ D∞ →ᶜ A →ˢ (A →ˢ D∞) ⟫
  ρ [ δ / a ]D∞ = λ a′ → if a == a′ then δ else ρ a′

  lookup-id :
    ⟦ var a ⟧ (ρ [ δ / a ]D∞) ≡ δ
  lookup-id = refl

  app-id :
    ⟦ ⦅ ⦅λ a ␣ var a ⦆ ␣ var b ⦆ ⟧ ρ ≡ ρ b
  app-id = refl

  app-k :
    ⟦ ⦅ ⦅λ a ␣ var b ⦆ ␣ var c ⦆ ⟧ ρ ≡ ρ b
  app-k = refl

```
The following test involves the diverging evaluation of a λ-abstraction to
itself. It is commented-out, to avoid nontermination of the Agda type-checker.
```agda
  -- app-id-to-divergence :
  --   ⟦  ⦅  ⦅λ a ␣ var a ⦆ ␣
  --         ⦅ ⦅λ c ␣ ⦅ var c ␣ var c ⦆ ⦆ ␣ ⦅λ c ␣ ⦅ var c ␣ var c ⦆ ⦆ ⦆ ⦆ ⟧ ρ ≡ ρ b
  -- app-id-to-divergence = refl

```
The following test illustrates that application of a λ-abstraction can
terminate when evaluation of its argument would diverge.
```agda
  app-k-to-divergence :
    ⟦  ⦅  ⦅λ a ␣ var b ⦆ ␣
          ⦅ ⦅λ c ␣ ⦅ var c ␣ var c ⦆ ⦆ ␣ ⦅λ c ␣ ⦅ var c ␣ var c ⦆ ⦆ ⦆ ⦆ ⟧ ρ ≡ ρ b
  app-k-to-divergence = refl

```
This final illustrative test shows that the free variable `a` is not captured
by the λ-abstraction on `a`.
```agda
  app-k-abs :
    ⟦ ⦅ ⦅λ b ␣ ⦅ ⦅λ a ␣ var b ⦆ ␣ var c ⦆ ⦆ ␣ var a ⦆ ⟧ ρ ≡ ρ a
  app-k-abs = refl
```

A reviewer pointed out that the only interpretation of `⟪ D∞ ⟫` in Agda could be a singleton type,
in which case one should expect many equalities to hold.
However, when the Agda proof of an equality is simply by `refl`, it cannot use such reasoning
about cardinality.

[LC language]: ../Examples/LC/index.md#untyped-lambda-calculus
[property of recursive domains]: ../Properties/Recursion.md#recursive-domains
