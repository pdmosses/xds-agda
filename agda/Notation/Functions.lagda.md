# Function Domains

The conventional notation in denotational definitions for the domain of
continuous functions from $D$ to $E$ is $D \to E$ or $[D \to E]$.
However, Agda reserves the notation `D → E` for the type of *all* (total)
functions from type `D` to type `E`;
here, we use the notation `D →ᶜ E` for embedding continuous function domains:
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}
--"/hide"

module Notation.Functions where
--"hide"
  open import Notation.Domains
  open import Agda.Builtin.Equality public using (_≡_)
  open import Agda.Builtin.Equality.Rewrite using ()
--"/hide"
  postulate _→ᶜ_ : Domain → Domain → Domain
--"hide"
  -- D →ᶜ E is the domain of continuous functions from D to E
  infixr 0 _→ᶜ_
--"/hide"
```
Both λ-abstraction and application preserve continuity.
In conventional denotational semantics,
functions between domains are defined using λ-abstraction and application
from primitive continuous functions associated with specific domain constructors,
so they are *automatically* continuous.
This motivates treating the carrier `⟪ D →ᶜ E ⟫` of the embedding of a function domain
as a type of continuous functions.
(*Proving* functions defined in λ-notation to be continuous in Agda
requires pairing each λ-abstraction with an explicit proof of its continuity,
which is quite impractical – especially when embedding denotations defined in
continuation-passing style.)

However, to support type-checking the *direct* embedding of λ-notation
from conventional denotational definitions in Agda,
it appears to be necessary to *rewrite* the carrier types of function domains
to ordinary function types:
```agda
  postulate dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
```
Similarly, the notation `A →ˢ D` is the embedding of the domain of all functions
from an ordinary type `A` to a domain `D` (which are trivially continuous,
ordered pointwise):
```agda
  postulate _→ˢ_ : Set → Domain → Domain
--"hide"
  -- A →ˢ D is the domain of all functions from A to D
  infixr 0 _→ˢ_
--"/hide"
  postulate set-cts  : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
```
Embeddings of *endofunctions* `φ` on a domain `D` should always have
fixed points `fix φ`, with `fix` itself also being continuous:
```agda
  postulate fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
```
