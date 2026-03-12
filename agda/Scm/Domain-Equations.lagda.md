# Domain Equations

The domains for Scm are significantly simpler than for the denotational
semantics of the full Scheme language, but still involve almost all of
the domain constructors formalised in the `Notation` module.

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Scm.Domain-Equations where

  open import Scm.Abstract-Syntax using (Ide; Int)
  import Notation
  open Notation.Domains using (Domain; ⟪_⟫)
  open Notation.Functions using (_→ᶜ_; _→ˢ_)
  open Notation.Flat using (_+⊥)
  open Notation.Flat.Booleans using (Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥)
  open Notation.Sums using (_≳_↦_)
  open Notation.Products using (_×_)
  open Notation.Products.Sequences using (_⋆)
```

Agda allows non-recursive type definitions to be written simply as equations.
This avoids the need for the `fold` and `unfold` functions used in connection
with postulated domain equivalences `D ≡ E`.

```agda
  postulate Loc : Set
  𝐋  =  Loc +⊥                -- locations
  𝐍  =  Nat⊥                  -- natural numbers
  𝐓  =  Bool⊥                 -- booleans
  𝐑  =  Int +⊥                -- numbers
  𝐏  =  𝐋 × 𝐋                 -- pairs
  𝐔  =  Ide →ˢ 𝐋              -- environments
  data Misc : Set where
    null unallocated undefined unspecified : Misc
  𝐌  =  Misc +⊥               -- miscellaneous
```

The remaining domains are mutually recursive: the domain `𝐄` is supposed to be
the sum `𝐓 ⊕ 𝐑 ⊕ 𝐏 ⊕ 𝐌 ⊕ 𝐅`, where `𝐅` is a domain involving `𝐄` (directly, and
indirectly through `𝐄 ⋆` and `𝐂`). In conventional denotational semantics,
mutually recursive groups of domain equations have well-defined solutions.
However, defining both `𝐄` and `𝐅` by type equations on Agda would prevent the
type checker from terminating. Postulating one (or both) of these domains
avoids non-termination; postulating `𝐄` has the advantage that the embeddings
and projections for its summands incorporate the bijection between `𝐄` and its
intended structure. 

```agda
  postulate 𝐄 : Domain        -- expressed values
  𝐒  =  𝐋 →ᶜ 𝐄                -- stores
  postulate 𝐀 : Domain        -- answers
  𝐂  =  𝐒 →ᶜ 𝐀                -- command continuations
  𝐅  =  𝐄 ⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂  -- procedure values
```

The following postulates instantiate the emebdding, inspection, and projection
operations for each summand of `𝐄`.

```agda
  postulate instance
    E+=T  : 𝐄 ≳ 1 ↦ 𝐓
    E+=R  : 𝐄 ≳ 2 ↦ 𝐑
    E+=P  : 𝐄 ≳ 3 ↦ 𝐏
    E+=M  : 𝐄 ≳ 4 ↦ 𝐌
    E+=F  : 𝐄 ≳ 5 ↦ 𝐅
```

Conventional denotational definitions declare Greek lowercase letters as
(meta-)variables ranging over specified domains, allowing subscripts and primes
to be added. The following variable declarations in Agda look similar, but
they appear to be ignored by the type checker.

```agda
  variable
    α : ⟪ 𝐋 ⟫;  ρ : ⟪ 𝐔 ⟫;  μ  : ⟪ 𝐌 ⟫;   ϵ : ⟪ 𝐄 ⟫
    σ : ⟪ 𝐒 ⟫;  θ : ⟪ 𝐂 ⟫;  ϵ⋆ : ⟪ 𝐄 ⋆ ⟫;  φ : ⟪ 𝐅 ⟫
```