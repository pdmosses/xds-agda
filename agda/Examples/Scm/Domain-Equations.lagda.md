# Domain Equations

The domains for *Scm* are somewhat simpler than for the denotational semantics in
the Scheme standards [(Scheme)],
but still involve all our postulated domain constructors.
Using definitional equations `D = E` instead of postulated bijections `D ≅ E`
for non-recursive collections of domains
avoids the need for the functions `fold` and `unfold` in definitions of denotations.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Examples.Scm.Domain-Equations where
--"hide"

  open import Examples.Scm.Abstract-Syntax
  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat
  open import Notation.Flat.Booleans
  open import Notation.Flat.Naturals
  open import Notation.Sums
  open import Notation.Products
  open import Notation.Products.Sequences
--"/hide"

  postulate Loc : Set
  𝐋  =  Loc +⊥                -- locations
  𝐍  =  Nat⊥                  -- natural numbers
  𝐓  =  Bool⊥                 -- booleans
  𝐑  =  Int +⊥                -- numbers
  𝐏  =  𝐋 × 𝐋                 -- pairs
  𝐔  =  Ide →ˢ 𝐋              -- environments
  data Misc : Set where null unallocated undefined unspecified : Misc
  𝐌  =  Misc +⊥               -- miscellaneous
  postulate 𝐄 : Domain        -- expressed values
  𝐒  =  𝐋 →ᶜ 𝐄                -- stores
  postulate 𝐀 : Domain        -- answers
  𝐂  =  𝐒 →ᶜ 𝐀                -- command continuations
  𝐅  =  𝐄 ⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂  -- procedure values
```
The published denotational semantics of *Scm* [(Mosses2025CSE)] defines the domain $𝐄$
of expression values by the equation $𝐄 = 𝐓 + 𝐑 + 𝐏 + 𝐌 + 𝐅$,
and the domain $𝐅$ of procedure values by $𝐅 = 𝐄^* \to (𝐄 \to 𝐂) \to 𝐂$.
Mutually recursive groups of domain equations have well-defined solutions,
but in Agda, defining both the corresponding domains `𝐄` and `𝐅` by equations
would cause the type checker to diverge.
Postulating one (or both) of these domains avoids divergence;
postulating `𝐄` also has the benefit that the embeddings and projections for its summands
subsume the bijection between `𝐄` and its intended structure.

The following postulates instantiate the notation used in denotational semantics for [sum domains]:
injection (`δ in⊥ 𝐄`),
inspection (`ε ∈⊥ D`),
and projection (`ε |⊥ D`) for each summand `D` of `𝐄`.
```agda
  postulate instance
    E+=T  : 𝐄 ≳ 1 ↦ 𝐓
    E+=R  : 𝐄 ≳ 2 ↦ 𝐑
    E+=P  : 𝐄 ≳ 3 ↦ 𝐏
    E+=M  : 𝐄 ≳ 4 ↦ 𝐌
    E+=F  : 𝐄 ≳ 5 ↦ 𝐅
```
(where the numerical indices and order of the summand declarations are arbitrary).
```agda
--"hide"

  postulate instance
    eqL   : Eq Loc
    eqM   : Eq Misc
    eqR   : Eq Int

  variable
    α : ⟪ 𝐋 ⟫;  ρ : ⟪ 𝐔 ⟫;  μ  : ⟪ 𝐌 ⟫;    ϵ : ⟪ 𝐄 ⟫
    σ : ⟪ 𝐒 ⟫;  θ : ⟪ 𝐂 ⟫;  ϵ⋆ : ⟪ 𝐄 ⋆ ⟫;   φ : ⟪ 𝐅 ⟫;  κ : ⟪ 𝐄 →ᶜ 𝐂 ⟫
--"/hide"
```

[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Scheme)]: https://standards.scheme.org
[sum domains]: ../../Notation/Sums.md#sum-domains
