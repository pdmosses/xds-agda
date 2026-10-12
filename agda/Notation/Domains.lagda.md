# Domains

Domains are embedded in Agda as elements of the  type `Domain`.
A domain `D` is not itself a type, but it has a *carrier* type `⟪ D ⟫ : Set`,
which always contains an element `⊥{D}`
(written `⊥` when Agda can infer `D`).
```agda
module Notation.Domains where
  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the carrier type of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the 'bottom' element of D
    𝟙 : Domain                -- 𝟙 is a unit domain
  variable A B C : Set; D E F : Domain
```
Some previous papers on embedding denotational semantics in Agda
[(Mosses2025CDS)]\ [(Mosses2025CSE)]\ [(Mosses2025LAF)]
defined domains to be types: `Domain = Set`.
However, postulating `⊥ : D` for all `D : Domain` was then
*inconsistent* with the existence of an empty type in Agda.
Postulating `Domain : Set` avoids that inconsistency.

The notation for domains postulated here supports *type-checking*
embeddings of denotational semantics in Agda such as those in the
illustrative examples.
It does *not* define or constrain the *mathematical structure* of domains,
nor the algebraic and universal properties of the associated functions.

[(Mosses2025CDS)]: https://doi.org/10.1145/3759537.3762694
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Mosses2025LAF)]: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper11.pdf