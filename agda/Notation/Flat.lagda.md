# Flat Domains

Lifting an ordinary set $A$ by adding a $\bot$ element gives a flat domain,
usually written $A_\bot$.
Our Agda embedding postulates a corresponding domain constructor `A +⊥`,
together with a function `↑` for injecting elements of `A` into `A +⊥`,
and an operator `f ♯` for extending functions on `A` to arguments in `A +⊥`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Flat where
--"hide"
  
  open import Notation.Domains
  open import Notation.Functions
  
--"/hide"
  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
```
