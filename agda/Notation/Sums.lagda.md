# Sum Domains

The separated sum `D + E` of two domains corresponds to lifting the disjoint
union of their carrier sets. 
The following operations can be used directly for binary sums,
and iterated for domains with more than two summands.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation.Sums where
--"hide"

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat.Booleans
  
--"/hide"
  postulate
    _+_    : Domain → Domain → Domain   -- D + E is separated sum
    inj₁   : ⟪ D →ᶜ (D + E) ⟫           -- inj₁ δ is injection from D
    inj₂   : ⟪ E →ᶜ (D + E) ⟫           -- inj₂ ε is injection from E
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫
    -- [ φ , ψ ] applies φ to arguments in D, and ψ to arguments in E
```
Conventional denotational definitions of programming languages
(e.g., the *Scheme* semantics [(Scheme)])
use domain names instead of numerical indices in operations associated with separated sums.
The inherently *dependent* types of the Agda embedding of these operations are as follows.
```agda
  open import Agda.Builtin.Nat using (Nat)
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E injection
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D  projection
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D  inspection
```
The operations are defined only for `D` and `E`
where an instance of type `E ≳ n ↦ D` is declared for some\ `n`.
Instead of defining the summands `D` of a separated sum
domain `E` by an equation `E = ... + D + ...`, the
domain `E` is merely *postulated*, and each summand is
declared separately by `instance _ : E ≳ n ↦ D` (where\ `n`
should be a different natural number for each summand, but is otherwise arbitrary).

[(Scheme)]: https://standards.scheme.org
