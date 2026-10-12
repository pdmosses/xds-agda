# Domain Equations

Simply defining `D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda type-checker.
Instead, we postulate the domain `D∞`, together with a bijection `D∞ ≅ (D∞ →ᶜ D∞)`.
This declares the operations
`unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫` and `fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞ ⟫`
associated with [recursive domains].
```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Examples.LC.Domain-Equations where

  open import Examples.LC.Abstract-Syntax
  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Recursion
  open import Notation.Flat.Booleans
  open import Notation.Flat.Naturals
  open import Notation.Updates
  open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public

  postulate
    D∞ : Domain                      -- corresponds to Scott's domain 
    instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
  variable δ : ⟪ D∞ ⟫

  Env = Var →ˢ D∞                    -- environments
  variable ρ : ⟪ Env ⟫
```
Use of the conventional notation `ρ [ δ / v ]` for updating an environment `ρ` to map `v` to `δ`
requires an equality test for variables.
```agda
  _==ⱽ_ : Var → Var → Bool
  (x n ==ⱽ x n′) = (n ==ᴺ n′)
  instance eqVar : Eq Var
  _==_ {{eqVar}} = _==ⱽ_
```

[recursive domains]: ../../Notation/Recursion.md#recursive-domains
