# Semantic Functions

The semantic equations below correspond closely to those found in textbooks on denotational semantics
(e.g., [(Reynolds1998TPL)]).
In larger conventional definitions, `fold` and `unfold` are usually left implicit,
but Agda does not support this.
```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC.Semantic-Functions where

open import Examples.LC.Abstract-Syntax
open import Examples.LC.Domain-Equations
open import Notation

⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
⟦ var v ⟧ ρ        = ρ v
⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
```

[(Reynolds1998TPL)]: https://doi.org/10.1017/CBO9780511626364