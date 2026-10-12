# Function Domains

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Properties.Functions where
--"hide"
  open import Notation.Domains
  open import Notation.Functions public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

--"/hide"
  postulate
    apply-fix : {φ : ⟪ D →ᶜ D ⟫} → fix φ ≡ φ (fix φ) -- apply-fix{φ} unfolds fix φ once
  {-# REWRITE apply-fix #-}
```
The rewrite rule `apply-fix` does not cause the type-checker to diverge,
despite the obvious non-termination.
Agda's type checker uses *weak head evaluation*:
it only unfolds expressions to the point where the top-level constructor becomes visible.
In particular, it will not evaluate under a λ-abstraction
unless it is being compared to another λ-abstraction and the bodies are not syntactically equal.
