# Recursive Domains

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Properties.Recursion where
  open import Notation.Domains
  open import Notation.Recursion public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}

```
The property `fold (unfold d) ≡ d` could be added,
but it is not needed for the current illustrative tests.
