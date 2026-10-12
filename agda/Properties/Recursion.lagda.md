# Recursive Domains

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Properties.Recursion where
--"hide"
  open import Notation.Domains
  open import Notation.Recursion public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

--"/hide"
  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}

```
The property `fold (unfold d) ≡ d` could be added,
but it is not needed for the current illustrative tests.
