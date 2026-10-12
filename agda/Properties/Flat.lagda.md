# Flat Domains

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Properties.Flat where
--"hide"
  open import Notation.Domains
  open import Notation.Flat public
  open import Agda.Builtin.Equality public using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite using ()

--"/hide"
  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ #-}

```
The `elim-♯-⊥` property could be added as a rewrite rule for automatic use in proofs
about an embedding of denotations that represent errors or failures by `⊥`.
When `⊥` only represents nontermination, rewrite rules that propagate it are irrelevant.
