# Tuple Domains

The domain `D ^ n` of `n`-tuples of elements of a domain `D` is conventionally
written $D^n$, but Agda does not support the use of variables as superscripts.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Products.Tuples where
--"hide"

  open import Notation.Domains
  open import Notation.Products
--"/hide"
  open import Agda.Builtin.Nat public using (Nat; suc)

  _^_ : Domain → Nat → Domain  -- D ^ n is the domain of n-tuples (n ≥ 0)
  D ^ 0            = 𝟙 
  D ^ 1            = D
  D ^ suc (suc n)  = D × (D ^ suc n)
```