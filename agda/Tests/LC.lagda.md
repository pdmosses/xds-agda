# LC Tests

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Tests.LC where

open import Notation
open import Properties
open import Examples.LC.Abstract-Syntax
open import Examples.LC.Domain-Equations
open import Examples.LC.Semantic-Functions

check-id : -- (λx1.x1)x42 = x42
  ⟦ ⦅ ⦅λ x 1 ␣ var x 1 ⦆ ␣ var x 42 ⦆ ⟧ ≡ ⟦ var x 42 ⟧
check-id = refl

check-const : -- (λx1.x42)x0 = x42
  ⟦ ⦅ ⦅λ x 1 ␣ var x 42 ⦆ ␣ var x 0 ⦆ ⟧ ≡ ⟦ var x 42 ⟧
check-const = refl 

-- check-divergence : -- (λx0.x0 x0)(λx0.x0 x0) = ...
--   ⟦ ⦅ ⦅λ x 0 ␣ ⦅ var x 0 ␣ var x 0 ⦆ ⦆ ␣ ⦅λ x 0 ␣ ⦅ var x 0 ␣ var x 0 ⦆ ⦆ ⦆ ⟧ ≡ ⟦ var x 42 ⟧
-- check-divergence = refl -- Agda type-checker diverges

check-convergence : -- (λx1.x42)((λx0.x0 x0)(λx0.x0 x0)) = x42
  ⟦  ⦅ ⦅λ x 1 ␣ var x 42 ⦆ ␣
     ⦅ ⦅λ x 0 ␣ ⦅ var x 0 ␣ var x 0 ⦆ ⦆ ␣ ⦅λ x 0 ␣ ⦅ var x 0 ␣ var x 0 ⦆ ⦆ ⦆ ⦆ ⟧ ≡ ⟦ var x 42 ⟧
check-convergence = refl

check-abs : -- (λx1.x1)(λx1.x42) = λx1.x42
  ⟦ ⦅ ⦅λ x 1 ␣ var x 1 ⦆ ␣ ⦅λ x 1 ␣ var x 42 ⦆ ⦆ ⟧ ≡ ⟦ ⦅λ x 1 ␣ var x 42 ⦆ ⟧
check-abs = refl

check-free : -- (λx1.(λx42.x1)x2)x42 = x42
  ⟦ ⦅ ⦅λ x 1 ␣ ⦅ ⦅λ x 42 ␣ var x 1 ⦆ ␣ var x 2 ⦆ ⦆ ␣ var x 42 ⦆ ⟧ ≡ ⟦ var x 42 ⟧
check-free = refl
```
A reviewer pointed out that the only interpretation of `⟪ D∞ ⟫` in Agda could be a singleton type,
so that one should expect many equalities to hold.
However, when the proof of an equality is simply by `refl`,
Agda's type-checker does not automatically use such reasoning.