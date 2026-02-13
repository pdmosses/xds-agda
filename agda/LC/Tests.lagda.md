# Tests

```agda
{-# OPTIONS --rewriting --confluence-check #-}
module LC.Tests where

open import LC.Definitions
open Abstract-Syntax
open Domain-Equations
open Semantic-Functions

open import Properties

-- (λx1.x1)x42 = x42
check-id :
  ⟦ ⦅ ⦅λ x 1 ␣ val x 1 ⦆ ␣ val x 42 ⦆ ⟧ ≡ ⟦ val x 42 ⟧
check-id = refl

-- (λx1.x42)x0 = x42
check-const :
  ⟦ ⦅ ⦅λ x 1 ␣ val x 42 ⦆ ␣ val x 0 ⦆ ⟧ ≡ ⟦ val x 42 ⟧
check-const = refl 

-- (λx0.x0 x0)(λx0.x0 x0) = ...
-- check-divergence :
--   ⟦ ⦅ ⦅λ x 0 ␣ ⦅ val x 0 ␣ val x 0 ⦆ ⦆ ␣
--       ⦅λ x 0 ␣ ⦅ val x 0 ␣ val x 0 ⦆ ⦆ ⦆ ⟧
--   ≡ ⟦ val x 42 ⟧
-- check-divergence = refl 

-- (λx1.x42)((λx0.x0 x0)(λx0.x0 x0)) = x42
check-convergence :
  ⟦ ⦅ ⦅λ x 1 ␣ val x 42 ⦆ ␣ 
      ⦅ ⦅λ x 0 ␣ ⦅ val x 0 ␣ val x 0 ⦆ ⦆ ␣
        ⦅λ x 0 ␣ ⦅ val x 0 ␣ val x 0 ⦆ ⦆ ⦆ ⦆ ⟧
         ≡ ⟦ val x 42 ⟧
check-convergence = refl

-- (λx1.x1)(λx1.x42) = λx2.x42
check-abs :
  ⟦ ⦅ ⦅λ x 1 ␣ val x 1 ⦆ ␣ ⦅λ x 1 ␣ val x 42 ⦆ ⦆ ⟧
                        ≡ ⟦ ⦅λ x 1 ␣ val x 42 ⦆ ⟧
check-abs = refl

-- (λx1.(λx42.x1)x2)x42 = x42
check-free :
  ⟦ ⦅ ⦅λ x 1 ␣ ⦅ ⦅λ x 42 ␣ val x 1 ⦆ ␣ val x 2 ⦆ ⦆ ␣ val x 42 ⦆ ⟧
                                                    ≡ ⟦ val x 42 ⟧
check-free = refl
```