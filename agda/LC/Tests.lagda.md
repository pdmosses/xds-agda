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
  ⟦ (ƛ x 1 ␣ val x 1) ␣ (val x 42) ⟧ ≡ ⟦ val x 42 ⟧
check-id = refl

-- (λx1.x42)x0 = x42
check-const :
  ⟦ (ƛ x 1 ␣ val x 42) ␣ (val x 0) ⟧ ≡ ⟦ val x 42 ⟧
check-const = refl 

-- -- (λx0.x0 x0)(λx0.x0 x0) = ...
-- -- check-divergence :
-- --   ⟦ (ƛ x 0 ␣ ((val x 0) ␣ (val x 0))) ␣
-- --     (ƛ x 0 ␣ ((val x 0) ␣ (val x 0))) ⟧
-- --   ≡ ⟦ val x 42 ⟧
-- -- check-divergence = refl 

-- (λx1.x42)((λx0.x0 x0)(λx0.x0 x0)) = x42
check-convergence :
  ⟦ (ƛ x 1 ␣ val x 42) ␣ ((ƛ x 0 ␣ ((val x 0) ␣ (val x 0))) ␣
                          (ƛ x 0 ␣ ((val x 0) ␣ (val x 0)))) ⟧
         ≡ ⟦ val x 42 ⟧
check-convergence = refl 

-- (λx1.x1)(λx1.x42) = λx2.x42
check-abs :
  ⟦ (ƛ x 1 ␣ val x 1) ␣ (ƛ x 1 ␣ val x 42) ⟧
                     ≡ ⟦ ƛ x 2 ␣ val x 42 ⟧
check-abs = refl

-- (λx1.(λx42.x1)x2)x42 = x42
check-free :
  ⟦ (ƛ x 1 ␣ ((ƛ x 42 ␣ val x 1) ␣ (val x 2))) ␣ (val x 42) ⟧
                                              ≡ ⟦ val x 42 ⟧
check-free = refl
```