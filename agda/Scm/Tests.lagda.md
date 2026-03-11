# Tests

```agda
{-# OPTIONS --rewriting --confluence-check #-}
module Scm.Tests where

open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
open import Scm.Auxiliary-Functions
open import Scm.Semantic-Functions

open import Notation
open Notation.Flat
open Notation.Flat.Booleans
open Notation.Sums

-- postulate instance
--   E+=T2  : 𝐄 ≳ 2 ↦ 𝐓

check-sum : {β : ⟪ 𝐓 ⟫} → (β in⊥ 𝐄) ∈⊥ 𝐓 ≡ ↑ true
check-sum = refl
```