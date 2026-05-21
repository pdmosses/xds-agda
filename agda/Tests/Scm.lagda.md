# Scm Tests

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests.Scm where
--"hide"
open import Examples.Scm.Abstract-Syntax
open import Examples.Scm.Domain-Equations
open import Examples.Scm.Auxiliary-Functions
open import Examples.Scm.Semantic-Functions

open import Notation
open Notation.Flat
open Notation.Flat.Booleans
open Notation.Sums
open import Properties
open Properties.Flat
open Properties.Flat.Booleans
open Properties.Sums
--"/hide"

check-sum : {β : ⟪ 𝐓 ⟫} → (β in⊥ 𝐄) ∈⊥ 𝐓 ≡ ↑ true
check-sum = refl
```