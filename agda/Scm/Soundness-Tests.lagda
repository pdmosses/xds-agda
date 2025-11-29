\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Soundness-Tests where

open import Scm.Notation
open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
open import Scm.Auxiliary-Functions
open import Scm.Semantic-Functions

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

postulate
  fix-fix : (f : ⟪ D →ᶜ D ⟫) → fix f ≡ f (fix f)

\end{code}