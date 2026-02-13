# Properties

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
module Properties where
open import Agda.Builtin.Equality using (_≡_; refl) public
open import Agda.Builtin.Equality.Rewrite using ()
open import Data.Nat.Base renaming (ℕ to Nat) using (_≡ᵇ_) public
import Notation
open Notation.Domains
open Notation.Functions
variable A B C : Set
```

## Function domains

```agda
module Functions where
  open Notation.Functions
  postulate
    fix-fix : (f : ⟪ D →ᶜ D ⟫) → fix f ≡ f (fix f)
  {-# REWRITE fix-fix #-} 
```

## Recursive domains

```agda
module Recursion where
  open Notation.Recursion
  postulate
    unfold-fold-elim : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE unfold-fold-elim #-}
```

## Flat domains

```agda
module Flat where
  open Notation.Flat using (↑; _♯) public
  postulate
    elim-♯-↑  : (f : ⟪ A →ˢ D ⟫) (a : A) →  (f ♯) (↑ a)  ≡ f a
    elim-♯-⊥  : (f : ⟪ A →ˢ D ⟫) →          (f ♯) ⊥       ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-} 
```

### Booleans

```agda
  module Booleans where
    open Notation.Flat.Booleans
    variable δ₁ δ₂ : ⟪ D ⟫
    postulate
      true-cond    : (↑ true ⟶ δ₁ , δ₂)   ≡ δ₁
      false-cond   : (↑ false ⟶ δ₁ , δ₂)  ≡ δ₂
      bottom-cond  : (⊥ ⟶ δ₁ , δ₂)        ≡ ⊥
    {-# REWRITE true-cond false-cond #-} 
```

### Naturals

```agda
  module Naturals where
    open Notation.Flat.Booleans
    open Notation.Flat.Naturals
    variable n₁ n₂ : Nat
    postulate
      ==⊥≡ᵇ : (↑ n₁ ==⊥ ↑ n₂) ≡ ↑ (n₁ ≡ᵇ n₂)
    {-# REWRITE ==⊥≡ᵇ #-} 
```

## Sum domains

## Product domains

### Tuples

### Sequences

## Updates