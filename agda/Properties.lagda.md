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
    apply-fix : {f : ⟪ D →ᶜ D ⟫} → fix f ≡ f (fix f)
  {-# REWRITE apply-fix #-} 
```

## Recursive domains

```agda
module Recursion where
  open Notation.Recursion
  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}
```

## Flat domains

```agda
module Flat where
  open Notation.Flat using (↑; _♯) public
  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-} 
```

### Booleans

```agda
  module Booleans where
    open Notation.Flat.Booleans
    variable δ₁ δ₂ : ⟪ D ⟫
    postulate
      elim-true-⟶    : (↑ true ⟶ δ₁ , δ₂)   ≡ δ₁
      elim-false-⟶   : (↑ false ⟶ δ₁ , δ₂)  ≡ δ₂
      elim-bottom-⟶  : (⊥ ⟶ δ₁ , δ₂)        ≡ ⊥
    {-# REWRITE elim-true-⟶ elim-false-⟶ #-} 
```

### Naturals

```agda
  module Naturals where
    open Notation.Flat.Booleans
    open Notation.Flat.Naturals
    variable n₁ n₂ : Nat
    postulate
      elim-==⊥ : (↑ n₁ ==⊥ ↑ n₂) ≡ ↑ (n₁ ≡ᵇ n₂)
    {-# REWRITE elim-==⊥ #-} 
```

## Sum domains

```agda
module Sums where
  open Notation.Flat
  open Notation.Flat.Booleans
  open Notation.Sums
  open import Relation.Binary.PropositionalEquality.Core using (_≢_)
  variable D′ : Domain; n′ : Nat
  postulate
    elim-∈⊥    :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  (δ in⊥ E) ∈⊥ D′ ≡ ↑ (n ≡ᵇ n′)
    elim-|⊥    :  {{_ : E ≳ n ↦ D}} → (δ : ⟪ D ⟫) → (δ in⊥ E) |⊥ D ≡ δ
    elim-∈⊥-⊥  :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  {n ≢ n′} → (δ in⊥ E) |⊥ D′ ≡ ⊥
  {-# REWRITE elim-∈⊥ elim-|⊥ #-} 
```

Note that `elim-∈⊥` does not hold when `E` is a coalesced sum.

## Product domains

### Tuples

### Sequences

## Updates