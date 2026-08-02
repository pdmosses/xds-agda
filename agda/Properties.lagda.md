# Postulated Properties

The `Properties` module postulates basic properties of some of the operations
of the [postulated domain notation].
These properties are expected to hold in various categories of domains [(Abramsky1995DT)]
but they do *not* define the *mathematical structure* of domains.

The postulated properties support proofs that terms have identical denotations.
For example, some [illustrative tests] declare that the denotation of a function application
is equivalent to the denotation of a constant;
other tests declare that particular instances of renaming do not affect denotations.

When postulated properties are declared as *rewrite rules*,
Agda can use them *automatically* in proofs.
Agda also has an option to check that the declared rewrite rules form a confluent system.
Rewrite rules are safe to use with `Agda.Builtin.Equality` when that option is enabled.
Confluent but non-terminating rewrite rules cannot break consistency,
as shown by Cockx, Tabareau, and Winterhalter [(Cockx2021TRT)].

The rewrite rules declared below support *automatic* proof of identity for all the illustrative tests:
the proof terms are simply `refl` (i.e., reflexivity).
```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Properties where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 
import Notation
open Notation using (A; B; C)

module Domains where
  open Notation.Domains using (Domain; ⟪_⟫; ⊥; 𝟙; D; E; F) public
open Domains public

module Functions where
  open Notation.Functions using (_→ᶜ_; dom-cts; _→ˢ_; set-cts; fix) public
  postulate
    apply-fix : {φ : ⟪ D →ᶜ D ⟫} → fix φ ≡ φ (fix φ) -- apply-fix{φ} unfolds fix φ once
  {-# REWRITE apply-fix #-}
```
The rewrite rule `apply-fix` does not cause the type-checker to diverge,
despite the obvious non-termination.
Agda's type checker uses *weak head evaluation*:
it only unfolds expressions to the point where the top-level constructor becomes visible.
In particular, it will not evaluate under a λ-abstraction
unless it is being compared to another λ-abstraction and the bodies are not syntactically equal.
```agda
open Functions public

module Recursion where
  open Notation.Recursion using (_≅_; unfold; fold) public
  postulate
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}
```
A rule for `fold (unfold d) ≡ d` could be added, but it is not needed for the current illustrative tests.
```agda
module Flat where
  open Notation.Flat using (_+⊥; ↑; _♯) public

  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-}

  module Booleans where

    open Notation.Flat.Booleans using (Bool⊥; _⟶_,_; Eq; _==⊥_; eqBool) public

  module Naturals where

    open Notation.Flat.Naturals using (Nat⊥; eqNat) public
```
Removing any of the above rewrite rules breaks the proof in at least one of the illustrative tests.
In principle, all `refl` proof terms that rely on rewrite rules could be replaced by proofs
that apply the postulated properties to specified subterms.
However, we expect that it would be quite tedious to develop such proofs,
and reading them is unlikely to provide new insights.

The remaining postulated properties are for domains that are not used
in the semantics of the LC and PCF languages;
they will be needed when tests for equivalence of denotations of *Scm* expressions are added.

```agda
module Sums where
  open Notation.Sums using (_+_; inj₁; inj₂; [_,_]) public

  variable φ : ⟪ D →ᶜ F ⟫; ψ : ⟪ E →ᶜ F ⟫; δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-inj₁  :  [ φ , ψ ] (inj₁ δ)  ≡  φ δ
    elim-inj₂  :  [ φ , ψ ] (inj₂ ε)  ≡  ψ ε
    elim-[]-⊥  :  [ φ , ψ ] ⊥         ≡  ⊥
  {-# REWRITE elim-inj₁ elim-inj₂ #-} 

  open Notation.Sums using (n; _≳_↦_; _in⊥_; _|⊥_; _∈⊥_) public
  open Flat
  open Flat.Booleans
  open Flat.Naturals

  open import Relation.Binary.PropositionalEquality.Core using (_≢_)
  variable D′ : Domain; n′ : Nat
  postulate
    elim-∈⊥    :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  (δ in⊥ E) ∈⊥ D′ ≡ ↑ (n ==ᴺ n′)
    elim-|⊥    :  {{_ : E ≳ n ↦ D}} → (δ : ⟪ D ⟫) → (δ in⊥ E) |⊥ D ≡ δ
    elim-∈⊥-⊥  :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  {n ≢ n′} → (δ in⊥ E) |⊥ D′ ≡ ⊥
  {-# REWRITE elim-∈⊥ elim-|⊥ #-} 

module Products where

  open Notation.Products using (_×_; _,_; _↓₁; _↓₂) public

  variable δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-↓₁   :  ( δ , ε ) ↓₁     ≡  δ
    elim-↓₂   :  ( δ , ε ) ↓₂     ≡  ε
    elim-⊥-⊥  :  ( ⊥{D} , ⊥{E} )  ≡  ⊥{D × E}
  {-# REWRITE elim-↓₁ elim-↓₂ #-} 

  module Tuples where
    open Notation.Products.Tuples using (_^_) public

  module Sequences where
    open Notation.Products.Sequences using (n; _⋆; ⟨⟩; ⟨_⟩; #; _§_; _↓_; _†_) public

module Updates where
  open Notation.Updates using (_[_/_]; _[_/_]⊥; _[_←_]) public
```
Postulates of properties for our operations on tuples and sequences have not yet been developed.


[Postulated Domain Notation]: Notation.md#postulated-domain-notation
[Illustrative Tests]: Tests/index.md#illustrative-tests
[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf
[(Cockx2021TRT)]: https://doi.org/10.1145/3434341
