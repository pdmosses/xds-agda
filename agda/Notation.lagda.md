# Postulated Domain Notation

This section postulates Agda notation for the domain constructors and
associated functions used in the [illustrative examples].


[Illustrative Examples]: Examples/index.md#illustrative-examples
[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 

variable A B C : Set
```

## Domains

Domains are embedded in Agda as elements of the  type `Domain`.
A domain `D` is not itself a type, but it has a *carrier* type `⟪ D ⟫ : Set`,
which always contains an element `⊥{D}`
(written `⊥` when Agda can infer `D`).
```agda
module Domains where
  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the carrier type of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the 'bottom' element of D
    𝟙 : Domain                -- 𝟙 is a unit domain
  variable D E F : Domain

open Domains public
```
Some previous papers on embedding denotational semantics in Agda
[(Mosses2025CDS)]\ [(Mosses2025CSE)]\ [(Mosses2025LAF)]
defined domains to be types: `Domain = Set`.
However, postulating `⊥ : D` for all `D : Domain` was then
*inconsistent* with the existence of an empty type in Agda.
Postulating `Domain : Set` avoids that inconsistency.

The notation for domains postulated here supports *type-checking*
embeddings of denotational semantics in Agda such as those in the
illustrative examples.
It does *not* define or constrain the *mathematical structure* of domains,
nor the algebraic and universal properties of the associated functions.

[(Mosses2025CDS)]: https://doi.org/10.1145/3759537.3762694
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[(Mosses2025LAF)]: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper11.pdf

## Function Domains

The conventional notation in denotational definitions for the domain of
continuous functions from $D$ to $E$ is $D \to E$ or $[D \to E]$.
However, Agda reserves the notation `D → E` for the *type* of *all* (total)
functions from type `D` to type `E`;
instead, we use the notation `D →ᶜ E` for embedding continuous function domains:
```agda
module Functions where
  postulate _→ᶜ_ : Domain → Domain → Domain
  -- D →ᶜ E is the domain of continuous functions from D to E
  infixr 0 _→ᶜ_
```
Both λ-abstraction and application preserve continuity.
In conventional denotational semantics,
functions between domains are defined using λ-abstraction and application
from primitive continuous functions associated with specific domain constructors,
so they are *automatically* continuous.
This motivates treating the carrier `⟪ D →ᶜ E ⟫` of the embedding of a function domain
as a type of continuous functions.
(*Proving* functions defined in λ-notation to be continuous in Agda
requires pairing each λ-abstraction with an explicit proof of its continuity,
which is quite impractical – especially when embedding denotations defined in
continuation-passing style.)

However, to support type-checking the *direct* embedding of λ-notation
from conventional denotational definitions in Agda,
it appears to be necessary to *rewrite* the carrier types of function domains
to ordinary function types:
```agda
  postulate dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
```
Similarly, the notation `A →ˢ D` is the embedding of the domain of all functions
from an ordinary type `A` to a domain `D` (which are trivially continuous,
ordered pointwise):
```agda
  postulate _→ˢ_ : Set → Domain → Domain
  -- A →ˢ D is the domain of all functions from A to D
  infixr 0 _→ˢ_
  postulate set-cts  : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
```
Embeddings of *endofunctions* `φ` on a domain `D` should always have
fixed points `fix φ`, with `fix` itself also being continuous:
```agda
  postulate fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
```
```agda
open Functions public
```

## Recursive Domains

Conventional denotational semantics often involves groups of mutually
recursive domain definitions.
In Agda, recursive type definitions lead to non-termination of
the type-checker.
To avoid non-termination, it is sufficient to break the recursion by
leaving (one or more) domains as *postulated*.
The following operations can then be used to map values from a postulated domain
to its structure and *vice versa*.
```agda
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold  : {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold    : {{D ≅ E}} → ⟪ E →ᶜ D ⟫
```
The *instance parameter* `{{D ≅ E}}` of the above operations restricts them
to domains `D` and `E` for which `instance _ : D ≅ E` has been declared.

[(Abramsky1995DT)]: https://achimjungbham.github.io/pub/papers/handy1.pdf

## Flat Domains

Lifting an ordinary set $A$ by adding a $\bot$ element gives a flat domain,
usually written $A_\bot$.
Our Agda embedding postulates a corresponding domain constructor `A +⊥`,
together with a function `↑` for injecting elements of `A` into `A +⊥`,
and an operator `f ♯` for extending functions on `A` to arguments in `A +⊥`.
```agda
module Flat where
  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
```

### Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It returns `⊥` whenever its first argument is `⊥`.
```agda
  module Booleans where
    open import Data.Bool.Base public using (Bool; false; true; if_then_else_)
    Bool⊥ = Bool +⊥
    _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂) ♯  
    infixr 20 _⟶_,_
```
This module also defines `Eq A` for use as an instance parameter,
restricting operation definitions to types `A` such that `_==_ : A → A → Bool`,
and postulates a `Bool⊥`-valued operation `δ₁ ==⊥ δ₂` on `A +⊥`.
```agda
    record Eq (A : Set) : Set where field _==_ : A → A → Bool
    open Eq {{...}} public
    postulate
      _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      -- δ₁ ==⊥ δ₂ is ⊥ when either operand is ⊥
      instance eqBool : Eq Bool
```

### Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.
```agda
  module Naturals where
    open import Agda.Builtin.Nat public
      using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)
    Nat⊥ = Nat +⊥
    open Booleans
    postulate 
      instance eqNat : Eq Nat
```

## Sum Domains

The separated sum `D + E` of two domains corresponds to lifting the disjoint
union of their carrier sets. 
The following operations can be used directly for binary sums,
and iterated for domains with more than two summands.
```agda
module Sums where
  postulate
    _+_    : Domain → Domain → Domain   -- D + E is separated sum
    inj₁   : ⟪ D →ᶜ (D + E) ⟫           -- inj₁ δ is injection from D
    inj₂   : ⟪ E →ᶜ (D + E) ⟫           -- inj₂ ε is injection from E
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫
    -- [ φ , ψ ] applies φ to arguments in D, and ψ to arguments in E
```
Conventional denotational definitions of programming languages (e.g., in [(Scheme)])
use domain names instead of numerical indices in operations associated with separated sums.
The inherently *dependent* types of the Agda embedding of these operations are as follows.
```agda
  open import Agda.Builtin.Nat using (Nat)
  open Flat
  open Flat.Booleans
  open Flat.Naturals
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E injection
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D  projection
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D  inspection
```
The operations are defined only for `D` and `E`
where an instance of type `E ≳ n ↦ D` is declared for some `n`.
Instead of defining the summands `D` of a separated sum
domain `E` by an equation `E = ... + D + ...`, the
domain `E` is merely *postulated*, and each summand is
declared separately by `instance _ : E ≳ n ↦ D` (where
`n` should be a different natural number for each summand).

[(Scheme)]: https://standards.scheme.org

## Product Domains

The carrier of the binary product `D × E` of two domains consists of all
pairs `(d , e)` of elements of `D` and `E`
with the pair `(⊥{D} , ⊥{E})` as the bottom element `⊥{D × E}`.
Neither the product nor pairing is associative.
The following operations can be used directly for binary products,
and iterated for products of more than two domains.
```agda
module Products where
  postulate
    _×_  : Domain → Domain → Domain     -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫        -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫             -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫             -- (δ , ε)↓₂ is ε
  infixr 2 _×_
  infixr 4 _,_
```

### Tuples

The domain `D ^ n` of `n`-tuples of elements of a domain `D` is conventionally
written $D^n$, but Agda does not support the use of variables as superscripts.
```agda
  module Tuples where
    open import Agda.Builtin.Nat public using (Nat; suc)
    _^_ : Domain → Nat → Domain         -- D ^ n is the domain of n-tuples (n ≥ 0)
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)
```

### Sequences

The domain `D ⋆` of finite sequences of elements of a domain `D` is
conventionally written $D^*$.

The following notation for the various operations on sequences was introduced
in the early 1970s, and is used in the *Scheme* semantics [(Scheme)].
(The single angle-brackets `⟨...⟩` used to form sequences are unrelated to the
double angle-brackets `⟪ D ⟫` used for the carrier of domain `D`.)
```agda
  module Sequences where
    open Flat.Naturals
    open Tuples
    variable n : Nat
    postulate
      _⋆     : Domain → Domain          -- D ⋆ is the finite sequence domain
      ⟨⟩     : ⟪ D ⋆ ⟫                  -- ⟨⟩ is the empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫   -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫          -- # δ⋆ is the length of sequence δ⋆
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫    -- δ⋆₁ § δ⋆₂ is sequence concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫      -- δ⋆ ↓ n is the nth element
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫    -- δ⋆ † n is the nth tail
```

## Updates

When a type `A` has an equality operation `_==_ : A → A → Bool`,
environments `ρ : ⟪ A →ˢ D ⟫` can be 'updated' (i.e., extended or overridden) using the
conventional notation `ρ [ δ / a ]`, defined as follows.
```agda
module Updates where
  open Flat
  open Flat.Booleans
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
```
Similarly for stores `σ : ⟪ (A +⊥) →ᶜ D ⟫`:
```agda
  open Flat
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
```
Defining an operation `m [ x ← y ]` for extension or overriding of *dependent* maps `m` is less straightforward,
as it involves an equality test that may return an *equivalence proof*.
```agda
  open import Data.Maybe.Base public using (Maybe; just; nothing)
  open import Relation.Binary.PropositionalEquality.Core public using (_≡_; refl)
  record MaybeEq (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open MaybeEq {{...}} public
  variable X : Set; Y : X → Set
  _[_←_] :  {{MaybeEq X}} → (∀ x′ → Y x′) → (x : X) → Y x → (∀ x′ → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) where
    h : (x′ : X) → Maybe (x ≡ x′) → Y x′
    h x′ (just refl) = y
    h x′ nothing = m x′
```