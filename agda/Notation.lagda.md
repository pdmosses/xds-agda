# Notation

This module declares some conventional notation for Scott domains and the
associated functions on their carrier sets. The specified options support
direct use of λ-notation for defining functions between domains.

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

variable A B C : Set
```

## Domains

The notation used in conventional denotational definitions does not depend
on the details of the mathematical structure of domains.[^domains] The only
essential feature of domains is that each domain `D` has a distinguished
element `⊥` (pronounced "bottom") that represents undefinedness. The only
element of the trivial domain `𝟙` is `⊥`.[^bottom]

[^domains]:
    A Scott domain is an algebraic, bounded-complete and directed-complete
    partial order (dcpo).

[^bottom]:
    The standard Agda library module `Data.Empty` defines `⊥` to be the empty
    *type*. As domains are always non-empty, that type is not needed here.
    The built-in Agda notation for the only element of a 1-element type `⊤`
    is `tt`.

```agda
module Domains where
  postulate
    Domain : Set
    ⟪_⟫ : Domain → Set
    ⊥ : {D : Domain} → ⟪ D ⟫
    𝟙 : Domain
  variable D E F : Domain

open Domains public
```

In three previous papers ([Mosses2025CDS], [Mosses2025CSE], [Mosses2025LAF]),
the type of domains was defined by `Domain = Set`. However, postulating `⊥ : D`
for all domains `D` was then *inconsistent* with the existence of an empty type
in Agda. The current declaration `Domain : Set₁` circumvents that issue, but
Agda then requires domains `D` to be distinguished from their carrier sets
`⟪ D ⟫`.[^history]

[Mosses2025CDS]: https://doi.org/10.1145/3759537.3762694
[Mosses2025CSE]: https://doi.org/10.1145/3759427.3760369
[Mosses2025LAF]: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper11.pdf

[^history]:
    The current declarations were previously adopted in a lightweight
    formalisation of a denotational semantics of inheritance ([JENSFEST 2024]),
    see [Inheritance/Definitions]. András Kovács pointed out that they have the
    advantage of consistency.

[JENSFEST 2024]: https://2024.splashcon.org/home/jensfest-2024/
[Inheritance/Definitions]: https://github.com/pdmosses/jensfest-agda/blob/main/Inheritance/Definitions.lagda
[AIM-XLI]: https://wiki.portal.chalmers.se/agda/Main/AIMXLI

The notation for each domain constructor is generally declared in a separate
submodule.

!!! info
    The [Properties] module postulates equational properties of the postulated
    operations on elements of domains, and declares them as rewrite rules.

[Properties]: ../Properties/index.md

## Function domains

The conventional notation in denotational definitions for the domain of all
continuous functions from `D` to `E` is usually `D → E`, with `D → E → F`
grouped as `D → (E → F)`. However, Agda reserves the notation `D → E` for the
*type* of *all* total functions from `D` to `E`. The following module declares
the notation `D →ᶜ E` where the superscript `c` suggests that the elements of
the domain are continuous functions.

```agda
module Functions where
  open import Agda.Builtin.Equality using (_≡_) public
  open import Agda.Builtin.Equality.Rewrite using ()
  postulate
    _→ᶜ_ : Domain → Domain → Domain
  infixr 0 _→ᶜ_
```

In conventional denotational semantics, functions between domains are
*automatically* continuous when defined in terms of λ-abstraction and
application from primitive continuous functions associated with specific
domain constructors. And continuous *endofunctions* `f` in `D →ᶜ D` have
(least) fixed points, given by `fix f`:

```agda
  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
```

The carrier `⟪ D →ᶜ E ⟫` of a function domain `D →ᶜ E` should consist of just
the (Scott-)continuous functions between the carriers `⟪ D ⟫` and `⟪ E ⟫`.
In Agda, however, that would require pairing all λ-abstractions with explicit
proofs of their continuity (and explicitly discarding the proofs when applying
functions), which is quite impractical.

To support direct use of conventional λ-notation for defining functions between
domains, the type `⟪ D →ᶜ E ⟫` is *rewritten*[^rewrite] to the Agda type
`⟪ D ⟫ → ⟪ E ⟫`:

[^rewrite]:
    This rewrite rule appears to be essential for defining functions as
    elements of `⟪ D →ᶜ E ⟫` without applying an explicit injection to each
    λ-abstraction. Jesper Cockx suggested it, together with the use of the
    `--lossy-unification` option (which appears to be required in some modules,
    but resulted in slow type-checking when used in *all* modules).

```agda
  postulate
    dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}
```

It would be possible to declare an analogous type of *predomains*,[^pre]
together with notation for types of continuous functions between predomains.
An ordinary set `A` is a special case of a predomain. The domain `A →ˢ D`
include *all* functions from `A` to `D` (which are trivially continuous
when ordered pointwise).

[^pre]:
    A predomain is like a domain, but its carrier need not have a `⊥` element.

```agda
  postulate
    _→ˢ_ : Set → Domain → Domain
  infixr 0 _→ˢ_
```

The type `⟪ A →ˢ D ⟫` is *rewritten* to the Agda type `A → ⟪ D ⟫`:

```agda
  postulate
    set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
```

The subsequent modules all involve the above notation:

```agda
open Functions public
```

## Recursive domains

Conventional denotational semantics often involves groups of mutually
recursive domain definitions. Agda supports groups of non-recursive type
definitions, but recursive type definitions lead to non-termination of the
type-checker.

To avoid non-termination, it is sufficient to break the recursion by leaving
(one or more) domains as postulated. The following operations can then be used
to map values from a postulated domain to its structure and *vice versa*.

```agda
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫
```

The *instance parameter* `{{D ≅ E}}` of the above operations restricts them
to domains `D` and `E` such that `instance _ : D ≅ E` has been declared.

For example, an Agda formalisation of Scott's $D_\infty$ domain,
isomorphic to the domain of all continuous endofunctions on $D_\infty$,
is simply as follows.

```agda
  module D-infinity where
    postulate
      D∞ : Domain
      instance _ : D∞ ≅ (D∞ →ᶜ D∞)
```

## Flat domains

Adding a `⊥` element to an arbitrary set `A` forms the 'flat' domain `A +⊥`.
(The conventional notation for the lifted domain formed from $A$ is $A_⊥$, but
Agda does not support such a subscript.) 

The notation `↑ a` introduced below seems reasonably suggestive for the
inclusion of the non-`⊥` elements in `A +⊥`. (In theoretical treatments of
monads, `η a` is commonly used, but that conflicts with the convention of using
single lowercase Greek letters as bound variables.)

When `D` is a flat domain and `f` is a function from `A` to `D`, the notation
`f ♯` corresponds to the Kleisli extension of `f` to a function from `A +⊥`
to `D`. (In published examples of denotational semantics, ordinary operations
on sets are often *implicitly lifted* to flat domains, mapping `⊥` to `⊥`.
However, it is difficult to support such conventions in Agda.)

```agda
module Flat where
  postulate
    _+⊥  : Set → Domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫
```

### Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It is supposed to return `⊥` whenever its first
argument is `⊥`.

```agda
  module Booleans where
    open import Data.Bool.Base using (Bool; false; true; if_then_else_) public
    Bool⊥ = Bool +⊥
    postulate
      _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫
    infixr 20 _⟶_,_
```

The instance parameter of the strict equality test `δ₁ ==⊥ δ₂` below declares
the operation only for flat domains `D` with `instance _ : Eq⊥ D`.
(Equality is unavailable on non-flat domains because it is not continuous.)

```agda
    postulate
      Eq⊥ : Domain → Set
      _==⊥_ : {{Eq⊥ (A +⊥)}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      instance eq⊥Bool⊥ : Eq⊥ Bool⊥
```

### Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.

```agda
  module Naturals where
    open import Data.Nat.Base renaming (ℕ to Nat) using (suc; _+_; _∸_; _≡ᵇ_) public
    Nat⊥ = Nat +⊥
    open Booleans
    postulate
      instance eq⊥Nat⊥ : Eq⊥ Nat⊥
```

### Strings

Agda allows literal strings enclosed in double quotation marks `"..."`.

```agda
  module Strings where
    open import Data.String.Base using (String) public
    String⊥ = String +⊥
    open Booleans
    postulate
      instance _ : Eq⊥ String⊥
```

## Sum domains

The coalesced sum `D ⊕ E` of two domains corresponds to lifting the disjoint
union of the non-`⊥` elements of their carrier sets. It is associative (in
contrast to the separated sum, which lifts the disjoint union of the complete
carrier sets).

The following operations can be used directly for binary sums, and iterated
for domains with more than two summands.

```agda
module Sums where
  postulate
    _⊕_    : Domain → Domain → Domain
    inj₁   : ⟪ D →ᶜ (D ⊕ E) ⟫
    inj₂   : ⟪ E →ᶜ (D ⊕ E) ⟫
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D ⊕ E) →ᶜ F) ⟫
```

In published examples of denotational semantics, injection of $\delta$ from
a summand of a domain $E$ can be written $\delta \textsf{ in } E$ (but is
usually left implicit), and case analysis on $\epsilon$ is written by composing
the test $\epsilon \in \textsf{D}$ with the McCarthy conditional and projection
$\epsilon \mid \textsf{D}$. Agda supports type-checking the conventional notation
for these operations (after adding `⊥` as a suffix to avoid reserved symbols):

- When `δ : D`, `δ in⊥ E` is its injection into `E`.
- When `ε : E`, `ε |⊥ D` is its projection onto `D`,
  and `ε ∈⊥ D` tests whether `ε` is the injection of an element of `D`.

However, instead of defining the summands `D` of a coalesced sum domain `E` by
an equation `E = ... + D + ...`, the domain `E` is merely *postulated*, and
each summand is declared separately by `instance _ : E ≳ n ↦ D` (where `n`
should be a different natural number for each summand). This also avoids
non-termination due to indirect recursion in groups of type definitions.

The inherently *dependent* types of the above operations are as follows.
The argument `{D : Domain}` is implicit, and inferred from the other arguments;
the instance argument `{{E ≳ n ↦ D}}` is also inferred.

```agda
  open import Data.Nat.Base renaming (ℕ to Nat)
  open Flat.Booleans
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫
```

## Product domains

The carrier of the binary cartesian product of two domains consists of all
pairs of elements of the carriers of the agument domains. Neither the product
nor pairing is associative. The following operations can be used directly for
binary products, and iterated for products of more than two domains.


```agda
module Products where
  postulate
    _×_  : Domain → Domain → Domain
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫
  infixr 2 _×_
  infixr 4 _,_
```

### Tuples

The domain `D ^ n` of `n`-tuples of elements of a domain `D` is conventionally
written $D^n$, but Agda does not support the use of variables as superscripts.

```agda
  module Tuples where
    open import Data.Nat.Base renaming (ℕ to Nat) using (suc) public
    _^_ : Domain → Nat → Domain
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)
```

Making `D ^ 2` definitionally equal to `D × D` in Agda supports type-checking
the conventional notational ambiguity between tuples and iterated products.

### Sequences

The domain `D ⋆` of finite sequences of elements of a domain `D` is
conventionally written $D^*$.

The following notation for the various operations on sequences was introduced
and extensively used by Strachey and his colleagues in the early 1970s.
(The single angle-brackets `⟨...⟩` used to form sequences are unrelated to the
double angle-brackets `⟪ D ⟫` used for the carrier of domain `D`.)

```agda
  module Sequences where
    open Flat.Naturals
    open Tuples
    variable n : Nat
    postulate
      _⋆     : Domain → Domain
      ⟨⟩     : ⟪ D ⋆ ⟫
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫
```

## Updates

When an ordinary Agda type `A` has an equality operation `_==_ : A → A → Bool`,
environments `ρ : ⟪ A →ˢ D ⟫` can be "updated" (i.e., extended or overridden) using the
conventional notation `ρ [ δ / a ]`, defined as follows.

```agda
module Updates where
  open Flat
  open Flat.Booleans
  record Eq (A : Set) : Set where field _==_ : A → A → Bool
  open Eq {{...}} public
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
```

For stores `σ : ⟪ (A +⊥) →ᶜ D ⟫`, however, an equality operation
`_==⊥_ : ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫` on the flat domain is required:

```agda
  open Flat
  _[_/_]⊥ : {{Eq⊥ (A +⊥)}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
```

Defining extension or overriding of *dependent* maps is less straightforward,
as it involves a function that returns an *equivalence proof* instead of a
truth value: 

```agda
  open import Data.Maybe.Base using (Maybe; just; nothing) public
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl) public
  record EqMaybe (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open EqMaybe {{...}} public
  _[_←_] :  {X : Set} → {Y : X → Set} → {{EqMaybe X}} → 
            (∀ (x′) → Y x′) → (x : X) → Y x → (∀ (x′) → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) where
    h : (x′ : X) → Maybe (x ≡ x′) → Y x′
    h x′ (just refl) = y
    h x′ nothing = m x′
```