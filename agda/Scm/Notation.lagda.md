# Notation

This module declares some conventional notation for Scott-domains and the
associated functions on their carrier sets.

The following options support direct use of λ-notation for defining functions
between domains.

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
```
The notation for each domain constructor is generally declared in a separate
submodule. Opening a submodule makes its declared names directly visible.

```agda
module Scm.Notation where

open import Data.Bool.Base  using (Bool; false; true) public
open import Data.Nat.Base   renaming (ℕ to Nat) using (suc) public
open import Function        using (id; _∘_) public

postulate
  Domain  : Set₁         -- type of all domains
  ⟪_⟫     : Domain → Set  -- carrier

variable
  A B C   : Set
  D E F   : Domain
  n       : Nat

postulate
  ⊥       : ⟪ D ⟫         -- bottom element
  𝟙       : Domain        -- trivial domain
```

## Function domains

The carrier `⟪ D →ᶜ E ⟫` of a function domain should consist of just the
(Scott-)continuous functions between the carriers `⟪ D ⟫` and `⟪ E ⟫`.
In Agda, however, that would require pairing all λ-abstractions with explicit
proofs of their continuity (and explicitly discarding the proofs when applying
functions), which is quite impractical.

To support direct use of conventional λ-notation for defining functions between
domains, the type `⟪ D →ᶜ E ⟫` is rewritten to the Agda type `⟪ D ⟫ → ⟪ E ⟫` of
*all* total functions between the carriers of `D` and `E`. Functions between
domains are *automatically* continuous when defined in terms of λ-abstraction
and application from the primitive continuous functions associated with
specific domain constructors, as usual in conventional denotational semantics.
And continuous endofunctions have (least) fixed points.

```agda
module Functions where

  postulate
    _→ᶜ_     : Domain → Domain → Domain -- assume continuous
    dom-cts  : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)

  {-# REWRITE dom-cts #-}

  infixr 0 _→ᶜ_

  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫ -- fixed points of endofunctions
```

It would be possible to declare an analogous type of *predomains*,[^pre]
together with notation for types of continuous functions between predomains.
The following declarations are for the special case of all functions from an
arbitrary type to a domain, which are trivially continuous, and may themselves
be regarded as a domain (ordered pointwise).

[^pre]:
    A predomain is like a domain, but its carrier need not have a `⊥`-element.

```agda
  postulate
    _→ˢ_     : Set → Domain → Domain -- always continuous
    set-cts  : ⟪ A →ˢ E ⟫ ≡ (A → ⟪ E ⟫)

  {-# REWRITE set-cts #-}

  infixr 0 _→ˢ_

open Functions
```

## Lifted domains

Lifting adds a `⊥`-element to an arbitrary type `A` to form a domain
`A +⊥`.[^lift] The conventional notation for the lifted domain formed from
$A$ is $A_⊥$, but Agda does not support such a subscript.

[^lift]:
    Lifting can be generalised to add a (fresh) `⊥`-element to a domain or
    predomain.

In published examples of denotational semantics, the inclusion operation `η`
is generally left implicit; and ordinary operations on sets of elements are
assumed to map `⊥` to `⊥`, which avoids the need for explicit use of `_♯`.
However, it seems difficult to support such conventions in Agda formalisations.

```agda
module Lifted where

  postulate
    _+⊥  : Set → Domain               -- lifted set
    η    : ⟪ A →ˢ A +⊥ ⟫              -- inclusion
    _♯   : ⟪ (A →ˢ D) →ᶜ A +⊥ →ᶜ D ⟫  -- Kleisli extension

  infix 10 _+⊥
```

### Booleans

The McCarthy conditional operation extends the usual ternary conditional choice
to carriers of domains. It is expected to return `⊥` whenever its first argument
is `⊥`.

A short arrow is conventionally used in denotational semantics both for
function domains and McCarthy conditionals. Agda reserves the short arrow `→`
for ordinary (and dependent) function types.

```agda
  module Booleans where

    Bool⊥ = Bool +⊥                      -- truth-value domain
    
    postulate
      _⟶_,_  : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫  -- McCarthy conditional

    infixr 20 _⟶_,_
```

### Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.


```agda
  module Naturals where

    Nat⊥ = Nat +⊥ -- natural number domain

    open Booleans

    postulate
      _==⊥_  : ⟪ Nat⊥ →ᶜ Nat⊥ →ᶜ Bool⊥ ⟫ -- strict numerical equality
```

### Strings

Agda allows literal strings enclosed in double quotation marks `"..."`.

```agda
  module Strings where
    open import Data.String.Base using (String) public

    String⊥ = String +⊥ -- meta-string domain
```

## Sum domains

The coalesced sum of two domains correspons to lifting the disjoint union of
the non-`⊥` elements of their carriers. It is associative, in contrast to the
separated sum (which adds a fresh `⊥`-element to the disjoint union of the
complete carriers).

In published examples of denotational semantics, injections from summands
into sum domains are usually left implicit, and case analysis is specified
by combining a boolean-valued test with the McCarthy conditional and projection
from sums to summands.

```agda
module Sums where

  postulate
    _+_    : Domain → Domain → Domain                 -- coalesced sum
    inj₁   : ⟪ D →ᶜ D + E ⟫                            -- injection
    inj₂   : ⟪ E →ᶜ D + E ⟫                            -- injection
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ (D + E →ᶜ F) ⟫  -- case analysis

  infixr 1 _+_
```

## Product domains

The carrier of the binary cartesian product of two domains consists of all
pairs of elements of the carriers of the agument domains. Neither the product
nor pairing is associative.

```agda
module Products where

  postulate
    _×_   : Domain → Domain → Domain   -- cartesian product
    _,_   : ⟪ D →ᶜ E →ᶜ D × E ⟫         -- pairing
    _↓²1  : ⟪ D × E →ᶜ D ⟫              -- 1st projection
    _↓²2  : ⟪ D × E →ᶜ E ⟫              -- 2nd projection
    _↓³1  : ⟪ D × E × F →ᶜ D ⟫          -- 1st projection
    _↓³2  : ⟪ D × E × F →ᶜ E ⟫          -- 2nd projection
    _↓³3  : ⟪ D × E × F →ᶜ F ⟫          -- 3rd projection

  infixr 2 _×_
  infixr 4 _,_
```

It would be possible to add similar notation for so-called *smash*-products,
where the pairing operation is strict.

### Tuples

The domain `D ^ n` of `n`-tuples of elements of a domain `D` is conventionally
written $D^n$, but Agda does not support the use of variables as superscripts,
and requires spaces aroun the `^` operator.

Note that `D ^ 2` is equal to `D × D`.

```agda
  module Tuples where

    _^_ : Domain → Nat → Domain
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)

    infix 8  _^_
```

### Sequences

The domain `D ⋆` of finite sequences of elements of a domain `D` is
conventionally written $D^*$, but Agda does not allow the use of `*` as a
superscipt, and requires a space before the asterisk.

The following notation for the various operations on sequences was introduced
and extensively used by Strachey and his colleagues in the early 1970s.

The single angle-brackets `⟨...⟩` used to form  sequences are unrelated to the
double angle-brackets `⟪ D ⟫` used for the carrier of domain `D`.


```
  module Sequences where

    open Lifted.Naturals
    open Tuples

    postulate
      _⋆     : Domain → Domain         -- D ⋆ domain of finite sequences 
      ⟨⟩     : ⟪ D ⋆ ⟫                 -- empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫  -- ⟨ d₁ , ... , dₙ₊₁ ⟩ non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫         -- # d⋆                sequence length
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫   -- d⋆ § d⋆             concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫     -- d⋆ ↓ n              nth component
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫   -- d⋆ † n              nth tail
```

Temporary:

```agda
open Functions public
open Lifted public
open Booleans public
open Naturals public
open Strings public
open Sums public
open Products public
open Tuples public
open Sequences public
```