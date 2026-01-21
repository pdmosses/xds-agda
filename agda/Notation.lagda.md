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
module Notation where

open import Data.Bool.Base    using (Bool; false; true; if_then_else_) public
open import Data.Nat.Base     renaming (ℕ to Nat) using (suc; _+_; _∸_; _≡ᵇ_) public
open import Data.String.Base  using (String) public
open import Function          using (id; _∘_) public

-- record Eq (A : Set) : Set where
--   field
--     _==_ : A → A → Bool
--
-- open Eq {{...}} public
--
-- Eq moved to Lifting.Maps to avoid:
--
-- Agda v2.8.0
-- Error
-- src/full/Agda/TypeChecking/Rewriting/Confluence.hs:787:10-17:
-- Non-exhaustive patterns in Pi b c

postulate
  Domain  : Set₁          -- type of all domains
  ⟪_⟫     : Domain → Set  -- carrier of a domain

variable
  A B C   : Set
  D E F   : Domain
  n       : Nat

postulate
  ⊥       : ⟪ D ⟫         -- bottom element
  𝟙       : Domain        -- trivial domain
```

In several papers published in 2025, the type  of domains was defined by
`Domain = Set`. However, postulating `⊥ : D` was then *inconsistent* with the
existence of an empty type in Agda. The current declaration `Domain : Set₁`
circumvents that issue, but also requires domains to be distinguished from
their carrier sets.[^history]

[^history]:
    The current declarations were previously adopted in the lightweight
    formalisation of a denotational semantics of inheritance (presented at
    [JENSFEST 2024]), see [Inheritance/Definitions]. I thought that declaring
    `Domain = Set` simplified direct use of λ-notation for defining functions
    between domains. At [AIM-XLI], however, András Kovács pointed out that this
    was not the case.

[JENSFEST 2024]: https://2024.splashcon.org/home/jensfest-2024/
[Inheritance/Definitions]: https://github.com/pdmosses/jensfest-agda/blob/main/Inheritance/Definitions.lagda
[AIM-XLI]: https://wiki.portal.chalmers.se/agda/Main/AIMXLI

## Function domains

The carrier `⟪ D →ᶜ E ⟫` of a function domain should consist of just the
(Scott-)continuous functions between the carriers `⟪ D ⟫` and `⟪ E ⟫`.
In Agda, however, that would require pairing all λ-abstractions with explicit
proofs of their continuity (and explicitly discarding the proofs when applying
functions), which is quite impractical.

To support direct use of conventional λ-notation for defining functions between
domains, the type `⟪ D →ᶜ E ⟫` is rewritten[^rewrite] to the Agda type
`⟪ D ⟫ → ⟪ E ⟫` of *all* total functions between the carriers of `D` and `E`.
Functions between domains are *automatically* continuous when defined in terms
of λ-abstraction and application from the primitive continuous functions
associated with specific domain constructors, as usual in conventional
denotational semantics. And continuous endofunctions have (least) fixed points.

[^rewrite]:
    This rewrite rule appears to be essential for defining functions as
    elements of `⟪ D →ᶜ E ⟫` without applying an explicit injection to each
    λ-abstraction. Jesper Cockx suggested the rule to me at [AIM-XLI], as well
    as the addition of the `--lossy-unification` option (which appears to be
    required in some modules, but resulted in slow type-checking when used in
    all modules).

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

open Functions public
```

## Recursive domains

Groups of non-recursive domains can be specified in Agda by type definitions.
For groups of mutually-recursive domains, the corresponding Agda type
definitions would lead to non-termination of the type-checker. To avoid
non-termination, it is sufficient to break the recursion by leaving (one or
more) domains as postulated. The following inverse operations can then be used
to map values from a postulated domain to its structure and *vice versa*.

```agda
module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    unfold : {D E : Domain} → {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :   {D E : Domain} → {{D ≅ E}} → ⟪ E →ᶜ D ⟫
```

The instance parameter `{{D ≅ E}}`` of the above operations declares them
only for domains `D` and `E` with `instance _ : D ≅ E`.

For example, the lightweight formalisation of Scott's $D_\infty$ domain,
isomorphic to the domain of all continuous endofunctions on $D_\infty$,
is simply as follows.

```agda
  module D-infinity where
    postulate
      D∞ : Domain
      instance _ : D∞ ≅ (D∞ →ᶜ D∞)
```

## Lifted domains

Lifting adds a `⊥`-element to an arbitrary type `A` to form a 'flat' domain
`A +⊥`.[^lift] The conventional notation for the lifted domain formed from
$A$ is $A_⊥$, but Agda does not support such a subscript.

The notation for the inclusion of `A` in `A +⊥` varies; `η` is commonly used
in theoretical treatments of monads, but conflicts with the convention of using
single lowercase Greek letters as bound variables. The 'floor' notation `⌊ a ⌋`
introduced below seems reasonably suggestive for the non-`⊥` elements of
`A +⊥`, and has the advantage of reducing the need for parentheses.
(Its conventional arithmetical interpretation is seldom needed in semantic
of programming languages.)

[^lift]:
    Lifting can be generalised to add a (fresh) `⊥`-element to a domain or
    predomain.

```agda
module Lifted where

  postulate
    _+⊥     : Set → Domain               -- lifted set
    ⌊_⌋     : ⟪ A →ˢ A +⊥ ⟫              -- inclusion
    _♯   : ⟪ (A →ˢ D) →ᶜ A +⊥ →ᶜ D ⟫  -- Kleisli extension

  infix 10 _+⊥
```

In published examples of denotational semantics, ordinary operations on sets
of elements are often implicitly lifted to flat domains, mapping `⊥` to `⊥`.
However, it seems difficult to support such conventions in Agda formalisations.

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

The instance parameter `{{Eq⊥ (A +⊥)}}` of the strict equality test `d₁ ==⊥ d₂`
below declares the operation only for flat domains `D` with `instance _ : Eq D`.
(Equality is unavailable on non-flat domains because it is not continuous.)

```agda
    postulate
      Eq⊥ : Domain → Set
      _==⊥_ : {A : Set} → {{Eq⊥ (A +⊥)}} → ⟪ A +⊥ →ᶜ A +⊥ →ᶜ Bool⊥ ⟫
```

### Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.

```agda
  module Naturals where

    Nat⊥ = Nat +⊥ -- natural number domain
```

### Strings

Agda allows literal strings enclosed in double quotation marks `"..."`.

```agda
  module Strings where

    String⊥ = String +⊥ -- meta-string domain
```

### Maps

When an ordinary Agda type `A` has an equality operation `_==_ : A → A → Bool`,
functions of type `A → B` can be extended or overridden using the following
conventional notation.

```agda
  module Maps where

    record Eq (A : Set) : Set where
      field
        _==_ : A → A → Bool
    
    open Eq {{...}} public

    _[_/_] : {A : Set} → {{Eq A}} → (A → B) → B → A → (A → B)
    f [ b / a ] = λ a′ → if a == a′ then b else f a′
```

The same notation can be used when `B` is `⟪ D ⟫` for some domain `D`:
the carrier of the function domain `A →ˢ D` is equivalent to `A → ⟪ D ⟫`.

The following definition lifts the above operation to a continuous function
domain `A +⊥ →ᶜ D`.

```agda
    open Booleans
    
    _[_/_]⊥ : {A : Set} → {{Eq⊥ (A +⊥)}} →
              ⟪ (A +⊥ →ᶜ D) →ᶜ D →ᶜ A +⊥ →ᶜ (A +⊥ →ᶜ D) ⟫
    φ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , φ α′
```

## Sum domains

The coalesced sum of two domains correspons to lifting the disjoint union of
the non-`⊥` elements of their carriers. It is associative, in contrast to the
separated sum (which adds a fresh `⊥`-element to the disjoint union of the
complete carriers).

```agda
module Sums where

  postulate
    _⊕_    : Domain → Domain → Domain                 -- coalesced sum
    inj₁   : ⟪ D →ᶜ D ⊕ E ⟫                            -- injection
    inj₂   : ⟪ E →ᶜ D ⊕ E ⟫                            -- injection
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ (D ⊕ E →ᶜ F) ⟫  -- case analysis

  infixr 1 _⊕_
```

In published examples of denotational semantics, injections from summands
into sum domains are usually left implicit, and case analysis is specified
by combining a boolean-valued test with the McCarthy conditional and projection
from sums to summands.

Here, `D ⇌ E` when `D` is a summand of a coalesced sum domain `E`.

- When `d` is an element of `D`, `d in⊥ E` is its injection into `E`.
- When `e` is an element of `E`, `e |⊥ D` is its projection onto `D`,
  and `e ∈⊥ D` tests whether `e` is the injection of an element of `D`.

The (inherently *dependent*) types of the above operations are given below.
The argument `{D : Domain}` is implicit, and inferred from the other arguments.
The argument `{{D ⇌ E}}` is an instance argument, and inferred from `instance`
declarations.

```agda
  open Lifted.Booleans
  
  postulate
    _⇌_   : Domain → Domain → Set
    _in⊥_ : {D : Domain} → ⟪ D ⟫ → (E : Domain) → {{D ⇌ E}} → ⟪ E ⟫
    _|⊥_  : {E : Domain} → ⟪ E ⟫ → (D : Domain) → {{D ⇌ E}} → ⟪ D ⟫
    _∈⊥_  : {E : Domain} → ⟪ E ⟫ → (D : Domain) → {{D ⇌ E}} → ⟪ Bool⊥ ⟫
```

!!! note

    The following Test module is to be removed.

```agda
  module Test where
  
    postulate R S T U : Domain

    postulate instance
      _ : R ⇌ S
      _ : T ⇌ U

    postulate
      r : ⟪ R ⟫
      t : ⟪ T ⟫

    s : ⟪ S ⟫
    s = r in⊥ S  -- ok accepted

    -- x : ⟪ S ⟫
    -- x = t in⊥ S  -- ok rejected (but accepted when x : S omitted!)
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
      _⋆     : Domain → Domain         -- D ⋆          finite sequences 
      ⟨⟩     : ⟪ D ⋆ ⟫                 -- ⟨⟩            empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫  -- ⟨ d₁ , ... ⟩  non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫         -- # d⋆          sequence length
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫   -- d⋆ § d⋆       concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫     -- d⋆ ↓ n        nth component
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫   -- d⋆ † n        nth tail
```

Use `open import Notation.All` to use all the notation declared above.

```agda
module All where
  open Functions public
  open Recursion public
  open Lifted    public
  open Booleans  public
  open Naturals  public
  open Strings   public
  open Maps      public
  open Sums      public
  open Products  public
  open Tuples    public
  open Sequences public
```