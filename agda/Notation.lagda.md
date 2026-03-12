# Notation

This module declares some conventional notation for Scott domains and the
associated functions on their carrier sets. The specified options support
direct use of λ-notation for defining functions between domains.

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 

variable A B C : Set
```

## Domains

The notation used in conventional denotational definitions does not depend
on the details of the mathematical structure of domains.[^domains] The only
essential feature of domains is that each domain `D` has a distinguished
element `⊥` (pronounced "bottom") that represents undefinedness. The only
element of the unit domain `𝟙` is `⊥`.[^bottom]

[^domains]:
    A Scott domain is an algebraic, bounded-complete and directed-complete
    partial order (dcpo).

[^bottom]:
    The standard Agda library module `Data.Empty` defines `⊥` to be the empty
    *type*. As domains are always non-empty, that type is not needed here.
    The built-in Agda notation for the only element of a 1-element type `⊤`
    is `tt`.

!!! warning
    The specified postulates that declare types and functions for domains
    are used only for type-checking denotational semantics in Agda.
    They do *not* define the mathematical structure of domains,
    nor the algebraic and universal properties of the associated functions.
    Postulated equivalences are used for testing denotations of terms,
    and added as rewrite rules to allow their use to be implicit.

```agda
module Domains where

  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the type of elements of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the bottom element of D
    𝟙 : Domain                -- 𝟙 is a unit domain

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

## Function domains

The conventional notation in denotational definitions for the domain of all
continuous functions from `D` to `E` is usually `D → E`, with `D → E → F`
grouped as `D → (E → F)`. However, Agda reserves the notation `D → E` for the
*type* of *all* total functions from `D` to `E`. The following module declares
the notation `D →ᶜ E` where the superscript `c` suggests that the elements of
the domain are continuous functions.

```agda
module Functions where

  postulate
    _→ᶜ_ : Domain → Domain → Domain
    -- D →ᶜ E is the domain of continuous functions from D to E
  infixr 0 _→ᶜ_
```

In conventional denotational semantics, functions between domains are
*automatically* continuous when defined in terms of λ-abstraction and
application from primitive continuous functions associated with specific
domain constructors. 

The carrier `⟪ D →ᶜ E ⟫` of a function domain `D →ᶜ E` should consist of just
the (Scott-)continuous functions between the carriers `⟪ D ⟫` and `⟪ E ⟫`.
In Agda, however, that would require pairing all λ-abstractions with explicit
proofs of their continuity (and explicitly discarding the proofs when applying
functions), which is quite impractical.

To support type-checking direct use of conventional λ-notation for defining functions between
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
includes *all* functions from `A` to `D` (which are trivially continuous
when ordered pointwise).

[^pre]:
    A predomain is like a domain, but its carrier need not have a `⊥` element.

```agda
  postulate
    _→ˢ_ : Set → Domain → Domain
  -- A →ˢ D is the domain of all functions from A to D
  infixr 0 _→ˢ_
```

The type `⟪ A →ˢ D ⟫` is *rewritten* to the Agda type `A → ⟪ D ⟫`:

```agda
  postulate
    set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}
```

Continuous *endofunctions* `φ` in `D →ᶜ D` have (least) fixed points `fix φ`:

```agda
  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
    -- fix φ is the least fixed point of the continuous function φ
    apply-fix : {φ : ⟪ D →ᶜ D ⟫} → fix φ ≡ φ (fix φ)
    -- apply-fix{φ} unfolds fix φ once
  {-# REWRITE apply-fix #-}
```

The above notation is implicitly imported by the remaining submodules of `Notation`:

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
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}
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

The least domain `D` with `D ≅ (D →ᶜ D)` is the unit domain. For any
domain `D₀` there is a domain `D` that includes `D₀` with `D ≅ (D →ᶜ D)`.

## Flat domains

Adding a `⊥` element to an arbitrary set `A` forms the 'flat' domain `A +⊥`.
(The conventional notation for the lifted domain formed from $A$ is $A_⊥$, but
Agda does not support such a subscript.) 

The notation `↑ a` introduced below seems reasonably suggestive for the
inclusion of the non-`⊥` elements in `A +⊥`. (In theoretical treatments of
monads, `η a` is commonly used, but that conflicts with the convention of using
single lower-case Greek letters as bound variables.)

When `D` is a flat domain and `f` is a function from `A` to `D`, the notation
`f ♯` corresponds to the Kleisli extension of `f` to a function from `A +⊥`
to `D`. (In published examples of denotational semantics, ordinary operations
on sets are often *implicitly lifted* to flat domains, mapping `⊥` to `⊥`.
However, it is difficult to support such conventions in Agda.)

```agda
module Flat where

  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-} 
```

### Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It returns `⊥` whenever its first argument is `⊥`.

```agda
  module Booleans where

    open import Data.Bool.Base public using (Bool; false; true; if_then_else_)
    Bool⊥ = Bool +⊥
    _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂)♯  
    infixr 20 _⟶_,_
```

The instance parameter of the strict equality test `δ₁ ==⊥ δ₂` below declares
the operation only for flat domains `A +⊥` with `instance _ : Eq A`.
(Equality is unavailable on non-flat domains because it is not continuous.)

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
    variable n₁ n₂ : Nat
    postulate
      elim-==⊥ : (↑ n₁ ==⊥ ↑ n₂) ≡ ↑ (n₁ ==ᴺ n₂)
    {-# REWRITE elim-==⊥ #-} 
```

## Sum domains

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

  variable φ : ⟪ D →ᶜ F ⟫; ψ : ⟪ E →ᶜ F ⟫; δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-inj₁  :  [ φ , ψ ] (inj₁ δ)  ≡  φ δ
    elim-inj₂  :  [ φ , ψ ] (inj₂ ε)  ≡  ψ ε
    elim-[]-⊥  :  [ φ , ψ ] ⊥         ≡  ⊥
  {-# REWRITE elim-inj₁ elim-inj₂ #-} 
```

In published examples of denotational semantics, injection of $\delta$ from
a summand of a domain $E$ can be written $\delta \textsf{ in } E$ (but is
usually left implicit), and case analysis on $\epsilon$ is written by composing
the test $\epsilon \in D$ with the McCarthy conditional and projection
$\epsilon \mid D$. 

Agda supports type-checking the conventional notation
for these operations (after adding `⊥` as a suffix to avoid reserved symbols):

- When `δ : D`, `δ in⊥ E` is its injection into `E`.
- When `ε : E`, `ε |⊥ D` is its projection onto `D`,
  and `ε ∈⊥ D` (`ε ∈⊥ E`) tests whether `ε` is
  the injection of an element of `D` (resp. `E`).

This notation is independent of the order of the summands.

However, instead of defining the summands `D` of a separated sum domain `E` by
an equation `E = ... + D + ...`, the domain `E` is merely *postulated*, and
each summand is declared separately by `instance _ : E ≳ n ↦ D` (where `n`
should be a different natural number for each summand). This also avoids
non-termination due to indirect recursion in groups of type definitions.

The inherently *dependent* types of the above operations are as follows.
The inferred instance argument `{{E ≳ n ↦ D}}` determines `D` and `E`.
(The notation `D →ᶜ E` cannot be used for dependent types, but for fixed domains
the unary functions are known to be continuous when `E` is a sum domain.)

```agda
  open import Agda.Builtin.Nat using (Nat)
  open Flat
  open Flat.Booleans
  open Flat.Naturals
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E is injection from D
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D is projection to D
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D tests an injection

  open import Relation.Binary.PropositionalEquality.Core using (_≢_)
  variable D′ : Domain; n′ : Nat
  postulate
    elim-∈⊥    :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  (δ in⊥ E) ∈⊥ D′ ≡ ↑ (n ==ᴺ n′)
    elim-|⊥    :  {{_ : E ≳ n ↦ D}} → (δ : ⟪ D ⟫) → (δ in⊥ E) |⊥ D ≡ δ
    elim-∈⊥-⊥  :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  {n ≢ n′} → (δ in⊥ E) |⊥ D′ ≡ ⊥
  {-# REWRITE elim-∈⊥ elim-|⊥ #-} 
```

## Product domains

The carrier of the binary cartesian product of two domains consists of all
pairs of elements of the carriers of the agument domains. Neither the product
nor pairing is associative. The following operations can be used directly for
binary products, and iterated for products of more than two domains.


```agda
module Products where

  postulate
    _×_  : Domain → Domain → Domain  -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫     -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫          -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫          -- (δ , ε)↓₂ is ε

  infixr 2 _×_
  infixr 4 _,_

  variable δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-↓₁  :  ( δ , ε ) ↓₁  ≡  δ
    elim-↓₂  :  ( δ , ε ) ↓₂  ≡  ε
  {-# REWRITE elim-↓₁ elim-↓₂ #-} 
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
      _⋆     : Domain → Domain          -- D ⋆ is the finite sequence domain
      ⟨⟩     : ⟪ D ⋆ ⟫                  -- ⟨⟩ is the empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫   -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫          -- # δ⋆ is the length of sequence δ⋆
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫    -- δ⋆₁ § δ⋆₂ is sequence concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫      -- δ⋆ ↓ n is the nth element
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫    -- δ⋆ † n is the nth tail
```

## Updates

When an ordinary Agda type `A` has an equality operation `_==_ : A → A → Bool`,
environments `ρ : ⟪ A →ˢ D ⟫` can be "updated" (i.e., extended or overridden) using the
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

Defining extension or overriding of *dependent* maps is less straightforward,
as it involves a function that returns an *equivalence proof* instead of a
truth value: 

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