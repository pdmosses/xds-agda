# PCF definitions

PCF and its denotational semantics were orginally defined by Dana Scott in 1969
([Scott 1993]) with combinators (`S`, `K`) instead of λ-abstraction.
Gordon Plotkin subsequently defined a denotational semantics for PCF including 
λ-abstraction ([Plotkin 1977]). This module formalises a denotational semantics
of PCF in Agda, corresponding closely to Plotkin's original paper.

The following options are needed in connection with the lightweight
formalisation of [function domains] in Agda.

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Definitions where
open import Notation
```

## Abstract Syntax

```agda
module Abstract-Syntax where
```

### Types

The notation for types in ([Plotkin 1977]) uses the Greek letters `σ` and `τ`
to range over types, `ι` and `o` for ground types (of individuals and
truthvalues respectively), and `(σ → τ)` for function types. Agda supports
mixfix notation, but ordinary arrows and parentheses are reserved symbols;
the Agda formalisation of PCF types uses `σ ⇒ τ` instead of `(σ → τ)`:

```agda
  data Types  : Set where
    ι o       : Types
    _⇒_       : Types → Types → Types
  infixr 1 _⇒_
  variable σ τ : Types
```

As usual, `σ₁ ⇒ σ₂ ⇒ τ` is implicitly grouped to the right: `σ₁ ⇒ (σ₂ ⇒ τ)`.

### Variables

A variable in `Vars σ` is written `α i σ`; in ([Plotkin 1977]) variables are
written $\alpha_i^\sigma$, and the set of variables is not named.

The argument `i` merely distinguishes between variables – it is *not* a De Bruin
index.

```agda
  open import Data.Nat.Base renaming (ℕ to Nat) using () public
  data Vars   : Types → Set where
    α         : Nat → (σ : Types) → Vars σ
  variable i  : Nat
```

### Constants

The PCF term language includes `ℒᴬ`, the set of *standard* constants for arithmetic,
written $\mathcal L_A$ in ([Plotkin 1977]). 

```agda
  data ℒᴬ     : Types → Set where
    tt ff     : ℒᴬ o
    ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)
    Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)
    k         : Nat → ℒᴬ ι
    ⦅+1⦆      : ℒᴬ (ι ⇒ ι)
    ⦅−1⦆      : ℒᴬ (ι ⇒ ι)
    Z         : ℒᴬ (ι ⇒ o)
  variable c  : ℒᴬ σ
```

In ([Plotkin 1977]) the constants `⊃` and `Y` are subscripted by their types;
in Agda, it is simpler to leave `σ` as an *implicit* argument.

### Terms

For each type `σ` the terms in `Terms σ` are *[intrinsically-typed]*: all their
subterms are *well-typed*.

The term constructor `𝑉` below merely includes variables in terms;
the constructor `𝐿` includes constants.

In Agda, mixfix notation requires arguments to be separated by characters
other than spaces. Below, the notation for application `⦅ M ␣ N ⦆` and
λ-abstraction `⦅λ α ␣ M ⦆` uses the Unicode character `␣` (representing a
space) as a separator. Following ([Plotkin 1977]), both terms are
parenthesised, but using `⦅…⦆` instead of ordinary parentheses.

```agda
  data Terms  : Types → Set where
    𝑉_        : Vars σ → Terms σ
    𝐿_        : ℒᴬ σ → Terms σ
    ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ
    ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)
  variable M N : Terms σ
```

## Domain equations

The domains `𝒟 σ` form a *standard collection of domains for arithmetic*
in PCF, written $\mathcal D_\sigma$ in ([Plotkin 1977]).

As PCF is a simply-typed language, the domain equations do not involve
recursion. Their formalisation in Agda is as ordinary type definitions,
not involving bijections or embeddings.

```agda
module Domain-Equations where
  open Abstract-Syntax
  open Notation.Flat.Booleans using (Bool; Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥; eq⊥Nat⊥)
  𝒟 : Types → Domain
  𝒟 ι        = Nat⊥
  𝒟 o        = Bool⊥
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ
  variable x y z : ⟪ 𝒟 σ ⟫
```

Environments `ρ` are type-preserving maps from variables to values. They are
naturally modeled by a dependent type: `Env σ` consists of type-preserving maps
from variables in `Vars σ` to their values in the carrier of the domain `𝒟 σ`.
The environment `ρ⊥` maps all variables to `⊥`.

```agda
  Env = (σ : Types) → ⟪ Vars σ →ˢ 𝒟 σ ⟫
  variable ρ : Env
  ρ⊥ : Env
  ρ⊥ = λ _ → λ _ → ⊥
```

Extension or overriding environments requires instances of the equality tests
for both variables and types. The definition of the latter is somewhat tedious
in Agda.

```agda
  open Notation.Updates using (Eq; _==_; _[_/_])
  _==ⱽ_ : Vars σ → Vars σ → Bool
  open import Data.Nat.Base using (_≡ᵇ_) public
  (α i σ ==ⱽ α i′ σ)  =  (i ≡ᵇ i′)
  instance
    eqV : Eq (Vars σ)
    _==_ {{eqV}} = _==ⱽ_
  open Notation.Updates using (EqMaybe; _==?_; just; nothing; refl; _[_←_])
  instance
    eqT : EqMaybe Types
    _==?_ {{eqT}} ι ι = just refl
    _==?_ {{eqT}} o o = just refl
    _==?_ {{eqT}} (σ ⇒ τ) (σ₁ ⇒ τ₁) with σ ==? σ₁
    _==?_ {{eqT}} (σ ⇒ τ) (σ₁ ⇒ τ₁)    | nothing = nothing
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ τ₁)    | just refl with τ ==? τ₁
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ τ₁)    | just refl    | nothing   = nothing
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ .τ)    | just refl    | just refl = just refl
    _==?_ {{eqT}} _ _ = nothing
```

The definition of `ρ [ x / v ]′` is essentially the composition of two levels
of extension:

```agda
  _[_/_]′ : Env → ⟪ 𝒟 σ ⟫ → Vars σ → Env
  _[_/_]′ {σ} ρ x v = ρ [ σ ← ρ σ [ x / v ] ]
```

## Semantic functions

```agda
module Semantic-Functions where
  open Abstract-Syntax
  open Domain-Equations
```

### Variables

The notation `ρ ⟦ α i σ ⟧` gives the value of the variable `α i σ` in `ρ` by
applying `ρ σ` to the variable.

```agda
  _⟦_⟧ : Env → Vars σ → ⟪ 𝒟 σ ⟫
  ρ ⟦ α i σ ⟧ = ρ σ (α i σ)
```

### Constants

The semantic function `𝒜⟦ c ⟧` gives the standard interpretation of the
constant `c`. The corresponding definitions in ([Plotkin 1977]) use
case analysis, which is not supported in this Agda formalisation
(partly because it can express non-continuous functions).

```agda
  open Notation.Flat using (↑; _♯)
  open Notation.Flat.Booleans using (_⟶_,_; _==⊥_; false; true)
  open Notation.Flat.Naturals using (_+_; _∸_)
  𝒜⟦_⟧ : ℒᴬ σ → ⟪ 𝒟 σ ⟫
  𝒜⟦ tt ⟧    =  ↑ true
  𝒜⟦ ff ⟧    =  ↑ false
  𝒜⟦ ⊃ ⟧     =  λ β δ₁ δ₂ → (β ⟶ δ₁ , δ₂)
  𝒜⟦ Y ⟧     =  fix
  𝒜⟦ k n ⟧   =  ↑ n
  𝒜⟦ ⦅+1⦆ ⟧  =  (λ n → ↑ (n + 1)) ♯
  𝒜⟦ ⦅−1⦆ ⟧  =  (λ n → (↑ n ==⊥ ↑ 0) ⟶ ⊥ , ↑ (n ∸ 1)) ♯
  𝒜⟦ Z ⟧     =  (λ n → (↑ n ==⊥ ↑ 0)) ♯
```

### Terms

The semantic function `𝓐′⟦ M ⟧` is written
$\hat{\mathcal A} \llbracket M \rrbracket$ in ([Plotkin 1977]). It gives the
denotation of the term `M` as a function of the environment `ρ`.

```agda
  𝓐′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫
  𝓐′⟦ 𝑉 α i σ ⟧ ρ           =  ρ ⟦ α i σ ⟧
  𝓐′⟦ 𝐿 c ⟧ ρ               =  𝒜⟦ c ⟧
  𝓐′⟦ ⦅ M ␣ N ⦆ ⟧ ρ         =  𝓐′⟦ M ⟧ ρ (𝓐′⟦ N ⟧ ρ) 
  𝓐′⟦ ⦅λ α i σ ␣ M ⦆ ⟧ ρ x  =  𝓐′⟦ M ⟧ (ρ [ x / α i σ ]′)
```

See the [Tests] module for some examples of abstract syntax terms and
equivalence proofs.

[Scott 1993]: https://doi.org/10.1016/0304-3975(93)90095-B
[Plotkin 1977]: https://doi.org/10.1016/0304-3975(77)90044-5
[intrinsically-typed]: https://ncatlab.org/nlab/show/intrinsic+and+extrinsic+views+of+typing
[Tests]: ../Tests/index.md