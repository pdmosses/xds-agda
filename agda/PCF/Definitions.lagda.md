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

```agda
  data Types : Set where ι o : Types ; _⇒_  : Types → Types → Types
  infixr 1 _⇒_
  variable σ τ : Types
```

### Variables

A variable in `𝒱 σ` is written `α i σ`; in ([Plotkin 1977]) variables are
written $\alpha_i^\sigma$, and the set of variables is not named.

The argument `i` merely distinguishes between variables – it is *not* a De Bruin
index.

```agda
  data 𝒱 : Types → Set where α : Nat → (σ : Types) → 𝒱 σ
  variable i : Nat
```

### Constants

The PCF language `ℒ` includes `ℒᴬ`, the set of *standard* constants for arithmetic,
written $\mathcal L_A$ in ([Plotkin 1977]).

```agda
  data ℒᴬ : Types → Set where
    tt ff    : ℒᴬ o
    ⊃        : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)
    Y        : ℒᴬ ((σ ⇒ σ) ⇒ σ)
    k        : Nat → ℒᴬ ι
    +1′ -1′  : ℒᴬ (ι ⇒ ι)
    Z        : ℒᴬ (ι ⇒ o)
  variable c : ℒᴬ σ
```

### Terms

The terms of PCF are *[intrinsically-typed]*: all terms are well-typed.

The term constructor `𝑉` below merely includes variables in terms;
the constructor `𝐿` includes constants.

Agda does not support the use of the conventional notation `λ _ . _`
for the abstract syntax of lambda abstraction terms, nor juxtaposition `_ _`
for the abstract syntax of application terms. The Unicode symbols `ƛ` and `␣`
allow abstract syntax terms to be written reasonably suggestively.

```agda
  data ℒ : Types → Set where
    𝑉     : 𝒱 σ → ℒ σ
    𝐿     : ℒᴬ σ → ℒ σ
    _␣_   : ℒ (σ ⇒ τ) → ℒ σ → ℒ τ
    ƛ_␣_  : 𝒱 σ → ℒ τ → ℒ (σ ⇒ τ)
  infixl 20 _␣_
  variable M N : ℒ σ
```

## Domain equations

The domains `𝒟 σ` form a *standard collection of domains for arithmetic*
in PCF, written $\mathcal D_\sigma$ in ([Plotkin 1977]). As PCF is a
simply-typed language, the domain equations do not involve recursion.

```agda
module Domain-Equations where
  open Abstract-Syntax
  open Notation.Flat.Booleans using (Bool; Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥; eq⊥Nat⊥)
  𝒟 : Types → Domain
  𝒟 ι        =  Nat⊥
  𝒟 o        =  Bool⊥
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ
  variable x y z : ⟪ 𝒟 σ ⟫
```

Environments `ρ` are type-preserving maps from variables to values. They are
naturally modeled by a dependent type: `Env σ` consists of type-preserving maps
from variables in `𝒱 σ` to their values in the carrier of the domain `𝒟 σ`.
The environment `ρ⊥` maps all variables to `⊥`.

```agda
  Env = (σ : Types) → 𝒱 σ → ⟪ 𝒟 σ ⟫
  variable ρ : Env
  ρ⊥ : Env
  ρ⊥ = λ _ → λ _ → ⊥
```

Extension or overriding environments requires instances of the equality tests
for both variables and types. The definition of the latter is somewhat tedious
in Agda.

```agda
  open Notation.Updates using (Eq; _==_; EqMaybe; _==?_; just; nothing; refl; _[_/_])
  _==ⱽ_ : 𝒱 σ → 𝒱 σ → Bool
  α i σ ==ⱽ α i′ σ  =  (i ≡ᵇ i′)
  instance
    eqV : Eq (𝒱 σ)
    _==_ {{eqV}} = _==ⱽ_
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
  _⟦_⟧ : ⟪ Env →ˢ 𝒱 σ →ˢ 𝒟 σ ⟫
  ρ ⟦ α i σ ⟧ = ρ σ (α i σ)
```

### Constants

The semantic function `𝒜⟦ c ⟧` gives the standard interpretation of the
constant `c`. The corresponding definitions in ([Plotkin 1977]) use
case analysis, which is not supported in this Agda formalisation
(partly because it could be used to define non-monotonic functions).

```agda
  open Notation.Flat using (⌊_⌋; _♯)
  open Notation.Flat.Booleans using (_⟶_,_; _==⊥_; false; true)
  𝒜⟦_⟧ : ℒᴬ σ → ⟪ 𝒟 σ ⟫
  𝒜⟦ tt   ⟧ =  ⌊ true ⌋
  𝒜⟦ ff   ⟧ =  ⌊ false ⌋
  𝒜⟦ ⊃    ⟧ =  λ β δ₁ δ₂ → (β ⟶ δ₁ , δ₂)
  𝒜⟦ Y    ⟧ =  fix
  𝒜⟦ k n  ⟧ =  ⌊ n ⌋
  𝒜⟦ +1′  ⟧ =  (λ n → ⌊ n + 1 ⌋) ♯
  𝒜⟦ -1′  ⟧ =  (λ n → (⌊ n ⌋ ==⊥ ⌊ 0 ⌋) ⟶ ⊥ , ⌊ n ∸ 1 ⌋) ♯
  𝒜⟦ Z    ⟧ =  (λ n → (⌊ n ⌋ ==⊥ ⌊ 0 ⌋)) ♯
```

### Terms

The semantic function `𝓐′⟦ M ⟧` is written
$\hat{\mathcal A} \llbracket M \rrbracket$ in ([Plotkin 1977]). It gives the
denotation of the term `M` as a function of the environment `ρ`.

The notation `f [ y / x ]′` is declared as syntax for `extend-map f x y`;
Agda does not support references to the declared syntax when opening modules.

```agda
  open Notation.Updates using (_[_/_]; extend-map)
  𝓐′⟦_⟧ : ℒ σ → ⟪ Env →ˢ 𝒟 σ ⟫
  𝓐′⟦ 𝑉 (α i σ)    ⟧ ρ    =  ρ ⟦ α i σ ⟧
  𝓐′⟦ 𝐿 c          ⟧ ρ    =  𝒜⟦ c ⟧
  𝓐′⟦ M ␣ N        ⟧ ρ    =  𝓐′⟦ M ⟧ ρ (𝓐′⟦ N ⟧ ρ) 
  𝓐′⟦ ƛ α i σ ␣ M  ⟧ ρ x  =  𝓐′⟦ M ⟧ (ρ [ ρ σ [ x / α i σ ] / σ ]′)
```

[Scott 1993]: https://doi.org/10.1016/0304-3975(93)90095-B
[Plotkin 1977]: https://doi.org/10.1016/0304-3975(77)90044-5
[intrinsically-typed]: https://ncatlab.org/nlab/show/intrinsic+and+extrinsic+views+of+typing