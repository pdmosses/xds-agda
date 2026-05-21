# Semantic functions

The notation `ρ ⟦ α i σ ⟧` gives the value of the variable `α i σ` in `ρ` by
applying `ρ σ` to the variable.
```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.PCF.Semantic-Functions where

open import Notation
open import Examples.PCF.Abstract-Syntax
open import Examples.PCF.Domain-Equations

_⟦_⟧ : Env → Vars σ → ⟪ 𝒟 σ ⟫     -- typed variable denotations
ρ ⟦ α i σ ⟧ = ρ σ (α i σ)
```
The semantic function `𝒜⟦ c ⟧` gives the standard interpretation of the
constant `c`. The corresponding definitions in [(Plotkin1977LCP)] use
case analysis on the domain `𝒟 ι`, which our Agda embedding does not support
(partly because it can express non-continuous functions).
```agda

open Notation.Flat using (↑; _♯)
open Notation.Flat.Booleans using (_⟶_,_; _==⊥_; false; true)
open Notation.Flat.Naturals using (_+_; _-_)

𝒜⟦_⟧ : ℒᴬ σ → ⟪ 𝒟 σ ⟫             -- typed constant denotations
𝒜⟦ tt ⟧    =  ↑ true
𝒜⟦ ff ⟧    =  ↑ false
𝒜⟦ ⊃ ⟧     =  λ β δ₁ δ₂ → (β ⟶ δ₁ , δ₂)
𝒜⟦ Y ⟧     =  fix
𝒜⟦ k n ⟧   =  ↑ n
𝒜⟦ ⦅+1⦆ ⟧  =  (λ n → ↑ (n + 1)) ♯
𝒜⟦ ⦅−1⦆ ⟧  =  (λ n → ↑ (n ==ᴺ 0) ⟶ ⊥ , ↑ (n - 1)) ♯
𝒜⟦ Z ⟧     =  (λ n → ↑ (n ==ᴺ 0)) ♯
```
The semantic function `𝒜′⟦ M ⟧` is written
$\hat{\mathcal A} \llbracket M \rrbracket$ in [(Plotkin1977LCP)]. It gives the
denotation of the term `M` as a function of the environment `ρ`.
```agda
𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫  -- typed term denotations
𝒜′⟦ 𝑉 α i σ ⟧ ρ           =  ρ ⟦ α i σ ⟧
𝒜′⟦ 𝐿 c ⟧ ρ               =  𝒜⟦ c ⟧
𝒜′⟦ ⦅ M ␣ N ⦆ ⟧ ρ         =  𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
𝒜′⟦ ⦅λ α i σ ␣ M ⦆ ⟧ ρ x  =  𝒜′⟦ M ⟧ (ρ [ x / α i σ ]′)
```
Comparison with Plotkin's original definition of PCF [(Plotkin1977LCP)] confirms
the directness of our Agda embedding.

[(Plotkin1977LCP)]: https://doi.org/10.1016/0304-3975(77)90044-5