{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.PCF.Semantic-Functions where

open import Notation
open import Examples.PCF.Abstract-Syntax
open import Examples.PCF.Domain-Equations

_⟦_⟧ : Env → Vars σ → ⟪ 𝒟 σ ⟫     -- typed variable denotations
ρ ⟦ α i σ ⟧ = ρ σ (α i σ)


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

𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫  -- typed term denotations
𝒜′⟦ 𝑉 α i σ ⟧ ρ           =  ρ ⟦ α i σ ⟧
𝒜′⟦ 𝐿 c ⟧ ρ               =  𝒜⟦ c ⟧
𝒜′⟦ ⦅ M ␣ N ⦆ ⟧ ρ         =  𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
𝒜′⟦ ⦅λ α i σ ␣ M ⦆ ⟧ ρ x  =  𝒜′⟦ M ⟧ (ρ [ x / α i σ ]′)