# Semantic Functions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Semantic-Functions where

  open import Scm.Abstract-Syntax
  open import Scm.Domain-Equations
  open import Scm.Auxiliary-Functions
  import Notation
  open Notation.Domains using (⟪_⟫)
  open Notation.Functions using (_→ᶜ_; _→ˢ_)
  open Notation.Flat using (↑)
  open Notation.Flat.Booleans using (_⟶_,_; _==⊥_; true; false)
  open Notation.Sums using (_in⊥_; _|⊥_)
  open Notation.Products.Sequences using (_⋆; ⟨⟩; ⟨_⟩; _§_)
  open Notation.Updates using (_[_/_])
```

## Constants and expressions

```agda
  𝒦⟦_⟧   :  ⟪ Con →ˢ 𝐄 ⟫                      -- constant denotations
  ℰ⟦_⟧   :  ⟪ Exp →ˢ 𝐔 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫     -- expression denotations
  ℰ⋆⟦_⟧  :  ⟪ Exp⋆ →ˢ 𝐔 →ᶜ (𝐄 ⋆ →ᶜ 𝐂) →ᶜ 𝐂 ⟫  -- sequence denotations

  𝒦⟦ int Z ⟧  = ↑ Z in⊥ 𝐄
  𝒦⟦ #t ⟧     = ↑ true in⊥ 𝐄
  𝒦⟦ #f ⟧     = ↑ false in⊥ 𝐄

  ℰ⟦ con K ⟧ ρ κ =
    κ (𝒦⟦ K ⟧)
  ℰ⟦ ide I ⟧ ρ κ =
    hold (ρ I) κ
  ℰ⟦ ⦅ E ␣ E⋆ ⦆ ⟧ ρ κ =
    ℰ⟦ E ⟧ ρ (λ ϵ → ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ → (ϵ |⊥ 𝐅) ϵ⋆ κ))
  ℰ⟦ ⦅lambda I ␣ E ⦆ ⟧ ρ κ =
    κ ( (λ ϵ⋆ κ′ → list ϵ⋆ (λ ϵ → alloc ϵ (λ α → ℰ⟦ E ⟧ (ρ [ α / I ]) κ′))) in⊥ 𝐄 )
  ℰ⟦ ⦅if E ␣ E₁ ␣ E₂ ⦆ ⟧ ρ κ =
    ℰ⟦ E ⟧ ρ (λ ϵ → truish ϵ ⟶ ℰ⟦ E₁ ⟧ ρ κ , ℰ⟦ E₂ ⟧ ρ κ)
  ℰ⟦ ⦅set! I ␣ E ⦆ ⟧ ρ κ =
    ℰ⟦ E ⟧ ρ (λ ϵ → assign (ρ I) ϵ (κ (↑ unspecified in⊥ 𝐄)))

  ℰ⋆⟦ ␣␣␣ ⟧ ρ κ      = κ ⟨⟩
  ℰ⋆⟦ E ␣␣ E⋆ ⟧ ρ κ  = ℰ⟦ E ⟧ ρ (λ ϵ → ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ → κ (⟨ ϵ ⟩ § ϵ⋆)))
```

## Definitions and programs

```agda
  ℬ⟦_⟧   :  ⟪ Body →ˢ 𝐔 →ᶜ (𝐔 →ᶜ 𝐂) →ᶜ 𝐂 ⟫    -- body denotations
  ℬ⁺⟦_⟧  :  ⟪ Body⁺ →ˢ 𝐔 →ᶜ (𝐔 →ᶜ 𝐂) →ᶜ 𝐂 ⟫   -- sequence denotations
  𝒫⟦_⟧   :  ⟪ Prog →ˢ 𝐀 ⟫                     -- program execution answers

  ℬ⟦ ␣␣ E ⟧ ρ κ =
    ℰ⟦ E ⟧ ρ (λ ϵ → κ ρ)
  ℬ⟦ ⦅define I ␣ E ⦆ ⟧ ρ κ =
    ℰ⟦ E ⟧ ρ (λ ϵ → (ρ I ==⊥ ↑ unknown) ⟶ alloc ϵ (λ α → κ (ρ [ α / I ])) ,
    assign (ρ I) ϵ (κ ρ))
  ℬ⟦ ⦅begin B⁺ ⦆ ⟧ ρ κ =
    ℬ⁺⟦ B⁺ ⟧ ρ κ

  ℬ⁺⟦ ␣␣ B ⟧ ρ κ =
    ℬ⟦ B ⟧ ρ κ
  ℬ⁺⟦ B ␣␣ B⁺ ⟧ ρ κ =
    ℬ⟦ B ⟧ ρ (λ ρ′ → ℬ⁺⟦ B⁺ ⟧ ρ′ κ)

  𝒫⟦ ␣␣␣ ⟧    = finished initial-store
  𝒫⟦ ␣␣ B⁺ ⟧  = ℬ⁺⟦ B⁺ ⟧ initial-env (λ ρ → finished) initial-store
```