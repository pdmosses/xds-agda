# Semantic Functions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Semantic-Functions where

open import Notation
open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
open import Scm.Auxiliary-Functions

𝒦⟦_⟧    : ⟪ Con →ˢ 𝐄 ⟫
ℰ⟦_⟧    : ⟪ Exp →ˢ 𝐔 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
ℰ⋆⟦_⟧  : ⟪ Exp⋆ →ˢ 𝐔 →ᶜ (𝐄⋆ →ᶜ 𝐂) →ᶜ 𝐂 ⟫

ℬ⟦_⟧    : ⟪ Body →ˢ 𝐔 →ᶜ (𝐔 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
ℬ⁺⟦_⟧   : ⟪ Body⁺ →ˢ 𝐔 →ᶜ (𝐔 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
𝒫⟦_⟧    : ⟪ Prog →ˢ 𝐀 ⟫
```

## Constants

```agda
𝒦⟦ int Z ⟧  = η Z 𝐑-in-𝐄
𝒦⟦ #t ⟧     = η true 𝐓-in-𝐄
𝒦⟦ #f ⟧     = η false 𝐓-in-𝐄
```

## Expressions

```agda
ℰ⟦ con K ⟧ ρ κ = κ (𝒦⟦ K ⟧)

ℰ⟦ ide I ⟧ ρ κ = hold (ρ I) κ

ℰ⟦ ⦅ E ␣ E⋆ ⦆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ →
    ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ →
      (ϵ |-𝐅) ϵ⋆ κ))

ℰ⟦ ⦅lambda I ␣ E ⦆ ⟧ ρ κ =
  κ (  (λ ϵ⋆ κ′ →
          list ϵ⋆ (λ ϵ → 
            alloc ϵ (λ α →
              ℰ⟦ E ⟧ (ρ [ α / I ]) κ′))
       ) 𝐅-in-𝐄)

ℰ⟦ ⦅if E ␣ E₁ ␣ E₂ ⦆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ →
    truish ϵ ⟶ ℰ⟦ E₁ ⟧ ρ κ , ℰ⟦ E₂ ⟧ ρ κ)

ℰ⟦ ⦅set! I ␣ E ⦆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ →
    assign (ρ I) ϵ (
      κ (η unspecified 𝐌-in-𝐄)))
```

## Expression Sequences

```agda
ℰ⋆⟦ ␣␣␣ ⟧ ρ κ = κ ⟨⟩

ℰ⋆⟦ E ␣␣ E⋆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ →
    ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ →
      κ (⟨ ϵ ⟩ § ϵ⋆)))
```

## Bodies

```agda
ℬ⟦ ␣␣ E ⟧ ρ κ = ℰ⟦ E ⟧ ρ (λ ϵ → κ ρ)

ℬ⟦ ⦅define I ␣ E ⦆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ → (ρ I ==ᴸ unknown) ⟶ 
                      alloc ϵ (λ α → κ (ρ [ α / I ])),
                    assign (ρ I) ϵ (κ ρ))

ℬ⟦ ⦅begin B⁺ ⦆ ⟧ ρ κ = ℬ⁺⟦ B⁺ ⟧ ρ κ
```

## Body Sequences

```agda
ℬ⁺⟦ ␣␣ B ⟧ ρ κ = ℬ⟦ B ⟧ ρ κ

ℬ⁺⟦ B ␣␣ B⁺ ⟧ ρ κ = ℬ⟦ B ⟧ ρ (λ ρ′ → ℬ⁺⟦ B⁺ ⟧ ρ′ κ)
```

## Programs

```agda
𝒫⟦ ␣␣␣ ⟧ = finished initial-store

𝒫⟦ ␣␣ B⁺ ⟧ = ℬ⁺⟦ B⁺ ⟧ initial-env (λ ρ → finished) initial-store
```