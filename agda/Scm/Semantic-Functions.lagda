\begin{code}
module Scm.Semantic-Functions where

open import Scm.Notation
open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
open import Scm.Auxiliary-Functions

𝒦⟦_⟧    : Con → 𝐄
ℰ⟦_⟧    : Exp → 𝐔 → (𝐄 → 𝐂) → 𝐂
ℰ⋆⟦_⟧  : Exp⋆ → 𝐔 → (𝐄⋆ → 𝐂) → 𝐂

ℬ⟦_⟧    : Body → 𝐔 → (𝐔 → 𝐂) → 𝐂
ℬ⁺⟦_⟧   : Body⁺ → 𝐔 → (𝐔 → 𝐂) → 𝐂
𝒫⟦_⟧    : Prog → 𝐀

-- Constant denotations 𝒦⟦ K ⟧ : 𝐄

𝒦⟦ int Z ⟧  = η Z 𝐑-in-𝐄
𝒦⟦ #t ⟧     = η true 𝐓-in-𝐄
𝒦⟦ #f ⟧     = η false 𝐓-in-𝐄

-- Expression denotations

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

-- ℰ⋆⟦_⟧  : Exp⋆ → 𝐔 → (𝐄⋆ → 𝐂) → 𝐂

ℰ⋆⟦ ␣␣␣ ⟧ ρ κ = κ ⟨⟩

ℰ⋆⟦ E ␣␣ E⋆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ →
    ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ →
      κ (⟨ ϵ ⟩ § ϵ⋆)))
\end{code}
\iflatex
\clearpage
\fi
\begin{code}
-- Body denotations ℬ⟦ B ⟧ : 𝐔 → (𝐔 → 𝐂) → 𝐂

ℬ⟦ ␣␣ E ⟧ ρ κ = ℰ⟦ E ⟧ ρ (λ ϵ → κ ρ)

ℬ⟦ ⦅define I ␣ E ⦆ ⟧ ρ κ =
  ℰ⟦ E ⟧ ρ (λ ϵ → (ρ I ==ᴸ unknown) ⟶ 
                      alloc ϵ (λ α → κ (ρ [ α / I ])),
                    assign (ρ I) ϵ (κ ρ))

ℬ⟦ ⦅begin B⁺ ⦆ ⟧ ρ κ = ℬ⁺⟦ B⁺ ⟧ ρ κ

-- Body sequence denotations ℬ⁺⟦ B⁺ ⟧ : 𝐔 → (𝐔 → 𝐂) → 𝐂

ℬ⁺⟦ ␣␣ B ⟧ ρ κ = ℬ⟦ B ⟧ ρ κ

ℬ⁺⟦ B ␣␣ B⁺ ⟧ ρ κ = ℬ⟦ B ⟧ ρ (λ ρ′ → ℬ⁺⟦ B⁺ ⟧ ρ′ κ)

-- Program denotations 𝒫⟦ Π ⟧ : 𝐀

𝒫⟦ ␣␣␣ ⟧ = finished initial-store

𝒫⟦ ␣␣ B⁺ ⟧ = ℬ⁺⟦ B⁺ ⟧ initial-env (λ ρ → finished) initial-store
\end{code}