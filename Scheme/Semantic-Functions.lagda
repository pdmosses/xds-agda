\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Scheme.Semantic-Functions where

open import Scheme.Domain-Notation
open import Scheme.Abstract-Syntax
open import Scheme.Domain-Equations
open import Scheme.Auxiliary-Functions

-- 7.2.3. Semantic functions

postulate 𝒦⟦_⟧ : Con → 𝐄
ℰ⟦_⟧   : Exp → 𝐔 → 𝐊 → 𝐂
ℰ*⟦_⟧  : Exp * → 𝐔 → 𝐊 → 𝐂
𝒞*⟦_⟧  : Com * → 𝐔 → 𝐂 → 𝐂

-- Definition of 𝒦 deliberately omitted.

ℰ⟦ con K ⟧ = λ ρ κ → send (𝒦⟦ K ⟧) κ

ℰ⟦ ide I ⟧ = λ ρ κ →
  hold (lookup ρ I) (single (λ ϵ →
    (misc-undefined ♯) (▻ ϵ) ⟶⊥ wrong "undefined variable" ,
      send ϵ κ))

-- Non-compositional:
-- ℰ⟦ ⦅ E₀ ␣ E* ⦆ ⟧ =
--   λ ρ κ → ℰ*⟦ permute (⟨ E₀ ⟩ § E* ) ⟧
--           ρ
--           (λ ϵ⋆ → ((λ ϵ⋆ → applicate (ϵ⋆ ↓ 1) (ϵ⋆ † 1) κ)
--                    (unpermute ϵ⋆)))

ℰ⟦ ⦅ E* ⦆ ⟧ = λ ρ κ →
  ℰ*⟦ E* ⟧ ρ (◅ λ ϵ⋆ →
    applicate (ϵ⋆ ↓ 1) (ϵ⋆ † 1) κ)

ℰ⟦ ⦅lambda␣⦅ I* ⦆ Γ* ␣ E₀ ⦆ ⟧ = λ ρ κ → ◅ λ σ → 
    (new σ ∈𝐋) ⟶⊥
        ▻ (send (◅ ( (new σ |𝐋) ,
                     (λ ϵ⋆ κ′ →
                        (# ϵ⋆ ==⊥ #′ I*) ⟶⊥
                            tievals
                              (λ α⋆ → (λ ρ′ → 𝒞*⟦ Γ* ⟧ ρ′ (ℰ⟦ E₀ ⟧ ρ′ κ′))
                                      (extends ρ I* α⋆))
                              ϵ⋆ ,
                          wrong "wrong number of arguments"
                     )
                   ) 𝐅-in-𝐄)
                κ)
          (update (new σ |𝐋) unspecified-in-𝐄 σ) ,
      ▻ (wrong "out of memory") σ
\end{code}
\clearpage
\begin{code}
ℰ⟦ ⦅lambda␣⦅ I* · I ⦆ Γ* ␣ E₀ ⦆ ⟧ = λ ρ κ → ◅ λ σ → 
    (new σ ∈𝐋) ⟶⊥
        ▻ (send (◅ ( (new σ |𝐋) ,
                     (λ ϵ⋆ κ′ →
                        (# ϵ⋆ >=⊥ #′ I*) ⟶⊥
                           tievalsrest
                              (λ α⋆ → (λ ρ′ → 𝒞*⟦ Γ* ⟧ ρ′ (ℰ⟦ E₀ ⟧ ρ′ κ′))
                              (extends ρ (I* §′ ( 1 , I )) α⋆))
                              ϵ⋆
                              (η (#′ I*)) ,
                          wrong "too few arguments"
                     )
                   ) 𝐅-in-𝐄)
                κ)
          (update (new σ |𝐋) unspecified-in-𝐄 σ) ,
      ▻ (wrong "out of memory") σ

-- Non-compositional:
-- ℰ⟦ ⦅lambda I ␣ Γ* ␣ E₀ ⦆ ⟧ = ℰ⟦ ⦅lambda ⦅ · I ⦆ Γ* ␣ E₀ ⦆ ⟧

ℰ⟦ ⦅lambda I ␣ Γ* ␣ E₀ ⦆ ⟧ = λ ρ κ → ◅ λ σ → 
    (new σ ∈𝐋) ⟶⊥
        ▻ (send (◅ ( (new σ |𝐋) ,
                     (λ ϵ⋆ κ′ →
                        tievalsrest
                          (λ α⋆ → (λ ρ′ → 𝒞*⟦ Γ* ⟧ ρ′ (ℰ⟦ E₀ ⟧ ρ′ κ′))
                                  (extends ρ (1 , I) α⋆))
                          ϵ⋆
                          (η 0))
                   ) 𝐅-in-𝐄)
                κ)
          (update (new σ |𝐋) unspecified-in-𝐄 σ) ,
      ▻ (wrong "out of memory") σ


ℰ⟦ ⦅if E₀ ␣ E₁ ␣ E₂ ⦆ ⟧ = λ ρ κ → 
  ℰ⟦ E₀ ⟧ ρ (single (λ ϵ →
    truish ϵ ⟶⊥ ℰ⟦ E₁ ⟧ ρ κ ,
      ℰ⟦ E₂ ⟧ ρ κ))

ℰ⟦ ⦅if E₀ ␣ E₁ ⦆ ⟧ = λ ρ κ → 
  ℰ⟦ E₀ ⟧ ρ (single (λ ϵ →
    truish ϵ ⟶⊥ ℰ⟦ E₁ ⟧ ρ κ ,
      send unspecified-in-𝐄 κ))

-- Here and elsewhere, any expressed value other than `undefined`
-- may be used in place of `unspecified`.
\end{code}
\clearpage
\begin{code}
ℰ⟦ ⦅set! I ␣ E ⦆ ⟧ = λ ρ κ →
  ℰ⟦ E ⟧ ρ (single (λ ϵ →
    assign (lookup ρ I) ϵ (send unspecified-in-𝐄 κ)))

-- ℰ*⟦_⟧  : Exp * → 𝐔 → 𝐊 → 𝐂

ℰ*⟦ 0 , _ ⟧  = λ ρ κ → ▻ κ ⟨⟩

ℰ*⟦ 1 , E ⟧  = ℰ⟦ E ⟧

ℰ*⟦ suc (suc n) , E , Es ⟧ = λ ρ κ →
  ℰ⟦ E ⟧ ρ (single (λ ϵ₀ →
    ℰ*⟦ suc n , Es ⟧ ρ (◅ λ ϵ⋆ →
      ▻ κ (⟨ ϵ₀ ⟩ § ϵ⋆))))

-- 𝒞*⟦_⟧  : Com * → 𝐔 → 𝐂 → 𝐂

𝒞*⟦ 0 , _ ⟧ =  λ ρ θ → θ

𝒞*⟦ 1 , Γ ⟧ = λ ρ θ → ℰ⟦ Γ ⟧ ρ (◅ λ ϵ⋆ → θ)

𝒞*⟦ suc (suc n) , Γ , Γs ⟧ = λ ρ θ →
  ℰ⟦ Γ ⟧ ρ (◅ λ ϵ⋆ →
    𝒞*⟦ suc n , Γs ⟧ ρ θ)

\end{code} 