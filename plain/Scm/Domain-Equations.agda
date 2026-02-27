
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Domain-Equations where
  open import Scm.Abstract-Syntax using (Ide; Int)
  import Notation
  open Notation.Domains using (Domain; ⟪_⟫)
  open Notation.Functions using (_→ᶜ_; _→ˢ_)
  open Notation.Flat using (_+⊥)
  open Notation.Flat.Booleans using (Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥)
  open Notation.Sums using (_≳_↦_)
  open Notation.Products using (_×_)
  open Notation.Products.Sequences using (_⋆)

  postulate Loc : Set
  𝐋  =  Loc +⊥
  𝐍  =  Nat⊥
  𝐓  =  Bool⊥
  𝐑  =  Int +⊥
  𝐏  =  𝐋 × 𝐋
  𝐔  =  Ide →ˢ 𝐋
  data Misc : Set where
     null unallocated undefined unspecified : Misc
  𝐌  =  Misc +⊥

  postulate 𝐄 : Domain
  𝐒  =  𝐋 →ᶜ 𝐄
  postulate 𝐀 : Domain
  𝐂  =  𝐒 →ᶜ 𝐀
  𝐅  =  𝐄 ⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂

  postulate instance
    E+=T  : 𝐄 ≳ 1 ↦ 𝐓
    E+=R  : 𝐄 ≳ 2 ↦ 𝐑
    E+=P  : 𝐄 ≳ 3 ↦ 𝐏
    E+=M  : 𝐄 ≳ 4 ↦ 𝐌
    E+=F  : 𝐄 ≳ 5 ↦ 𝐅

  variable
    α : ⟪ 𝐋 ⟫;  ρ : ⟪ 𝐔 ⟫;  μ  : ⟪ 𝐌 ⟫;   ϵ : ⟪ 𝐄 ⟫
    σ : ⟪ 𝐒 ⟫;  θ : ⟪ 𝐂 ⟫;  ϵ⋆ : ⟪ 𝐄 ⋆ ⟫;  φ : ⟪ 𝐅 ⟫
