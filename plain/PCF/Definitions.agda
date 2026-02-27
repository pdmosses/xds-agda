
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Definitions where
open import Notation


module Abstract-Syntax where


  data Types  : Set where
    ι o       : Types
    _⇒_       : Types → Types → Types
  infixr 1 _⇒_
  variable σ τ : Types


  open import Data.Nat.Base renaming (ℕ to Nat) using () public
  data Vars   : Types → Set where
    α         : Nat → (σ : Types) → Vars σ
  variable i  : Nat


  data ℒᴬ     : Types → Set where
    tt ff     : ℒᴬ o
    ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)
    Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)
    k         : Nat → ℒᴬ ι
    ⦅+1⦆      : ℒᴬ (ι ⇒ ι)
    ⦅−1⦆      : ℒᴬ (ι ⇒ ι)
    Z         : ℒᴬ (ι ⇒ o)
  variable c  : ℒᴬ σ


  data Terms  : Types → Set where
    𝑉_        : Vars σ → Terms σ
    𝐿_        : ℒᴬ σ → Terms σ
    ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ
    ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)
  variable M N : Terms σ


module Domain-Equations where
  open Abstract-Syntax
  open Notation.Flat.Booleans using (Bool; Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥; eq⊥Nat⊥)
  𝒟 : Types → Domain
  𝒟 ι        = Nat⊥
  𝒟 o        = Bool⊥
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ
  variable x y z : ⟪ 𝒟 σ ⟫


  Env = (σ : Types) → ⟪ Vars σ →ˢ 𝒟 σ ⟫
  variable ρ : Env
  ρ⊥ : Env
  ρ⊥ = λ _ → λ _ → ⊥


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


  _[_/_]′ : Env → ⟪ 𝒟 σ ⟫ → Vars σ → Env
  _[_/_]′ {σ} ρ x v = ρ [ σ ← ρ σ [ x / v ] ]


module Semantic-Functions where
  open Abstract-Syntax
  open Domain-Equations


  _⟦_⟧ : Env → Vars σ → ⟪ 𝒟 σ ⟫
  ρ ⟦ α i σ ⟧ = ρ σ (α i σ)


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


  𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫
  𝒜′⟦ 𝑉 α i σ ⟧ ρ           =  ρ ⟦ α i σ ⟧
  𝒜′⟦ 𝐿 c ⟧ ρ               =  𝒜⟦ c ⟧
  𝒜′⟦ ⦅ M ␣ N ⦆ ⟧ ρ         =  𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
  𝒜′⟦ ⦅λ α i σ ␣ M ⦆ ⟧ ρ x  =  𝒜′⟦ M ⟧ (ρ [ x / α i σ ]′)
