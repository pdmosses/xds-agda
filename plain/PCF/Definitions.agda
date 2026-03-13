
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Definitions where

open import Notation

module Abstract-Syntax where

  data Types  : Set where                          -- type terms
    ι         : Types                              -- individuals
    o         : Types                              -- truth-values
    _⇒_       : Types → Types → Types              -- functions
  infixr 1 _⇒_
  variable σ τ : Types

  open import Agda.Builtin.Nat public using (Nat)
  data Vars   : Types → Set where                  -- typed variables
    α         : Nat → (σ : Types) → Vars σ         -- α i σ is a variable of type σ
  variable i  : Nat

  data ℒᴬ     : Types → Set where                  -- typed constants
    tt        : ℒᴬ o                               -- true
    ff        : ℒᴬ o                               -- false
    ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)                 -- conditional
    Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)                   -- fixed point
    k         : Nat → ℒᴬ ι                         -- numerals
    ⦅+1⦆      : ℒᴬ (ι ⇒ ι)                         -- successor
    ⦅−1⦆      : ℒᴬ (ι ⇒ ι)                         -- predecessor
    Z         : ℒᴬ (ι ⇒ o)                         -- zero test
  variable c  : ℒᴬ σ

  data Terms  : Types → Set where                  -- typed terms
    𝑉_        : Vars σ → Terms σ                   -- variable
    𝐿_        : ℒᴬ σ → Terms σ                     -- constant
    ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ  -- function application
    ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)   -- function abstraction
  variable M N : Terms σ

module Domain-Equations where

  open Abstract-Syntax
  open Notation.Flat.Booleans using (Bool; Bool⊥)
  open Notation.Flat.Naturals using (Nat⊥; eqNat)
  𝒟 : Types → Domain       -- standard domains
  𝒟 ι        = Nat⊥        -- natural numbers
  𝒟 o        = Bool⊥       -- truth-values
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ  -- functions
  variable x y z : ⟪ 𝒟 σ ⟫

  Env = (σ : Types) → ⟪ Vars σ →ˢ 𝒟 σ ⟫  -- typed environments
  variable ρ : Env
  ρ⊥ : Env                               -- initial environment
  ρ⊥ _ _ = ⊥

  open Notation.Flat.Booleans using (Eq; _==_)
  open Notation.Updates using (_[_/_])
  _==ⱽ_ : Vars σ → Vars σ → Bool
  open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
  (α i σ ==ⱽ α i′ σ)  =  (i ==ᴺ i′)
  instance
    eqV : Eq (Vars σ)
    _==_ {{eqV}} = _==ⱽ_
  open Notation.Updates using (MaybeEq; _==?_; just; nothing; refl; _[_←_])
  instance
    eqT : MaybeEq Types
    eqT ._==?_ ι ι = just refl
    eqT ._==?_ o o = just refl
    eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁) with σ ==? σ₁  | τ ==? τ₁
    eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | just refl | just refl = just refl
    eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | _         | _         = nothing
    eqT ._==?_ _ _ = nothing

  _[_/_]′ : Env → ⟪ 𝒟 σ ⟫ → Vars σ → Env
  -- ρ [ v / x ]′ maps x to v, and other x′ to ρ x′
  _[_/_]′ {σ} ρ x v = ρ [ σ ← ρ σ [ x / v ] ]

module Semantic-Functions where

  open Abstract-Syntax
  open Domain-Equations

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
