\begin{code}

module Scheme.Auxiliary-Functions where

open import Scheme.Domain-Notation
open import Scheme.Domain-Equations
open import Scheme.Abstract-Syntax
  using (Ide)

-- 7.2.4. Auxiliary functions

postulate _==ᴵ_ : Ide → Ide → Bool

_[_/_] : 𝐔 → 𝐋 → Ide → 𝐔
-- ρ [ α / I ] overrides ρ with the binding of I to α
ρ [ α / I ] = ◅ λ I′ → if I ==ᴵ I′ then α else ▻ ρ I′

lookup : 𝐔 → Ide → 𝐋
lookup = λ ρ I → ▻ ρ I

extends : 𝐔 → Ide * → 𝐋 ⋆ → 𝐔
extends = fix λ extends′ →
  λ ρ I* α⋆ →
    η (#′ I* == 0) ⟶⊥ ρ ,
      ( ( ( (λ I → λ I*′ →
              extends′ (ρ [ (α⋆ ↓ 1) / I ]) I*′ (α⋆ † 1)) ♯)
          (I* ↓′ 1)) ♯) (I* †′ 1)

postulate
  wrong : String → 𝐂
  -- wrong : 𝐗 → 𝐂 -- implementation-dependent

send : 𝐄 → 𝐊 → 𝐂
send = λ ϵ κ → ▻ κ ⟨ ϵ ⟩

single : (𝐄 → 𝐂) → 𝐊
single =
  λ ψ → ◅ λ ϵ⋆ → 
    (# ϵ⋆ ==⊥ 1) ⟶⊥ ψ (ϵ⋆ ↓ 1) ,
      wrong "wrong number of return values"

postulate
  new : 𝐒 → 𝕃 (𝐋 + 𝐗)
-- new : 𝐒 → (𝐋 + {error}) -- implementation-dependent
-- unclear why R5RS uses an undeclared value instead of 𝐗

hold : 𝐋 → 𝐊 → 𝐂
hold = λ α κ → ◅ λ σ → ▻ (send (▻ σ α ↓1) κ) σ

-- assign : 𝐋 → 𝐄 → 𝐂 → 𝐂
-- assign = λ α ϵ θ σ → θ (update α ϵ σ)
-- forward reference to update

postulate
  _==ᴸ_ : 𝐋 → 𝐋 → 𝐓

-- R5RS and [Stoy] explain _[_/_] only in connection with environments
_[_/_]′ : 𝐒 → (𝐄 × 𝐓) → 𝐋 → 𝐒
σ [ z / α ]′ = ◅ λ α′ → (α ==ᴸ α′) ⟶⊥ z , ▻ σ α′

update : 𝐋 → 𝐄 → 𝐒 → 𝐒
update = λ α ϵ σ → σ [ (ϵ , η true) / α ]′

assign : 𝐋 → 𝐄 → 𝐂 → 𝐂
assign = λ α ϵ θ → ◅ λ σ → ▻ θ (update α ϵ σ)

tievals : (𝐋 ⋆ → 𝐂) → 𝐄 ⋆ → 𝐂
tievals = fix λ tievals′ →
  λ ψ ϵ⋆ → ◅ λ σ →
    (# ϵ⋆ ==⊥ 0) ⟶⊥ ▻ (ψ ⟨⟩) σ ,
      ((new σ ∈𝐋) ⟶⊥
          ▻  (tievals′ (λ α⋆ → ψ (⟨ new σ |𝐋 ⟩ § α⋆)) (ϵ⋆ † 1))
             (update (new σ |𝐋) (ϵ⋆ ↓ 1) σ) ,
        ▻ (wrong "out of memory") σ )

list : 𝐄 ⋆ → 𝐊 → 𝐂
-- Add declarations:
dropfirst : 𝐄 ⋆ → 𝐍 → 𝐄 ⋆
takefirst : 𝐄 ⋆ → 𝐍 → 𝐄 ⋆

tievalsrest : (𝐋 ⋆ → 𝐂) → 𝐄 ⋆ → 𝐍 → 𝐂
tievalsrest =
  λ ψ ϵ⋆ ν → list  (dropfirst ϵ⋆ ν)
                   (single (λ ϵ → tievals ψ ((takefirst ϵ⋆ ν) § ⟨ ϵ ⟩)))

dropfirst = fix λ dropfirst′ →
  λ ϵ⋆ ν →
    (ν ==⊥ 0) ⟶⊥ ϵ⋆ ,
      dropfirst′ (ϵ⋆ † 1) (((η ∘ pred) ♯) ν)

takefirst = fix λ takefirst′ →
  λ ϵ⋆ ν →
    (ν ==⊥ 0) ⟶⊥ ⟨⟩ ,
      ( ⟨ ϵ⋆ ↓ 1 ⟩ § (takefirst′ (ϵ⋆ † 1) (((η ∘ pred) ♯) ν)) )

truish : 𝐄 → 𝐓
-- truish = λ ϵ → ϵ = false ⟶⊥ false , true
truish = λ ϵ → (misc-false ♯) (▻ ϵ) ⟶⊥ (η false) , (η true) where
  misc-false : (𝐐 + 𝐇 + 𝐑 + 𝐄𝐩 + 𝐄𝐯 + 𝐄𝐬 + 𝐌 + 𝐅) → 𝕃 Bool
  misc-false (inj-𝐌 μ)  = ((λ { false → η true ; _ → η false }) ♯) (μ)
  misc-false (inj₁ _)   = η false
  misc-false (inj₂ _)   = η false

-- Added:
misc-undefined : (𝐐 + 𝐇 + 𝐑 + 𝐄𝐩 + 𝐄𝐯 + 𝐄𝐬 + 𝐌 + 𝐅) → 𝕃 Bool
misc-undefined (inj-𝐌 μ)  = ((λ { undefined → η true ; _ → η false }) ♯) (μ)
misc-undefined (inj₁ _)    = η false
misc-undefined (inj₂ _)    = η false

-- permute    : Exp * → Exp *  -- implementation-dependent
-- unpermute  : 𝐄 ⋆ → 𝐄 ⋆      -- inverse of permute

applicate : 𝐄 → 𝐄 ⋆ → 𝐊 → 𝐂
applicate =
  λ ϵ ϵ⋆ κ →
    (ϵ ∈𝐅) ⟶⊥ (▻ (ϵ |𝐅) ↓2) ϵ⋆ κ ,
      wrong "bad procedure"

onearg : (𝐄 → 𝐊 → 𝐂) → (𝐄 ⋆ → 𝐊 → 𝐂)
onearg =
  λ ζ ϵ⋆ κ →
    (# ϵ⋆ ==⊥ 1) ⟶⊥ ζ (ϵ⋆ ↓ 1) κ ,
      wrong "wrong number of arguments"

twoarg : (𝐄 → 𝐄 → 𝐊 → 𝐂) → (𝐄 ⋆ → 𝐊 → 𝐂)
twoarg =
  λ ζ ϵ⋆ κ →
    (# ϵ⋆ ==⊥ 2) ⟶⊥ ζ (ϵ⋆ ↓ 1) (ϵ⋆ ↓ 2) κ ,
      wrong "wrong number of arguments"

cons : 𝐄 ⋆ → 𝐊 → 𝐂

-- list : 𝐄 ⋆ → 𝐊 → 𝐂
list = fix λ list′ →
  λ ϵ⋆ κ →
    (# ϵ⋆ ==⊥ 0) ⟶⊥ send (◅ (η (inj-𝐌 (η null)))) κ ,
      list′ (ϵ⋆ † 1) (single (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ))

-- cons : 𝐄 ⋆ → 𝐊 → 𝐂
cons = twoarg
  λ ϵ₁ ϵ₂ κ → ◅ λ σ →
    (new σ ∈𝐋) ⟶⊥
        (λ σ′ → (new σ′ ∈𝐋) ⟶⊥
                    ▻ (send ((new σ |𝐋 , new σ′ |𝐋 , (η true)) 𝐄𝐩-in-𝐄) κ)
                      (update (new σ′ |𝐋) ϵ₂ σ′) ,
                  ▻ (wrong "out of memory") σ′)
        (update (new σ |𝐋) ϵ₁ σ) ,
      ▻ (wrong "out of memory") σ
\end{code} 