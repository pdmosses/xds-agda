\begin{code}
module Scheme.Domain-Equations where

open import Scheme.Domain-Notation
open import Scheme.Abstract-Syntax
  using (Ide)

-- 7.2.2. Domain equations

-- Domain definitions

postulate Loc  :  Set
𝐋              =  Loc +⊥       -- locations
𝐍              =  ℕ +⊥         -- natural numbers
𝐓              =  Bool +⊥      -- booleans
postulate 𝐐    :  Domain       -- symbols
postulate 𝐇    :  Domain       -- characters
postulate 𝐑    :  Domain       -- numbers
𝐄𝐩             =  (𝐋 × 𝐋 × 𝐓)  -- pairs
𝐄𝐯             =  (𝐋 ⋆ × 𝐓)    -- vectors
𝐄𝐬             =  (𝐋 ⋆ × 𝐓)    -- strings
data Misc      :  Set where    false true null undefined unspecified : Misc
𝐌              =  Misc +⊥      -- miscellaneous
𝐗              =  String +⊥    -- errors

-- Domain isomorphisms

open import Function
  using (Inverse; _↔_) public

postulate
  𝐅            :  Domain       -- procedure values
  𝐄            :  Domain       -- expressed values
  𝐒            :  Domain       -- stores
  𝐔            :  Domain       -- environments
  𝐂            :  Domain       -- command continuations
  𝐊            :  Domain       -- expression continuations
  𝐀            :  Domain       -- answers

postulate instance
  iso-𝐅        : 𝐅  ↔  (𝐋 × (𝐄 ⋆ → 𝐊 → 𝐂))
  iso-𝐄        : 𝐄  ↔  (𝕃 (𝐐 + 𝐇 + 𝐑 + 𝐄𝐩 + 𝐄𝐯 + 𝐄𝐬 + 𝐌 + 𝐅))
  iso-𝐒        : 𝐒  ↔  (𝐋 → 𝐄 × 𝐓)
  iso-𝐔        : 𝐔  ↔  (Ide → 𝐋)
  iso-𝐂        : 𝐂  ↔  (𝐒 → 𝐀)
  iso-𝐊        : 𝐊  ↔  (𝐄 ⋆ → 𝐂)

open Inverse {{ ... }}
  renaming (to to ▻ ; from to ◅ ) public
  -- iso-D : D ↔ D′ declares ▻ : D → D′ and ◅ : D′ → D
\end{code}
\clearpage
\begin{code}
variable
  α   : 𝐋
  α⋆  : 𝐋 ⋆
  ν   : 𝐍
  μ   : 𝐌
  φ   : 𝐅
  ϵ   : 𝐄
  ϵ⋆  : 𝐄 ⋆
  σ   : 𝐒
  ρ   : 𝐔
  θ   : 𝐂
  κ   : 𝐊

pattern
  inj-𝐄𝐩 ep  = inj₂ (inj₂ (inj₂ (inj₁ ep)))
pattern
  inj-𝐌 μ    = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ μ))))))
pattern
  inj-𝐅 φ    = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ φ))))))

_∈𝐅          : 𝐄 → Bool +⊥
ϵ ∈𝐅         = ((λ { (inj-𝐅 _) → η true ; _ → η false }) ♯) (▻ ϵ)

_|𝐅          : 𝐄 → 𝐅
ϵ |𝐅         = ((λ { (inj-𝐅 φ) → φ ; _ → ⊥ }) ♯) (▻ ϵ)

_∈𝐋          : 𝕃 (𝐋 + 𝐗) → Bool +⊥
_∈𝐋          = [ (λ _ → η true), (λ _ → η false) ] ♯

_|𝐋          : 𝕃 (𝐋 + 𝐗) → 𝐋
_|𝐋          = [ id , (λ _ → ⊥) ] ♯

_𝐄𝐩-in-𝐄          : 𝐄𝐩 → 𝐄
ep 𝐄𝐩-in-𝐄        = ◅ (η (inj-𝐄𝐩 ep))

_𝐅-in-𝐄           : 𝐅 → 𝐄
φ 𝐅-in-𝐄          = ◅ (η (inj-𝐅 φ))

unspecified-in-𝐄  : 𝐄
unspecified-in-𝐄  = ◅ (η (inj-𝐌 (η unspecified)))
\end{code} 