\begin{code}
module LC.Variables where
  
open import Data.Bool using (Bool)
open import Data.Nat  using (ℕ; _≡ᵇ_)

data Var : Set where
  x : ℕ → Var  -- variables

variable v : Var

_==_ : Var → Var → Bool
x n == x n′ = (n ≡ᵇ n′)
\end{code}