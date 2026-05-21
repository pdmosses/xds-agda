# Abstract Syntax

The following grammar [(Mosses2025CSE)] summarises the abstract syntax of *Scm*
expressions $\text{E} : \text{Exp}$
with integers $\text{Z} : \text{Int}$,
constants $\text{K} : \text{Con}$ and 
identifiers $\text{I} : \text{Ide}$.
The meta-variable $\text{E}^* : \text{Exp}^*$ implicitly ranges over arbitrary sequences of expressions.
@latex
@/latex
$$\begin{align}
  \text{K} & ::=
    \text{Z} \mid \text{\tt \#t} \mid \text{\tt \#f}
  \\
  \text{E} & ::=
    \text{K} \mid \text{I} \mid \texttt ( \text{E}_0~\text{E}^* \texttt ) \mid \text{\tt (lambda} ~ \text{I} ~ \text{E} \texttt ) \mid
    \text{\tt (if} ~ \text{E}_0 ~ \text{E}_1 ~ \text{E}_2 \texttt ) \mid \text{\tt (set!} ~ \text{I} ~ \text{E} \texttt )
\end{align}$$
@latex
@/latex
In the following Agda embedding of the above grammar, the abstract syntax of sequences `E⋆ : Exp⋆` is made explicit:
the empty sequence is represented by `␣␣␣` , and sequence prefixing by `E ␣␣ E⋆`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Examples.Scm.Abstract-Syntax where
--"hide"

open import Data.String.Base public using (String)
--"/hide"

Ide = String      -- identifiers
--"hide"
variable I : Ide

open import Data.Integer.Base public renaming (ℤ to Int) using ()
--"/hide"

data Con  : Set where  -- constants
  int     : Int → Con  -- integer numerals
  #t      : Con        -- true
  #f      : Con        -- false
--"hide"
variable K : Con
--"/hide"

mutual
  data Exp       : Set where              -- expressions
    con          : Con → Exp              -- constants
    ide          : Ide → Exp              -- identifiers
    ⦅_␣_⦆        : Exp → Exp⋆ → Exp       -- procedure application 
    ⦅lambda_␣_⦆  : Ide → Exp → Exp        -- procedure abstraction
    ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp  -- conditional choice
    ⦅set!_␣_⦆    : Ide → Exp → Exp        -- assignment
  data Exp⋆      : Set where              -- expression sequences
    ␣␣␣          : Exp⋆                   -- empty sequence
    _␣␣_         : Exp → Exp⋆ → Exp⋆      -- sequence prefix
--"hide"
variable E : Exp; E⋆ : Exp⋆

mutual
  data Body      : Set where              -- bodies
    ␣␣_          : Exp → Body             -- expression body
    ⦅define_␣_⦆  : Ide → Exp → Body       -- definition body
    ⦅begin_⦆     : Body⁺ → Body           -- body sequence
  data Body⁺     : Set where              -- body sequences
    ␣␣_          : Body → Body⁺           -- empty sequence
    _␣␣_         : Body → Body⁺ → Body⁺   -- sequence prefix
data Prog        : Set where              -- programs
  ␣␣␣            : Prog                   -- empty program
  ␣␣_            : Body⁺ → Prog           -- body sequence program
variable B : Body; B⁺ : Body⁺; Π : Prog
--"/hide"
```

[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369