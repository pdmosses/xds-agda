-- record Summand (D E : Set) : Set₁ where
--   field
--     inj : D → E
--
--  _inj_ : {D : Set} → D → (E : Set) → {{Summand D E}} → E
-- (x inj E) {{summand}} = Summand.inj summand x

postulate
  Summand : (D E : Set) → Set
  _inj_ : {D : Set} → D → (E : Set) → {{Summand D E}} → E

postulate R S T U : Set

postulate instance
  R<S : Summand R S
  T<U : Summand T U

postulate
  r : R
  t : T

s : S
s = r inj S  -- ok accepted

-- x : S
-- x = t inj S  -- ok rejected (but accepted when x : S omitted!)