import Lake
open Lake DSL

package "OddPerfectNumbers" where
  name := "OddPerfectNumbers"

-- Point at local Mathlib4 clone during development.
-- To use the published Mathlib4, replace with:
--   require "leanprover-community" / "mathlib" from
--     git "https://github.com/leanprover-community/mathlib4" @ "<commit>"
require "leanprover-community" / "mathlib" from
  "../mathlib4_PROOFS/mathlib4"

lean_lib OddPerfectNumbers
