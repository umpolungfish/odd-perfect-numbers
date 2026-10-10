import Lake
open Lake DSL

package "OddPerfectNumbers" where
  name := "OddPerfectNumbers"

-- Reconnected: the old local git path ../mathlib4_PROOFS/mathlib4 no longer
-- exists. Pin the same mathlib the main Imscribing repo builds on.
require "leanprover-community" / "mathlib" from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib OddPerfectNumbers
lean_lib Challenge
