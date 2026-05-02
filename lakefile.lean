import Lake
open Lake DSL

package "OddPerfectNumbers" where
  name := "OddPerfectNumbers"

require "leanprover-community" / "mathlib" from
  git "../mathlib4_PROOFS/mathlib4"

lean_lib OddPerfectNumbers
lean_lib Challenge
