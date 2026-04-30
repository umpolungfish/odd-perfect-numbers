import Lake
open Lake DSL

package "OddPerfectNumbers" where
  name := "OddPerfectNumbers"

require "leanprover-community" / "mathlib" from
  git "https://github.com/leanprover-community/mathlib4" @ "676b870c7dd6f238df74091c8353c766e3a97aef"

lean_lib OddPerfectNumbers
