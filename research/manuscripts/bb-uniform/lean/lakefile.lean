import Lake
open Lake DSL

package bbSharpUniform where
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b5eba595428809e96f3ed113bc7ba776c5f801ac"

@[default_target]
lean_lib BB
