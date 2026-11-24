import Lake
open Lake DSL

package «goldbach-twinprime-proof-lean4» where
  version := v!"0.1.0"

require lean4lean from git
  "gh:digama0/lean4lean.git" @ "7842f38"

require mathlib from git
  "gh:leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib «JSP000008» where
  srcDir := "."
  roots := #[`«JSP-000008»]
