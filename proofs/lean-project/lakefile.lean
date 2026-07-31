import Lake
open Lake DSL

package «proof-lab» where
  -- add package configuration options here

lean_lib «ProofLab» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.10.0"

@[default_target]
lean_exe «proof-lab» where
  root := `Main
