import Lake
open Lake DSL

package «lean-ml» where
  -- add package configuration options here

lean_lib «ML» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-ml» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require std from git "https://github.com/leanprover/std4" @ "main"
