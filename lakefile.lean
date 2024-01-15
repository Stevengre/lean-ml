import Lake
open Lake DSL

package «lean-ml» where
  -- add package configuration options here

lean_lib «LeanMl» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-ml» where
  root := `Main
