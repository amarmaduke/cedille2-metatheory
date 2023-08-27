import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"c532d7b"

package «cedille2» {
  -- add package configuration options here
}

lean_lib Common where
  roots := #[`Common]

lean_lib SystemFOmega where
  roots := #[`SystemFOmega]

lean_lib Cedille where
  roots := #[`Cedille]

@[default_target]
lean_exe «cedille» {
  root := `Main
}
