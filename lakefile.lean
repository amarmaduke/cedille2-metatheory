import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"4ceb2ea935085e8145e880f754cef760063f16de"

package «cedille2» {
  -- add package configuration options here
}

lean_lib Common where
  roots := #[`Common]

lean_lib Cedille where
  roots := #[`Cedille]

lean_lib WCCC where
  roots := #[`WCCC]

@[default_target]
lean_exe «cedille» {
  root := `Main
}
