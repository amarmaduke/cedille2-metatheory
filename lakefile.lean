import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"4ceb2ea935085e8145e880f754cef760063f16de"

package «cedille2» {
  -- add package configuration options here
}

lean_lib Common where
  roots := #[`Common]

lean_lib Erased where
  roots := #[`Erased]

lean_lib Fomega where
  roots := #[`Fomega]

lean_lib Cedille2 where
  roots := #[`Cedille2]

lean_lib WCCC where
  roots := #[`WCCC]

@[default_target]
lean_exe «cedille» {
  root := `Main
}
