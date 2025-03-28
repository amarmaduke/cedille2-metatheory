import Lake
open Lake DSL

package «cedille2» {
  -- add package configuration options here
}

require "leanprover-community" / "mathlib"

lean_lib Common where
  roots := #[`Common]

lean_lib SetTheory where
  roots := #[`SetTheory]

lean_lib Erased where
  roots := #[`Erased]

lean_lib Fomega where
  roots := #[`Fomega]

lean_lib CC where
  roots := #[`CC]

lean_lib Cedille2 where
  roots := #[`Cedille2]

@[default_target]
lean_exe «cedille» {
  root := `Main
}
