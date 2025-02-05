import Lake
open Lake DSL

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
