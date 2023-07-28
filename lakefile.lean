import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"

package «cedille2» {
  -- add package configuration options here
}

lean_lib Common where
  roots := #[`Common]

lean_lib SystemFOmega where
  roots := #[`SystemFOmega]

lean_lib Cedille where
  roots := #[`Cedille]
