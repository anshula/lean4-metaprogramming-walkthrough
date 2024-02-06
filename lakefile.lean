import Lake
open Lake DSL

package «LeanMetaprogrammingWalkthrough» where
  -- add package configuration options here

require verso from git "https://github.com/leanprover/verso" @ "main"
-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib Walkthrough where
  srcDir := "website"
  roots := #[`Walkthrough]

@[default_target]
lean_exe walkthrough where
  srcDir := "website"
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
