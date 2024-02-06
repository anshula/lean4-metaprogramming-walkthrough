import Lake
open Lake DSL

package «LeanMetaprogrammingWalkthrough» where
  -- add package configuration options here

lean_lib «LeanMetaprogrammingWalkthrough» where
  -- add library configuration options here

require verso from git "https://github.com/leanprover/verso" @ "main"

-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_exe «leanmetaprogrammingwalkthrough» where
  root := `LeanMetaprogrammingWalkthrough
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

-- A demo site that shows how to generate websites with Verso
lean_lib DemoSite where
  srcDir := "website"
  roots := #[`DemoSite]

@[default_target]
lean_exe demosite where
  srcDir := "website"
  root := `DemoSiteMain
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
