import Lake
open Lake DSL

package «charging» where
  -- add package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

lean_lib «Charging» where
  -- add library configuration options here
  roots := #[
    `Charging
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.23.0"


@[default_target]
lean_exe «charging» where
  root := `Main
