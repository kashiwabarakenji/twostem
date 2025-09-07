import Lake
open Lake DSL

package «twostem» where
  -- add package configuration options here

lean_lib «Twostem» where
  -- add library configuration options here
  roots := #[
    `Twostem.General,
    `Twostem.Basic,
    `Twostem.ProblemA,
    `Twostem.ProblemB,
    `Twostem.ProblemC,
    `Twostem.ProblemCC,
    `Twostem.ProblemDD
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0-rc2"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.22.0"


@[default_target]
lean_exe «twostem» where
  root := `Main
