import Lake
open Lake DSL

package «twostem» where
  -- add package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

lean_lib «Twostem» where
  -- add library configuration options here
  roots := #[
    `Twostem.Closure.Abstract,
    `Twostem.Closure.Core,
    `Twostem.Closure.Step,
    `Twostem.Closure.Sync,
    --`Twostem.Rules,
    --`Twostem.Closure,
    `Twostem.MainCore,
    `Twostem.Fiber,
    `Twostem.NDS,
    `Twostem.Synchronous,
    `Twostem.Bridge,
    `Twostem.Derivation,
    `Twostem
--    `Twostem.Twostem
    /-
    `Twostem.General,
    `Twostem.Basic,
    `Twostem.BDBasic,
    `Twostem.ProblemA,
    `Twostem.ProblemB,
    `Twostem.ProblemC,
    `Twostem.ProblemCC,
    `Twostem.ProblemDD,
    `Twostem.SCC,
    `Twostem.Free,
    `Twostem.Excess,
    `Twostem.Main,
    `Twostem.ProblemA_UC,
    `Twostem.B_Existence,
    `Twostem.B_NoBarrier_SafeShrink_UC
    -/
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.23.0"


@[default_target]
lean_exe «twostem» where
  root := `Main
