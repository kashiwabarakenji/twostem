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
    `Twostem.MainCore,
    `Twostem.NDS,
    `Twostem.Bridge,
    `Twostem.BridgeI,
    --`Twostem.Fiber,
    --`Twostem.Synchronous,
    --`Twostem.Rules,
    --`Twostem.Closure,
    --`Twostem.Derivation,
    --`Twostem.Twostem
   `Twostem
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.23.0"


@[default_target]
lean_exe «twostem» where
  root := `Main
