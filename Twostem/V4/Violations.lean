import Twostem.Core.Rules
import LeanCopilot

namespace V4
open Core
variable {α : Type _} [DecidableEq α]

def violates (R : Finset (Rule α)) (r : Rule α) (A : Finset α) : Prop :=
  r ∈ R ∧ r.prem ⊆ A ∧ r.head ∉ A

def violatesFirst (ρ : RuleOrder α) (R : Finset (Rule α))
    (r : Rule α) (A : Finset α) : Prop :=
  violates R r A ∧
  ∀ s : Rule α, violates R s A → ρ.ruleIndex r ≤ ρ.ruleIndex s

end V4
