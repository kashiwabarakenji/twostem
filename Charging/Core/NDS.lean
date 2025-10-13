import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Charging.Core.Basic

/-!
# Core.NDS
NDS の定義（閉集合族の上の有限和）。
-/

namespace Charging

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

open scoped BigOperators

abbrev RS := RuleSystem V

namespace RuleSystem

variable (R : RuleSystem V)

/-- NDS(R) := ∑_{C∈L(R)} (2|C| - |V|) を ℤ で定義。 -/
noncomputable def NDS : Int :=
  ∑ C ∈ R.closedFamily,
    ((2 : Int) * (Int.ofNat C.card) - (Int.ofNat (Fintype.card V)))

end RuleSystem

end Charging
