import Mathlib.Data.Finset.Basic
import Charging.Core.Basic
import Charging.Core.Chains

/-!
# Core.SCdagger
SC†（鎖内局所性 + 単調前方安全性）の定義。
証明は別フェーズ。ここは述語定義のみ。
-/

namespace Charging

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

namespace RuleSystem

variable (R : RuleSystem V) (D : ChainDecomp V)

/-- 鎖内局所性：各規則の `prem ∪ {head}` が同一鎖 `j` に含まれる。 -/
def IntraChainLocal : Prop :=
  ∀ t ∈ R.rules, ∃ j : D.ι, t.head ∈ D.P j ∧ t.prem ⊆ D.P j

/- 単調前方安全性（MS）：
  任意の鎖 `j` と任意の `k` について、`Pref(j,k)` に含まれる前提だけから
  その外側の `P(j) \ Pref(j,k)` に head を持つ規則は存在しない。 -/
--def MonotoneForwardSafe : Prop :=
--  ∀ j : D.ι, ∀ k : Nat,
--    ¬ ∃ t ∈ R.rules, t.prem ⊆ D.Pref j k ∧ t.head ∈ (D.P j) \ (D.Pref j k)

/-- (2) 単調前方安全性 (Monotone-Safety)：
  どの鎖でも、初期区間 Prefⱼ(k) 内の前提だけでは鎖外の要素を導けない。 -/
def MonotoneSafety : Prop :=
  ∀ (i : D.ι) (k : ℕ),
    ¬ ∃ t ∈ R.rules, t.prem ⊆ D.Pref i k ∧ t.head ∈ D.P i \ D.Pref i k

/-- （参考）MS の“実用形”（含意形）：
  `prem ⊆ Pref i k` かつ `head ∈ P i` なら `head ∈ Pref i k`。 -/
def MonotoneSafetyImp : Prop :=
  ∀ (i : D.ι) (k : ℕ) (t : Rule V),
    t ∈ R.rules → t.prem ⊆ D.Pref i k → t.head ∈ D.P i → t.head ∈ D.Pref i k

/-- MS（存在否定形）と実用形（含意形）は同値。 -/
lemma MonotoneSafety_iff_Imp :
    R.MonotoneSafety D ↔ R.MonotoneSafetyImp D := by
  classical
  constructor
  · -- → : 反証から含意を得る
    intro hMS i k t ht hsub hheadPi
    -- もし head ∉ Pref なら、反例の存在を組み立てられる
    by_contra hnot
    have : ∃ t' ∈ R.rules, t'.prem ⊆ D.Pref i k ∧ t'.head ∈ D.P i \ D.Pref i k := by
      refine ⟨t, ht, hsub, ?_⟩
      -- head ∈ (P i) \ (Pref i k) を示す
      have : t.head ∉ D.Pref i k := hnot
      -- sdiff の membership は `∈` と `∉` の組
      exact by
        -- `by cases` より `simp` が簡潔
        simpa [Finset.mem_sdiff] using And.intro hheadPi this
    exact (hMS i k) this
  · -- ← : 含意形から存在否定形を得る
    intro hImp i k hex
    rcases hex with ⟨t, ht, hsub, hmem⟩
    have hPi : t.head ∈ D.P i := by
      simpa [Finset.mem_sdiff] using (And.left (by
        -- `hmem : t.head ∈ P i \ Pref i k`
        -- から `t.head ∈ P i` と `t.head ∉ Pref i k` が取れる
        have : t.head ∈ D.P i ∧ t.head ∉ D.Pref i k := by
          simpa [Finset.mem_sdiff] using hmem
        exact this
        ))
    have hnotPref : t.head ∉ D.Pref i k := by
      simpa [Finset.mem_sdiff] using
        (And.right (by
          have : t.head ∈ D.P i ∧ t.head ∉ D.Pref i k := by
            simpa [Finset.mem_sdiff] using hmem
          exact this))
    -- 含意形に反するので矛盾
    have := hImp i k t ht hsub hPi
    exact hnotPref this


/-- SC† 条件：IntraChainLocal ∧ MonotoneSafety -/
def SCdagger : Prop :=
  R.IntraChainLocal D ∧ R.MonotoneSafety D

end RuleSystem

end Charging
