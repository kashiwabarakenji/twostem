import Mathlib.Data.Finset.Basic
import Twostem.Basic
import Twostem.ProblemA
import Twostem.ProblemA_UC

/-
# Twostem.B_Existence — UC 前提下の「Peel or Shrink」存在系（骨格）

目的：R ≠ ∅ なら
  (i) Barrier を持つ peelable な t0 がある か、
  (ii) SafeShrink できる
の二者択一を与える。さらに `PeelWitness` へ直結する形も準備。

依存：
- `Twostem.Basic`（PeelWitness, SafeShrink, supportedOn など）
- `Twostem.ProblemA`（BarrierHyp）
- `Twostem.ProblemA_UC`（UniqueChild, PeelWitness_from_UC_core へ接続）
-/

universe u
variable {α : Type u} [DecidableEq α]

namespace B_Existence

open ProblemA_UC
open ThreadA


/-- ★中核（NoBarrier→SafeShrink）。ここは別スレッドで証明差し替え予定。 -/
axiom noBarrier_implies_SafeShrink_UC
  (V : Finset α) (R : Finset (Rule α))
  (hV  : supportedOn V R) (hUC : UniqueChild R)
  (hne : R ≠ ∅)
  (hNoB : ∀ t ∈ R, ¬ ThreadA.BarrierHyp V R t) :
  ∃ R1, SafeShrink V R R1

/-- UC + R≠∅ で、Barrier があればそれを、なければ SafeShrink を返す二者択一。 -/
theorem PeelOrShrink_UC
  (V : Finset α) (R : Finset (Rule α))
  (hV  : supportedOn V R) (hUC : UniqueChild R)
  (hne : R ≠ ∅) :
  (∃ t0 ∈ R, ThreadA.BarrierHyp V R t0) ∨ (∃ R1, SafeShrink V R R1) := by
  classical
  -- 場合分け：Barrier をみたす t0 があるか
  by_cases hEx : ∃ t0 ∈ R, ThreadA.BarrierHyp V R t0
  · exact Or.inl hEx
  -- どの t も Barrier でない ⇒ SafeShrink
  ·
    have hNoB : ∀ t ∈ R, ¬ ThreadA.BarrierHyp V R t := by
      intro t ht hB
      have hneg : ¬ (∃ t0 ∈ R, ThreadA.BarrierHyp V R t0) := by exact hEx
      exact hneg ⟨t, ht, hB⟩
    have h := noBarrier_implies_SafeShrink_UC (V := V) (R := R) hV hUC hne hNoB
    cases' h with R1 hSS
    exact Or.inr ⟨R1, hSS⟩

/-- Barrier ⇒ PeelWitness（ユーザー提示版をそのまま利用） -/
theorem PeelWitness_from_Barrier
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hmem : t0 ∈ R) (hB : BarrierHyp V R t0) :
  PeelWitness V R t0 := by
  classical
  have avg := avgHalf_via_Barrier (V := V) (R := R) (t0 := t0) hB
  exact ⟨hmem, PeelStep_nondecrease_core (V := V) (R := R) (t0 := t0) avg⟩

/-- 二者択一を PeelWitness／SafeShrink に直結した存在版。 -/
theorem Exists_PeelWitness_or_SafeShrink
  (V : Finset α) (R : Finset (Rule α))
  (hV  : supportedOn V R) (hUC : UniqueChild R)
  (hne : R ≠ ∅) :
  (∃ t0, PeelWitness V R t0) ∨ (∃ R1, SafeShrink V R R1) := by
  classical
  have h := PeelOrShrink_UC (V := V) (R := R) hV hUC hne
  cases h with
  | inl hbar =>
      cases' hbar with t0 ht0
      cases' ht0 with hmem hB
      have pw := PeelWitness_from_Barrier (V := V) (R := R) (t0 := t0) hmem hB
      exact Or.inl ⟨t0, pw⟩
  | inr hsh =>
      cases' hsh with R1 hSS
      exact Or.inr ⟨R1, hSS⟩

end B_Existence

/-

/-- UC 前提下の Peel or Shrink（証明スケルトン） -/
theorem PeelOrShrink_UC
  (V : Finset α) (R : Finset (Rule α))
  (hV  : supportedOn V R) (hUC : UniqueChild R)
  (hne : R ≠ ∅) :
  (∃ t0 ∈ R, ThreadA.BarrierHyp V R t0) ∨ (∃ R1, SafeShrink V R R1) := by
  classical
  /- TODO:
    - `ViolSet` が空か非空かで分岐
    - 非空なら Core から `BarrierHyp` を構成
    - 空なら SCC 縮約などから `SafeShrink` を供給
  -/
  sorry

/-- PeelWitness か SafeShrink のいずれか（証明スケルトン） -/
theorem Exists_PeelWitness_or_SafeShrink
  (V : Finset α) (R : Finset (Rule α))
  (hV  : supportedOn V R) (hUC : UniqueChild R)
  (hne : R ≠ ∅) :
  (∃ t0, PeelWitness V R t0) ∨ (∃ R1, SafeShrink V R R1) := by
  classical
  have h := PeelOrShrink_UC (V := V) (R := R) hV hUC hne
  /- TODO:
    - 左枝：`⟨t0, ht0∈R, hB⟩` から `ProblemA_UC.PeelWitness_from_UC_core` を適用
    - 右枝：そのまま SafeShrink
  -/
  sorry

end B_Existence
end Twostem
-/
