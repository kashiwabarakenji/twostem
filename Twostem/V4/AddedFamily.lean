import Twostem.Core.Rules
import Twostem.Core.Closure
import Twostem.V4.Violations

namespace V4
open Core
variable {α : Type _} [DecidableEq α] [Fintype α]

noncomputable def addedFamily
  (R : Finset (Rule α)) (t : Rule α) : Finset (Finset α) :=
  (Core.Family (α:=α) (R.erase t)).filter (fun A =>
    True ∧ t.prem ⊆ A ∧ t.head ∉ A)

lemma mem_addedFamily_iff
  (R : Finset (Rule α)) (t : Rule α) (A : Finset α) :
  A ∈ addedFamily R t
  ↔ (Core.IsClosed (R.erase t) A ∧ t.prem ⊆ A ∧ t.head ∉ A) := by
  classical
  simp [addedFamily, Core.mem_Family_iff]
  -- True ∧ P ∧ Q  ≃  P ∧ Q


lemma first_min_of_added
  [DecidableEq (Rule α)]  -- addedFamily の erase で必要
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A : Finset α}
  --(ht : t ∈ R)
  (hA : A ∈ addedFamily (α:=α) R t) :
  ∀ s, violates R s A → ρ.ruleIndex t ≤ ρ.ruleIndex s := by
  classical
  -- addedFamily を展開
  have hdef := (mem_addedFamily_iff (R:=R) (t:=t) (A:=A)).mp hA
  rcases hdef with ⟨hClosed, hPrem_t, hHead_t⟩
  -- 任意の違反 s について示す
  intro s hs
  rcases hs with ⟨hsR, hsPrem, hsHead⟩
  -- s=t か s≠t で分岐
  by_cases hst : s = t
  · -- s = t なら反射律で終わり
    rw [hst]
  · -- s ≠ t の場合、s ∈ R.erase t なので閉性より head ∈ A、しかし violates と矛盾
    have hs_in_erase : s ∈ R.erase t := by
      -- Finset.mem_erase: x ∈ erase s a ↔ x ≠ a ∧ x ∈ s
      exact Finset.mem_erase.mpr ⟨hst, hsR⟩

    have : s.head ∈ A := by
      apply hClosed --(t := s) hs_in_erase hsPrem
      dsimp [stepPar]
      simp
      right
      dsimp [heads]
      dsimp [fires]
      simp
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
      use s

    exact (by
      -- 矛盾から任意命題（特にルールインデックスの不等式）を示すには、
      -- まず矛盾自体を導く必要がある。ここでは「hsHead : s.head ∉ A」と衝突。
      -- したがってこの分岐は発生しえず、ケース分け全体としては s = t 側のみが残る。
      -- しかし Lean 的にはこのブランチからは目標を直接示す必要があるので、
      -- False.elim で閉じるのではなく、矛盾から何でも示せるわけにはいきません。
      -- そこで、矛盾は「このブランチが起こらない」ことを示すので、
      -- `cases` による分岐の前に `by_cases` を使っており、このブランチは
      -- 実際には到達不能です：`exact (hsHead this).elim` で十分です。
      exact (hsHead this).elim)

end V4
