import Twostem.Core.Rules
import Twostem.Core.Closure
import Twostem.V4.RepAtoms
import Twostem.V4.Violations
import Twostem.V4.AddedFamily
import LeanCopilot

namespace V4
open Core
variable {α : Type _} [DecidableEq α] [Fintype α]

def FreeOf (B : Finset α) : Finset α := { x | x ∉ B }

def isWitness (ρ : RuleOrder α) (R : Finset (Rule α))
  (B S : Finset α) (t : Rule α) : Prop :=
  (∀ x ∈ S, x ∉ B) ∧
  violatesFirst ρ R t (B ∪ S)


lemma AF_mem_iff_closure
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α)
  (hUC : UniqueChild R) (ht : t ∈ R) :
  A ∈ addedFamily (α:=α) R t
  ↔ ∃ (B S : Finset α),
       A = syncCl (R.erase t) (B ∪ S) ∧ (isWitness ρ R B S t) := by
  classical
  constructor
  · -- →：added → witness（B := A, S := ∅ で構成）
    intro hA
    -- added の展開
    have h' := (mem_addedFamily_iff (R:=R) (t:=t) (A:=A)).mp hA
    rcases h' with ⟨hClosed, hPrem, hHead⟩
    -- 最小性：first_min_of_added を差し込む
    have hMin : ∀ s, violates R s A → ρ.ruleIndex t ≤ ρ.ruleIndex s :=
      first_min_of_added ρ R t (A:=A) hA
    -- violatesFirst を組み立て
    have hFirst : violatesFirst ρ R t A :=
      And.intro ⟨ht, hPrem, hHead⟩ hMin
    -- 閉包不動点：A = syncCl (R.erase t) A
    have hFix : syncCl (R.erase t) A = A :=
      syncCl_id_of_closed (R:=(R.erase t)) hClosed
    -- 目的の等式（∅ での合併に直す）
    have hEq : A = syncCl (R.erase t) (A ∪ (∅ : Finset α)) := by
      -- A = syncCl (R.erase t) A かつ A ∪ ∅ = A を使って書き換え
      have h₁ : A = syncCl (R.erase t) A := Eq.symm hFix
      have h₂ : syncCl (R.erase t) A = syncCl (R.erase t) (A ∪ ∅) := by
        -- 引数の等式 A = A ∪ ∅ の対称を `congrArg` で持ち上げる
        have hu : A ∪ (∅ : Finset α) = A := Finset.union_empty _
        exact congrArg (fun X => syncCl (R.erase t) X) hu.symm
      exact Eq.trans h₁ h₂
    -- ∅ ⊆ FreeOf A
    have hSsub : (∅ : Finset α) ⊆ FreeOf A := by
      intro x hx; cases (Finset.notMem_empty x) hx
    -- witness を組み立て
    refine Exists.intro A (Exists.intro (∅ : Finset α) ?_)
    apply And.intro hEq
    dsimp [isWitness]
    constructor
    · exact fun x a => Disjoint.notMem_of_mem_left_finset (fun ⦃x⦄ a a_1 => a) a
    · dsimp [violatesFirst]
      dsimp [violatesFirst] at hFirst
      constructor
      · simp
        exact hFirst.left
      · intro s hs
        apply hFirst.right s
        simp at hs
        exact hs

  · -- ←：witness → added
    intro h
    rcases h with ⟨B, S, hAeq, hW⟩
    -- まず `A_closed`：syncCl は閉集合
    have hClosedA : IsClosed (R.erase t) (syncCl (R.erase t) (B ∪ S)) :=
      syncCl_closed (α:=α) (R:=(R.erase t)) (I:=B ∪ S)
    -- `prem ⊆`：witness → violatesFirst → violates → prem ⊆ B∪S ⊆ syncCl …
    rcases hW.right with ⟨hViol, _⟩
    have hprem : t.prem ⊆ (B ∪ S) := hViol.right.left

    -- inflationary（像が元を含む）で閉包へ押し上げる
    have hInfl : (B ∪ S) ⊆ syncCl (R.erase t) (B ∪ S) :=
      syncCl_infl (R:=R.erase t) (I:=B ∪ S)

    -- 目的：t.prem ⊆ syncCl (R.erase t) (B ∪ S)
    have hPremSub : t.prem ⊆ syncCl (R.erase t) (B ∪ S) := by
      intro x hx
      exact hInfl (hprem hx)

    -- `head ∉`：既存補題を使用
    have hHeadNot :
      t.head ∉ syncCl (R.erase t) (B ∪ S) := by
        sorry  --下の定理を使う必要あり。
        --let hni := head_not_in_syncCl_of_erase_witness (α:=α) (ρ:=ρ) (R:=R) (B:=B) (S:=S) (t:=t) hUC ht hW
        --convert hni

    -- 以上を A へ転送して addedFamily 条件に詰める
    have : IsClosed (R.erase t) A ∧ t.prem ⊆ A ∧ t.head ∉ A := by
      -- `A = syncCl (R.erase t) (B ∪ S)` を使って書き換え
      refine And.intro ?hC ?hRest
      · -- 閉性
        -- rw で差し替え
        -- `rw [hAeq]` は `simpa using` を避けるために手で展開
        have := hClosedA
        -- 置換
        simp_all only [IsClosed]

      · -- 残り2つ
        have hPrem' :
          t.prem ⊆ A := by
          -- prem ⊆ syncCl … から A へ `rw`
          -- （前段の hPremSub を書き換え）
          simp_all only [IsClosed]
        have hHead' :
          t.head ∉ A := by
          -- head ∉ syncCl … から A へ `rw`
          -- （hHeadNot を書き換え）
          simp_all only [IsClosed, not_false_eq_true]
        exact And.intro hPrem' hHead'
    -- `addedFamily` へ
    have := (mem_addedFamily_iff (α:=α) R t A).mpr this
    exact this


lemma weak_lifting_mem
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (hUC : UC (R:=R))  -- 型に保持（使わないなら消しても可）
  (B S : Finset α) (t : Rule α)
  (hW : isWitness ρ R B S t) :
  t.prem ⊆ Core.syncCl (R.erase t) (B ∪ S)
  ∧ t.head ∉ Core.syncCl (R.erase t) (B ∪ S)
  ∧ Core.syncCl (R.erase t) (B ∪ S) ∈ addedFamily R t := by
  classical
  -- (1) prem ⊆ syncCl … : `syncCl_infl` と前提包含でOK
  -- (2) head ∉ syncCl … : 既存の `head_not_in_syncCl_of_erase_witness` を使用
  -- (3) AF 会員 : `syncCl_closed` / (1) / (2) を `mem_addedFamily_iff` に投げる
  have hclosed : Core.IsClosed (R.erase t) (Core.syncCl (R.erase t) (B ∪ S)) :=
    Core.syncCl_closed (R.erase t) (B ∪ S)
  have hinfl : (B ∪ S) ⊆ Core.syncCl (R.erase t) (B ∪ S) :=
    Core.syncCl_infl (R.erase t) (B ∪ S)
  have hprem : t.prem ⊆ Core.syncCl (R.erase t) (B ∪ S) := by
    -- ここは `violatesFirst` の前件（prem ⊆ B∪S）と hinfl から
    rcases hW with ⟨hfree, hfirst⟩
    rcases hfirst with ⟨hvio, _⟩
    rcases hvio with ⟨htR, hprem, hnot⟩
    exact Finset.Subset.trans hprem hinfl
  -- head 排除は既存補題で
  have hhead : t.head ∉ Core.syncCl (R.erase t) (B ∪ S) := by
    -- プロジェクトにある `head_not_in_syncCl_of_erase_witness` を呼ぶ
    -- ここでは仮配置
    sorry
  have hmem : Core.syncCl (R.erase t) (B ∪ S) ∈ addedFamily R t := by
    -- mem_addedFamily_iff に hclosed / hprem / hhead を挿すだけ
    have := (mem_addedFamily_iff (R:=R) (t:=t) (A:=Core.syncCl (R.erase t) (B ∪ S))).mpr
      ⟨hclosed, hprem, hhead⟩
    simpa using this
  exact ⟨hprem, hhead, hmem⟩

end V4
