-- Twostem/Synchronous.lean
import Mathlib/Data/Finset/Basic
import Twostem.Rules
import Twostem.Closure

namespace Twostem

open Finset

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- 同期ステップ： 現在集合 X から「前提がすべて X に含まれる」ルールの head を一斉に追加 -/
def syncStep (R : Finset (Rule α)) (X : Finset α) : Finset α :=
  X ∪ (R.filter (fun t => t.prem ⊆ X)).image (fun t => t.head)

lemma syncStep_mono {R : Finset (Rule α)} :
  Monotone (syncStep R) := by
  intro X Y hXY
  classical
  apply union_subset_union_left.mpr
  -- (filter prem⊆X).image head ⊆ (filter prem⊆Y).image head
  refine image_subset_iff.mpr ?_
  intro t ht
  have htR : t ∈ R := (mem_filter.mp ht).1
  have hsub : t.prem ⊆ Y := subset_trans (mem_filter.mp ht).2 hXY
  exact mem_image.mpr ⟨t, mem_filter.mpr ⟨htR, hsub⟩, rfl⟩

/-- 同期列： step^n を反復する -/
def syncIter (R : Finset (Rule α)) : ℕ → Finset α → Finset α
| 0,     X => X
| (n+1), X => syncStep R (syncIter R n X)

lemma syncIter_mono {R : Finset (Rule α)} :
  ∀ n, Monotone (syncIter R n)
| 0     => fun _ _ h => h
| (n+1) => fun _ _ h => (syncStep_mono (R:=R)) ((syncIter_mono (R:=R) n) h)

lemma le_syncIter_succ {R : Finset (Rule α)} {n : ℕ} {X : Finset α} :
  syncIter R n X ⊆ syncIter R (n+1) X := by
  classical
  change syncIter R n X ⊆ syncStep R (syncIter R n X)
  exact subset_union_left

/-- 0 段目からの包含： X ⊆ syncIter R n X （単純帰納） -/
lemma subset_syncIter {R : Finset (Rule α)} :
  ∀ n X, X ⊆ syncIter R n X
| 0,     X => by intro a ha; simpa using ha
| (n+1), X =>
  by
    intro a ha
    have : a ∈ syncIter R n X := subset_syncIter n X ha
    exact (subset_union_left : syncIter R n X ⊆ syncStep R (syncIter R n X)) this

/-- 閉包は R-閉：Closure.lean 側の基本補題を利用（なければ同名補題を用意） -/
-- isClosed_closure : IsClosed R (closure R X)
-- IsClosed.def: ∀ t∈R, prem⊆I → head∈I
lemma head_mem_closure_of_prem_subset {R : Finset (Rule α)} {X : Finset α}
  {t : Rule α} (ht : t ∈ R) (hPrem : t.prem ⊆ closure R X) :
  t.head ∈ closure R X := by
  have hClosed := isClosed_closure (R:=R) (X:=X)
  -- hClosed: ∀ t∈R, t.prem ⊆ closure R X → t.head ∈ closure R X
  simpa using hClosed ht hPrem

/-- 同期列の各段は閉包に含まれる -/
lemma syncIter_subset_closure {R : Finset (Rule α)} {X : Finset α} :
  ∀ n, syncIter R n X ⊆ closure R X
| 0     => subset_closure (R:=R) (I:=X)
| (n+1) =>
  by
    classical
    intro a ha
    -- a ∈ syncStep R (syncIter R n X)
    rcases mem_union.mp ha with hIn | hHead
    · exact (syncIter_subset_closure (R:=R) (X:=X) n) hIn
    · rcases mem_image.mp hHead with ⟨t, htFilt, rfl⟩
      have htR : t ∈ R := (mem_filter.mp htFilt).1
      have hPremX : t.prem ⊆ syncIter R n X := (mem_filter.mp htFilt).2
      have hPremCl : t.prem ⊆ closure R X :=
        subset_trans hPremX (syncIter_subset_closure (R:=R) (X:=X) n)
      exact head_mem_closure_of_prem_subset (R:=R) (X:=X) (t:=t) htR hPremCl

end Twostem
