-- Twostem/Synchronous.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Twostem.Rules
import Twostem.Closure

--論文にSynchronousという言葉はある。
--1タイミングごとに根を追加していくことか。
--Closure.leanのほうにも似たようなものがある。

namespace Twostem

open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- 同期ステップ： 現在集合 X から「前提がすべて X に含まれる」ルールの head を一斉に追加 -/
def syncStep (R : Finset (Rule α)) (X : Finset α) : Finset α :=
  X ∪ (R.filter (fun t => t.prem ⊆ X)).image (fun t => t.head)

omit [Fintype α][DecidableEq α][LinearOrder α] in
lemma syncStep_mono [DecidableEq α] {R : Finset (Rule α)} :
  Monotone (syncStep (α:=α) R) := by
  classical
  -- 単調性：X ⊆ Y → syncStep R X ⊆ syncStep R Y
  intro X Y hXY a ha
  -- ha : a ∈ X ∪ image(…X…)
  -- ゴール : a ∈ Y ∪ image(…Y…)
  rcases Finset.mem_union.mp ha with hX | hImg
  · -- a ∈ X ⇒ a ∈ Y（X ⊆ Y）⇒ 左和に入る
    exact Finset.mem_union.mpr (Or.inl (hXY hX))
  · -- a が image 側から来た場合
    rcases Finset.mem_image.mp hImg with ⟨t, ht, rfl⟩
    -- ht : t ∈ R.filter (fun t => t.prem ⊆ X)
    -- まず filter の条件を分解
    have htR : t ∈ R := by
      have := (Finset.mem_filter.mp ht).1
      exact this
    have hsubX : t.prem ⊆ X := by
      have := (Finset.mem_filter.mp ht).2
      exact this
    -- X ⊆ Y より prem ⊆ Y
    have hsubY : t.prem ⊆ Y := fun u hu => hXY (hsubX hu)
    -- したがって t は R.filter (…⊆ Y) にも属する
    have htY : t ∈ R.filter (fun t => t.prem ⊆ Y) := by
      exact (Finset.mem_filter.mpr ⟨htR, hsubY⟩)
    -- よって t.head は image 側で Y にも入る
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨t, htY, rfl⟩))


/-- 同期列： step^n を反復する -/
def syncIter (R : Finset (Rule α)) : ℕ → Finset α → Finset α
| 0,     X => X
| (n+1), X => syncStep R (syncIter R n X)

omit [Fintype α][LinearOrder α] in
lemma syncIter_mono {R : Finset (Rule α)} :
  ∀ n, Monotone (syncIter R n)
| 0     => fun _ _ h => h
| (n+1) => fun _ _ h => (syncStep_mono (R:=R)) ((syncIter_mono (R:=R) n) h)

omit [Fintype α] [LinearOrder α] in
lemma le_syncIter_succ {R : Finset (Rule α)} {n : ℕ} {X : Finset α} :
  syncIter R n X ⊆ syncIter R (n+1) X := by
  classical
  change syncIter R n X ⊆ syncStep R (syncIter R n X)
  exact subset_union_left

omit [Fintype α] [LinearOrder α] in
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
-- isClosed_closure : IsClosed R (syncCl R X)
-- IsClosed.def: ∀ t∈R, prem⊆I → head∈I
lemma head_mem_closure_of_prem_subset {R : Finset (Rule α)} {X : Finset α}
  {t : Rule α} (ht : t ∈ R) (hPrem : t.prem ⊆ syncCl R X) :
  t.head ∈ syncCl R X := by
  have hClosed : IsClosed R (syncCl R X) := syncCl_closed (R := R) (I := X)
  exact hClosed ht hPrem


end Twostem
