import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.Closure.Sync
import LeanCopilot

namespace Twostem

open scoped BigOperators
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- 全体 α 上の閉集合族（powerset を `IsClosed` でフィルタ） -/
def Family (R : Finset (Rule α)) [DecidablePred (fun I => IsClosed R I)] : Finset (Finset α) :=
  (univ : Finset α).powerset.filter (fun I => (IsClosed R I))

omit [DecidableEq α] [LinearOrder α] in
/-- `I ∈ Family R` の同値条件（`I ⊆ univ` は自明なので `IsClosed` が実質） -/
lemma mem_Family {R : Finset (Rule α)} [DecidablePred (IsClosed R)] {I : Finset α} :
  I ∈ Family (α:=α) R ↔ IsClosed R I := by
  classical
  unfold Family
  have : I ⊆ (univ : Finset α) := fun _ _ => by simp
  constructor
  · intro h; simpa [mem_filter, mem_powerset, this] using h
  · intro h;
    simp_all only [subset_univ, powerset_univ, mem_filter, mem_univ, and_self]

/-- ポテンシャル `NDS`（全体 α を台として定義） -/
def NDS (R : Finset (Rule α)) [DecidablePred (fun I => IsClosed R I)] : ℤ :=
  ∑ I ∈ Family R, (2 * (I.card : ℤ) - (Fintype.card α : ℤ))

/-- 任意の `I` に対し `syncCl R I` は閉集合族 `Family R` に属する -/
lemma syncCl_mem_Family {R : Finset (Rule α)} {I : Finset α} [DecidablePred (fun I => IsClosed R I)] :
  syncCl (α:=α) R I ∈ Family R := by
  classical
  have hclosed : IsClosed R (syncCl R I) := syncCl_closed (α:=α) (R:=R) (I:=I)
  simpa [mem_Family] using hclosed

/- `syncCl` は最小閉包：任意の閉集合 `J` で `I ⊆ J` なら `syncCl R I ⊆ J` -/
--lemma syncCl_le_of_closed {R : Finset (Rule α)} {I J : Finset α}
--  (hIJ : I ⊆ J) (hJ : IsClosed R J) :
--  syncCl R I ⊆ J := by
--    exact syncCl_min R hIJ hJ

end Twostem
