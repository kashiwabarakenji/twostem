import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Int
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

open scoped BigOperators
variable {α : Type u} [DecidableEq α]

theorem finset_sum_le_finset_sum {ι : Type _} [DecidableEq ι] {N : Type _}
    [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N]
    {f g : ι → N} {s : Finset ι} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  refine Finset.induction_on s (by simp) (fun a s has IH => ?_) h
  ·
    intro x
    simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
      Finset.sum_insert]
    obtain ⟨left, right⟩ := x
    gcongr
