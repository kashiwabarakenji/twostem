import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import LeanCopilot

open scoped BigOperators

namespace Twostem
open Closure

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Rules and basic predicates (assume your existing `Rule` etc. are imported). -/
-- placeholder: `Rule α` should already be defined in your project
def UC (R : Finset (Rule α)) : Prop :=
  ∀ a : α, (R.filter (fun t => t.head = a)).card ≤ 1

-- Closed family w.r.t. rules R
@[simp] def IsClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ ⦃t : Rule α⦄, t ∈ R → t.prem ⊆ I → t.head ∈ I

/-- Rules applicable to I (prem ⊆ I ∧ head ∉ I). -/
@[simp] def applicable (R : Finset (Rule α)) (I : Finset α) : Finset (Rule α) :=
  R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I)

/-- All heads that can fire in one step. -/
@[simp] def fires [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  (R.filter (fun t => t.prem ⊆ I)).image (fun t => t.head)

/-- One-step expansion by firing all currently applicable heads. -/
@[simp] def step [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  I ∪ fires R I

/-- Monotonicity of `fires`. -/
lemma fires_mono {α : Type*} [DecidableEq α]
  (R : Finset (Rule α)) : Monotone (fires R) := by
  intro X Y h x hx
  dsimp [fires] at hx ⊢
  rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
  rcases Finset.mem_filter.mp ht with ⟨htR, hsub⟩
  exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htR, hsub.trans h⟩, rfl⟩

/-- Inflationary: `I ⊆ step R I`. -/
lemma step_infl {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
  ∀ s, s ⊆ step R s := by
  intro s x hx;
  dsimp [step];
  simp_all only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, true_or]

/-- Monotone: `X ⊆ Y → step R X ⊆ step R Y`. -/
lemma step_mono {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
  Monotone (step R) := by
  intro X Y hXY; dsimp [step]
  exact Finset.union_subset_union hXY (fires_mono R hXY)
