
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Twostem.General
import Twostem.Basic
import LeanCopilot

universe u
variable {α : Type u} [DecidableEq α]

def InStar (R : Finset (Rule α)) (r : α) : Finset (Rule α) := R.filter (fun t => t.2.2 = r) /-- 親集合：r の in-star 中に親として現れる点の集合（V で制限） -/

def ParentSet (V : Finset α) (R : Finset (Rule α)) (r : α) : Finset α := V.filter (fun x => ∃ t ∈ InStar R r, t.1 = x ∨ t.2.1 = x) /-- χ_I(x) = 1 if x ∈ I, else 0（ℚ 版） -/

--定義にMathlib.Algebra.Order.Ring.Ratが必要。
def chi (I : Finset α) (x : α) : ℚ := if x ∈ I then 1 else 0

lemma chi_sum_card (V : Finset α) (I : Finset α) (h : I ⊆ V) :
  (∑ x ∈ V, chi I x) = (I.card : ℚ) := by
  classical
  dsimp [chi]
  rw [← @Finset.sum_filter _ _ V _ (· ∈ I) _ (fun _ => 1)]
  · simp_all only [Finset.sum_const, nsmul_eq_mul, mul_one, Rat.natCast_inj]
    congr
    ext a : 1
    simp_all only [Finset.mem_filter, and_iff_right_iff_imp]
    intro a_1
    exact h a_1


/-- 和の入替：`∑_{I∈A} ∑_{x∈V} χ_I(x) = ∑_{I∈A} |I|` -/
lemma swap_chi_sum (V : Finset α) (A : Finset (Finset α)) (hA: ∀ I ∈ A, I ⊆ V) :
  (∑ I ∈ A, ∑ x ∈ V, chi I x)
  =
  (∑ I ∈ A, (I.card : ℚ)) := by
  classical
  -- 外側の和で `chi_sum_card` を適用するだけ
  refine Finset.sum_congr rfl ?_
  intro I hI
  apply chi_sum_card V I
  exact hA I hI


def totalWeight (R : Finset (Rule α)) (r : α) (w : Rule α → ℚ) : ℚ := ∑ t ∈ InStar R r, w t

/-- 親ペア指示子：両親が I に入っていれば 1、そうでなければ 0（ℚ 版） -/
def indParents (t : Rule α) (I : Finset α) : ℚ := if (t.1 ∈ I ∧ t.2.1 ∈ I) then 1 else 0 /-- x が t の親かどうかの指示子（ℚ 版, 0/1） -/

def isParentOf (x : α) (t : Rule α) : ℚ := if (t.1 = x ∨ t.2.1 = x) then 1 else 0

lemma isParentOf_nonneg (x : α) (t : Rule α) : 0 ≤ isParentOf x t := by
  unfold isParentOf; by_cases h : (t.1 = x ∨ t.2.1 = x) <;> simp [h]

/-- LP 可行性（非負・親容量 ≤ 1） -/
def LocalLPFeasible (V : Finset α) (R : Finset (Rule α)) (r : α) (w : Rule α → ℚ) : Prop :=
  (∀ t, t ∈ InStar R r → 0 ≤ w t) ∧ (∀ x ∈ ParentSet V R r, (∑ t ∈ InStar R r, if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤ 1)

/-- AM–GM 型：1_{a,b ⊆ I} ≤ (χ_I(a)+χ_I(b))/2。 -/

lemma indParents_le_half (t : Rule α) (I : Finset α) : indParents t I ≤ (chi I t.1 + chi I t.2.1) / 2 := by
  unfold indParents chi
  by_cases h1 : t.1 ∈ I
  · by_cases h2 : t.2.1 ∈ I
    · simp_all only [and_true, ↓reduceIte]
      obtain ⟨fst, snd⟩ := t
      obtain ⟨fst_1, snd⟩ := snd
      simp_all only
      rw [propext (one_le_div₀ rfl)]
      have : (1 : ℚ) + (1 : ℚ) = (2 : ℚ) := by
        exact one_add_one_eq_two
      rw [this]

    · simp_all only [and_false, ↓reduceIte, add_zero, one_div, inv_nonneg]
      obtain ⟨fst, snd⟩ := t
      obtain ⟨fst_1, snd⟩ := snd
      simp_all only
      rfl
  · by_cases h2 : t.2.1 ∈ I
    · simp_all only [and_true, ↓reduceIte, zero_add, one_div, inv_nonneg]
      obtain ⟨fst, snd⟩ := t
      obtain ⟨fst_1, snd⟩ := snd
      simp_all only
      rfl

    · simp [h1, h2]
