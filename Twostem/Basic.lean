import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Ring.Rat
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

abbrev Rule (α) := α × α × α

/-- `I` が `R`-閉：すべての `(a,b,r) ∈ R` で `a ∈ I ∧ b ∈ I → r ∈ I` -/
def isClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ t ∈ R, (t.1 ∈ I ∧ t.2.1 ∈ I) → t.2.2 ∈ I

/-- Provide decidable instance for isClosed using classical reasoning -/
noncomputable instance isClosedDecidable (R : Finset (Rule α)) (I : Finset α) : Decidable (isClosed R I) := by
  classical infer_instance

/-- 閉包族：`V` の冪集合を `isClosed R` でフィルタ -/
noncomputable def family (V : Finset α) (R : Finset (Rule α)) : Finset (Finset α) := by
  classical
  exact V.powerset.filter (fun I => isClosed R I)

/-- NDS₂ 便利定義：`∑ (2|I| - |V|)` -/
def NDS2 (V : Finset α) (F : Finset (Finset α)) : Int :=
  ∑ I ∈ F, ((2 : Int) * (I.card : Int) - (V.card : Int))

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

/- 総量（in-star 上の重みの総和） -/
--def totalWeight (R : Finset (Rule α)) (r : α) (w : Rule α → ℚ) : ℚ := ∑ t ∈ InStar R r, w t

/-- 容量：LocalLPFeasible より，任意の親 x ∈ P で ∑_{t∈S} 1_{xが親}·w(t) ≤ 1。 -/ lemma capacity_at_parent {V : Finset α} {R : Finset (Rule α)} {r x : α} {w : Rule α → ℚ} (hLP : LocalLPFeasible V R r w) (hx : x ∈ ParentSet V R r) : (∑ t ∈ InStar R r, if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤ 1 := by exact (hLP.2) x hx

--def S : Finset (Rule α) := InStar (R.erase t0) t0.2.2
--def P : Finset α := ParentSet V (R.erase t0) t0.2.2
--def T : ℚ := totalWeight (R.erase t0) t0.2.2 w

/-
def t0_2_2 : α := t0.2.2
local notation "S" => (InStar (R.erase t0) t0.2.2)
local notation "P" => ParentSet V (R.erase t0) t0.2.2
local notation "T" => totalWeight (R.erase t0) t0.2.2 w
#check t0_2_2
-/
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

omit [DecidableEq α] in
lemma family_mono
  (V : Finset α) {R₁ R₂ : Finset (Rule α)} (hR : R₁ ⊆ R₂) :
  family V R₂ ⊆ family V R₁ := by
  classical
  intro I hI
  have hPowI : I ∈ V.powerset := (Finset.mem_filter.mp hI).1
  have hClosedR₂ : isClosed R₂ I := (Finset.mem_filter.mp hI).2  -- ← ここ！直接 .2 で取れる！

  -- `R₁ ⊆ R₂` より、`R₂`-閉 ⇒ `R₁`-閉
  have hClosedR₁ : isClosed R₁ I := by
    intro t ht hparents
    exact hClosedR₂ t (hR ht) hparents

  -- フィルタに戻す
  apply Finset.mem_filter.mpr
  constructor
  · exact hPowI
  · exact hClosedR₁


 -- メンバー条件をほどく have hPowI : I ∈ V.powerset := (Finset.mem_filter.mp hI).1 have hClosedR₂ : isClosed R₂ I := by have : decide (isClosed R₂ I) = true := by sorry --(Finset.mem_filter.mp hI).2 simp_all only [Finset.mem_powerset, decide_eq_true_eq] -- `R₁ ⊆ R₂` より、`R₂`-閉 ⇒ `R₁`-閉 have hClosedR₁ : isClosed R₁ I := by intro t ht hparents exact hClosedR₂ t (hR ht) hparents -- フィルタに戻す apply Finset.mem_filter.mpr constructor · exact hPowI · exact hClosedR₁

/-- 追加族（削除後に新たに現れる閉包集合の全体） -/
noncomputable def addedFamily (V : Finset α) (R : Finset (α × α × α)) (t0 : α × α × α) :
    Finset (Finset α) :=
  (family V (R.erase t0)) \ (family V R)

lemma family_drop_partition
  (V : Finset α) (R : Finset (α × α × α)) (t0 : α × α × α) :
  (family V (R.erase t0))
    = (family V R) ∪ (addedFamily V R t0)
  ∧ Disjoint (family V R) (addedFamily V R t0) := by
  classical
  dsimp [addedFamily]
  constructor
  · -- A = B ∪ (A \ B)
    refine Eq.symm (Finset.union_sdiff_of_subset ?_)
    dsimp [family]
    apply family_mono V
    exact Finset.erase_subset t0 R

  · -- B ∩ (A \ B) = ∅
    exact Finset.disjoint_sdiff

/-- 「`t0=(a,b,r)` を破る」：`a,b ∈ I` かつ `r ∉ I` -/
def Violates (t0 : Rule α) (I : Finset α) : Prop :=
  t0.1 ∈ I ∧ t0.2.1 ∈ I ∧ t0.2.2 ∉ I

/-- `R.erase t0`-閉かつ `t0` を破る集合全体 -/
noncomputable def ViolSet (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) :
    Finset (Finset α) := by
  classical
  exact (family V (R.erase t0)).filter (fun I => Violates t0 I)

/-- 交わり核（違反集合群の共通部分）。空なら便宜上 `V` とする。 -/
noncomputable def Core (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) :
    Finset α := by
  classical
  let C := ViolSet V R t0
  exact V
