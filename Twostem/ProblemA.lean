import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Basic
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

namespace ThreadA

/-! ## 基本定義 -/
/-
/-- ルールは `(親, 親, 子)` のタプル -/
abbrev Rule (α) := α × α × α

/-- `I` が `R`-閉：すべての `(a,b,r) ∈ R` で `a ∈ I ∧ b ∈ I → r ∈ I` -/
def isClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ t ∈ R, (t.1 ∈ I ∧ t.2.1 ∈ I) → t.2.2 ∈ I

/-- 閉包族：`V` の冪集合を `isClosed R` でフィルタ -/
noncomputable def family (V : Finset α) (R : Finset (Rule α)) :
    Finset (Finset α) := by
  classical
  exact V.powerset.filter (fun I => isClosed R I)

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
-/
/-- Barrier 仮定：Core が「大きく」「必ず含まれる」。 -/
structure BarrierHyp (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) : Prop where
  nonempty  : (ViolSet V R t0) ≠ ∅
  parents   : t0.1 ∈ Core V R t0 ∧ t0.2.1 ∈ Core V R t0
  child_out : t0.2.2 ∉ Core V R t0
  size_lb   : V.card ≤ 2 * (Core V R t0).card
  coreSub   : ∀ {I}, I ∈ ViolSet V R t0 → Core V R t0 ⊆ I

/-- 目標：違反する `R.erase t0`-閉集合はすべて「大きい」。 -/
def LargeWhenParents (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) : Prop :=
  ∀ I ∈ family V (R.erase t0),
    t0.1 ∈ I → t0.2.1 ∈ I → t0.2.2 ∉ I →
    (2 : Int) * (I.card : Int) ≥ (V.card : Int)

/-! ### 便利補題（必要最小限） -/

/-- Nat→Int の乗法キャスト。 -/
lemma int_cast_mul (m n : ℕ) :
  ((m * n : ℕ) : ℤ) = (m : ℤ) * (n : ℤ) := by
  -- `Nat.cast_mul` を Int に特化して単純化
  simp [Nat.cast_mul]

/-- （任意）ViolSet メンバの展開。 -/
lemma mem_ViolSet_iff
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) (I : Finset α) :
  I ∈ ViolSet V R t0 ↔
    I ∈ family V (R.erase t0) ∧ Violates t0 I := by
  -- 定義がちょうど `filter` なので、そのまま
  constructor
  · intro h
    constructor
    · simp [ViolSet] at h
      exact h.1
    · dsimp [ViolSet] at h
      simp at h
      exact h.2
  · intro h
    dsimp [ViolSet]
    simp
    exact h

/-! ## メイン定理 -/

/-- ★ Barrier から LargeWhenParents を導く。 -/
theorem LargeWhenParents_of_CoreBarrier
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hB : BarrierHyp V R t0) :
  LargeWhenParents V R t0 := by
  classical
  intro I hFam ha hb hr
  -- `I` が違反集合であることを `ViolSet` の条件に翻訳
  have hIin : I ∈ ViolSet V R t0 := by
    -- `I ∈ family V (R.erase t0)` かつ `Violates t0 I`
    -- から `filter` への挿入
    exact Finset.mem_filter.mpr ⟨hFam, And.intro ha (And.intro hb hr)⟩
  -- Core ⊆ I
  have hSub : Core V R t0 ⊆ I := hB.coreSub hIin
  -- |Core| ≤ |I|
  have h_le_card : (Core V R t0).card ≤ I.card := by
    exact Finset.card_le_card hSub
  -- 2|Core| ≤ 2|I|
  have h_mul : 2 * (Core V R t0).card ≤ 2 * I.card :=
    Nat.mul_le_mul_left 2 h_le_card
  -- 連鎖：|V| ≤ 2|Core| ≤ 2|I|
  have h_nat : V.card ≤ 2 * I.card := le_trans hB.size_lb h_mul
  -- Int に持ち上げ
  have h_int : (V.card : Int) ≤ ((2 * I.card : Nat) : Int) := by
    exact_mod_cast h_nat
  -- 右辺を `(2:Int) * (I.card:Int)` に書き換える
  have h_cast :
      ((2 * I.card : Nat) : Int) = (2 : Int) * (I.card : Int) := by
    simp [Nat.cast_mul]
  -- 置換してゴールの向きに合わせる
  have : (V.card : Int) ≤ (2 : Int) * (I.card : Int) := by
    calc
      (V.card : Int) ≤ ((2 * I.card : Nat) : Int) := h_int
      _ = (2 : Int) * (I.card : Int) := h_cast
  -- 形をゴールに合わせて終了
  exact this

end ThreadA
