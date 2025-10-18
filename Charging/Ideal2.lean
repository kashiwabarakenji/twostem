/-
  Generalized Theorem A (layer-density monotone ⇒ NDS upper bound)
  -- dependency order fixed: sum_wZ_all_eq_zero proved first (pairing),
  -- then PZ_eq_neg_TZ, wZ_eq_alt, TZ_closed_form, etc.
  * binder sums only:  ∑ k ∈ ...
  * no `simpa using`
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic
import LeanCopilot

open scoped BigOperators
open Finset

namespace LayerDensity

/-- Integer weight: w(n,k) = (2k - n) * C(n,k) as ℤ. -/
def wZ (n k : ℕ) : ℤ :=
  ((2 : ℤ) * (k : ℤ) - (n : ℤ)) * (Nat.choose n k : ℤ)

/-- Partial sum P(n,t) = ∑_{k=0..t} w(n,k) as ℤ. -/
def PZ (n t : ℕ) : ℤ :=
  ∑ k ∈ Icc 0 t, wZ n k

/-- Tail sum T(n,t) = ∑_{k=t+1..n} w(n,k) as ℤ. -/
def TZ (n t : ℕ) : ℤ :=
  ∑ k ∈ Icc (t+1) n, wZ n k

/-- 係数の反転等式（ℤ）:  `2*(n-k) - n = -(2*k - n)` （`k ≤ n`） -/
private lemma coeff_pair (n k : ℕ) (hkn : k ≤ n) :
    (2 * (↑(n - k) : ℤ) - (↑n)) = - (2 * (↑k) - (↑n)) := by
  -- ↑(n - k) = ↑n - ↑k にそろえる
  have hsub : (↑(n - k) : ℤ) = (↑n - ↑k) := Int.ofNat_sub hkn
  -- 2*(n-k) - n = 2n - 2k - n = n - 2k = -(2k - n)
  calc
    2 * (↑(n - k) : ℤ) - (↑n)
        = 2 * (↑n - ↑k) - (↑n) := by
              exact congrArg (fun z : ℤ => 2 * z - (↑n)) hsub
    _   = - (2 * (↑k) - (↑n)) := by ring

/-- `k` と `n-k` のペアで消えること：`wZ n k + wZ n (n-k) = 0` （`0 ≤ k ≤ n`）。 -/
lemma pair_cancel (n k : ℕ) (hk : k ∈ Icc 0 n) :
    wZ n k + wZ n (n - k) = 0 := by
  -- 前提から k ≤ n
  have hkn : k ≤ n := (mem_Icc.mp hk).right
  -- choose の対称性
  have hCh : Nat.choose n (n - k) = Nat.choose n k :=
    Nat.choose_symm (n := n) (k := k) hkn
  -- 係数の反転
  have hCf : (2 * (↑(n - k) : ℤ) - (↑n)) = - (2 * (↑k) - (↑n)) :=
    coeff_pair n k hkn
  -- 展開して 0 を出す
  unfold wZ
  -- 右項を係数と choose の両方で書き換え
  calc
    ((2 : ℤ) * (k : ℤ) - (n : ℤ)) * (Nat.choose n k : ℤ)
    + ((2 : ℤ) * (↑(n - k)) - (n : ℤ)) * (Nat.choose n (n - k) : ℤ)
      = ((2 : ℤ) * (k : ℤ) - (n : ℤ)) * (Nat.choose n k : ℤ)
        + (-(2 * (↑k) - (↑n))) * (Nat.choose n k : ℤ) := by
          congr 1
          calc ((2 : ℤ) * (↑(n - k)) - (n : ℤ)) * (Nat.choose n (n - k) : ℤ)
              = (-(2 * (↑k) - (↑n))) * (Nat.choose n (n - k) : ℤ) := by rw [hCf]
            _ = (-(2 * (↑k) - (↑n))) * (Nat.choose n k : ℤ) := by rw [hCh]
      _ = 0 := by ring

private lemma wZ_fixed_zero (n k : ℕ) (hkfix : n - k = k) : wZ n k = 0 := by
  unfold wZ
  -- 2k = n を整数で示す
  have : (2 : ℤ) * (k : ℤ) - (n : ℤ) = 0 := by
    -- ↑(n - k) = ↑n - ↑k
    have hsub : (↑(n - k) : ℤ) = (↑n - ↑k) := by
      apply Int.ofNat_sub
      apply Nat.le_of_lt_succ
      apply Nat.lt_succ_iff.mpr
      apply Nat.le_trans
      exact Nat.le_refl k
      omega
    -- n - k = k → n = 2k
    have hnk : (↑n : ℤ) = 2 * (↑k) := by
      have h1 : (↑n : ℤ) - (↑k) = (↑k) := by
        -- ↑(n - k) = ↑k
        have : (↑(n - k) : ℤ) = (↑k) := by
          exact congrArg (fun x : ℕ => (x : ℤ)) hkfix
        -- ↑n - ↑k = ↑(n-k) = ↑k
        apply Eq.trans
        exact id (Eq.symm hsub)
        exact this
      exact (eq_add_of_sub_eq h1) ▸ by ring
    -- 2k - n = 0
    exact congrArg (fun z : ℤ => (2 : ℤ) * (k : ℤ) - z) hnk ▸ by ring
  -- 係数が 0 なので積も 0
  exact this ▸ by
    simp_all only [zero_mul]

/-- 固定点 `n - k = k`（かつ `k ≤ n`）では `wZ n k = 0`. -/
private lemma wZ_fixed_zero_of_mem (n k : ℕ)
    (hk : k ∈ Icc 0 n) (hkfix : n - k = k) : wZ n k = 0 := by
  unfold wZ
  have hkn : k ≤ n := (mem_Icc.mp hk).right
  -- (↑(n - k) : ℤ) = ↑n - ↑k
  have hsub : (↑(n - k) : ℤ) = (↑n - ↑k) := Int.ofNat_sub hkn
  -- n - k = k  ⇒  ↑n - ↑k = ↑k  ⇒  ↑n = 2*↑k  ⇒  (2k - n) = 0
  have hnkz : (↑(n - k) : ℤ) = (↑k) := congrArg (fun x : ℕ => (x : ℤ)) hkfix
  have h2 : (↑n : ℤ) = 2 * (↑k) := by
    have : (↑n : ℤ) - (↑k) = (↑k) := by simpa [hsub] using hnkz
    have := eq_add_of_sub_eq this
    simpa [two_mul, add_comm] using this
  have hcoeff : (2 : ℤ) * (k : ℤ) - (n : ℤ) = 0 := by
    simpa [two_mul] using congrArg (fun z : ℤ => (2 : ℤ) * (k : ℤ) - z) h2
  simp [hcoeff]

/-- 合計和は 0：  ∑_{k=0}^n w(n,k) = 0（整数）。
    非従属版 `sum_ninvolution` を使う。 -/

lemma sum_wZ_all_eq_zero (n : ℕ) : (∑ k ∈ Icc 0 n, wZ n k) = 0 := by
  classical
  refine Finset.sum_involution
    (s := Icc 0 n)
    (f := fun k => wZ n k)
    (g := fun k _hk => n - k)
    -- hg₁: ペア消去
    (by
      intro k hk
      exact pair_cancel n k hk)
    -- hg₃: f k ≠ 0 → g k ≠ k  （対偶で：g k = k → f k = 0）
    (by
      intro k hk fk_ne hfix
      apply fk_ne
      --search_proof
       (wZ_fixed_zero_of_mem n k hk hfix))
    -- g_mem: 0 ≤ n - k ≤ n
    (by
      intro k hk
      exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.sub_le _ _⟩)
    -- hg₄: 反転（Icc 内なので k ≤ n）
    (by
      intro k hk
      have hkn : k ≤ n := (mem_Icc.mp hk).right
      simpa using (Nat.sub_sub_self hkn))

/-- 分割恒等式： `PZ = - TZ`（`t ≤ n`）。
    `∑_{0..n} w = P + T` と `sum_wZ_all_eq_zero` から。 -/
lemma PZ_eq_neg_TZ (n t : ℕ) (ht : t ≤ n) : PZ n t = - TZ n t := by
  classical
  -- Icc 0 n = Icc 0 t ∪ Icc (t+1) n（互いに素）
  have hsplit : (Icc 0 n : Finset ℕ) = (Icc 0 t) ∪ (Icc (t+1) n) := by
    ext k; constructor
    · intro hk
      rcases mem_Icc.mp hk with ⟨hk0, hkn⟩
      by_cases hkt : k ≤ t
      · exact mem_union.mpr (Or.inl (mem_Icc.mpr ⟨hk0, hkt⟩))
      · have : t + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_le hkt)
        exact mem_union.mpr (Or.inr (mem_Icc.mpr ⟨this, hkn⟩))
    · intro hk
      rcases mem_union.mp hk with hk | hk
      · exact (Icc_subset_Icc (le_of_eq rfl) ht) hk
      · rcases mem_Icc.mp hk with ⟨h1, h2⟩
        exact mem_Icc.mpr ⟨le_trans (Nat.zero_le _) h1, h2⟩
  have hdisj : Disjoint (Icc 0 t) (Icc (t+1) n) := by
    simp [Finset.disjoint_iff_ne]
    intros; omega
  -- ∑_{0..n} w = P + T
  have hsum :
    (∑ k ∈ Icc 0 n, wZ n k)
    = (∑ k ∈ Icc 0 t, wZ n k) + (∑ k ∈ Icc (t+1) n, wZ n k) := by
    conv_lhs => rw [hsplit]
    rw [sum_union hdisj]
  -- 左辺は 0
  have hzero : (∑ k ∈ Icc 0 n, wZ n k) = 0 := sum_wZ_all_eq_zero n
  -- したがって PZ = -TZ
  unfold PZ TZ
  have : (∑ k ∈ Icc 0 t, wZ n k) + (∑ k ∈ Icc (t+1) n, wZ n k) = 0 := by
    exact Eq.trans hsum.symm hzero
  exact eq_neg_iff_add_eq_zero.mpr this

/-- 重みの差分形：`1 ≤ k ≤ n` で
    `(2k - n)·C(n,k) = n·( C(n-1,k-1) - C(n-1,k) )` （整数版）。 -/
lemma wZ_eq_alt (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    wZ n k
  = (n : ℤ) * ( (Nat.choose (n-1) (k-1) : ℤ) - (Nat.choose (n-1) k : ℤ) ) := by
  -- k * C(n,k) = n * C(n-1,k-1)
  have h1_nat :
    k * Nat.choose n k = n * Nat.choose (n-1) (k-1) := by
    -- succ_mul_choose_eq : n * C(n-1, k-1) = C(n,k) * k
    -- を左右ひっくり返してから左辺を交換則で並べ替える
        have h := (Nat.succ_mul_choose_eq (n-1) (k-1)).symm
        -- h : k.succ? ではなく、ここはそのまま等式の左右です
        -- choose 側は既に (n-1),(k-1) で合っている
        -- 右辺 `Nat.choose n k * k` を `k * Nat.choose n k` にする
        rw [Nat.mul_comm] at h
        unfold Nat.choose
        simp_all only [Nat.succ_eq_add_one, Nat.sub_add_cancel]
        split
        next x x_1 => simp_all only [nonpos_iff_eq_zero, one_ne_zero]
        next x x_1 n =>
          simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, nonpos_iff_eq_zero, Nat.add_eq_zero,
            one_ne_zero, and_false]
        next x x_1 n
          k =>
          simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, add_le_add_iff_right, add_tsub_cancel_right]
          split
          next x_2
            x_3 =>
            simp_all only [zero_le, zero_add, Nat.choose_one_right, one_mul, Nat.choose_zero_right,
              mul_one]
            rw [add_comm]
          next x_2 x_3 n => simp_all only [Nat.succ_eq_add_one, nonpos_iff_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false]
          next x_2 x_3 n k =>
            simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right]
            exact h

  -- (n - k) * C(n,k) = n * C(n-1,k)
  have h2_nat :
    (n - k) * Nat.choose n k = n * Nat.choose (n-1) k := by
    -- succ_mul_choose_eq と choose_succ_right_eq を合成
    -- n * C(n-1,k) = C(n,k+1) * (k+1)
    have hA := Nat.succ_mul_choose_eq (n-1) k
    -- C(n,k+1) * (k+1) = C(n,k) * (n - k)
    have hB := Nat.choose_succ_right_eq (n := n) (k := k)
    -- 連鎖： n * C(n-1,k) = C(n,k) * (n-k)
    have hC : n * Nat.choose (n-1) k = Nat.choose n k * (n - k) := by
      unfold Nat.choose at hA hB
      unfold Nat.choose
      simp_all only [Nat.succ_eq_add_one]
      split
      next x x_1 => simp_all only [nonpos_iff_eq_zero, one_ne_zero]
      next x x_1 n_1
        heq =>
        simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right, zero_add, mul_zero,
          Nat.choose_zero_succ, add_zero, zero_mul, zero_eq_mul]
        split
        next x_2 x_3 x_4 heq_1 => simp_all only [Nat.add_eq_zero, one_ne_zero, and_false]
        next x_2 x_3 n heq_1 =>
          simp_all only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, zero_tsub, nonpos_iff_eq_zero, Nat.add_eq_zero,
            one_ne_zero, and_false]
        next x_2 x_3 n k heq_1 =>
          subst heq
          simp_all only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, zero_add, add_le_iff_nonpos_left,
            nonpos_iff_eq_zero, Nat.choose_self, mul_one, Nat.choose_succ_self, Nat.reduceAdd, Nat.choose_zero_succ,
            add_zero, zero_mul, tsub_self, mul_zero, one_ne_zero, or_true]
      next x x_1 n_1 k heq =>
        simp_all only [Nat.succ_eq_add_one, Nat.pred_eq_succ_iff, le_add_iff_nonneg_left, zero_le, add_le_add_iff_right,
          Nat.add_one_sub_one, add_tsub_cancel_right, Nat.reduceSubDiff]



    -- 左右を入れ替え、左側を (n-k) * C(n,k) に交換
    have hC' := hC.symm
    -- 右辺の `Nat.choose n k * (n - k)` を交換則で左に
    rw [Nat.mul_comm] at hC'
    exact hC'
  -- 以降は ℤ にキャストして整理
  have h1 :
    (k : ℤ) * (Nat.choose n k : ℤ)
      = (n : ℤ) * (Nat.choose (n-1) (k-1) : ℤ) := by
    exact_mod_cast h1_nat
  have h2 :
    ((n - k : ℕ) : ℤ) * (Nat.choose n k : ℤ)
      = (n : ℤ) * (Nat.choose (n-1) k : ℤ) := by
    exact_mod_cast h2_nat
  unfold wZ
  -- (2k - n)C = (k - (n-k))C = (k*C) - ((n-k)*C)
  calc
    ((2 : ℤ) * (k : ℤ) - (n : ℤ)) * (Nat.choose n k : ℤ)
        = (k : ℤ) * (Nat.choose n k : ℤ)
          - ((n - k : ℕ) : ℤ) * (Nat.choose n k : ℤ) := by
          ring_nf
          unfold Nat.choose
          unfold Nat.choose at h1_nat h2_nat
          simp_all only [Nat.cast_sub]
          split
          next x x_1 => simp_all only [nonpos_iff_eq_zero, one_ne_zero]
          next x x_1 n =>
            simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, nonpos_iff_eq_zero, Nat.add_eq_zero,
              one_ne_zero, and_false]
          next x x_1 n
            k =>
            simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, add_le_add_iff_right, Nat.cast_add,
              Nat.cast_one, add_tsub_cancel_right, add_sub_add_right_eq_sub, Nat.reduceSubDiff]
            split at h1_nat
            next x_2 x_3 =>
              split at h2_nat
              next x_4 x_5 x_6 heq => simp_all only [zero_add, one_ne_zero]
              next x_4 x_5 n heq =>
                simp_all only [zero_add, Nat.succ_eq_add_one, Nat.right_eq_add, le_refl, CharP.cast_eq_zero, Nat.choose_self,
                  Nat.cast_one, mul_one, sub_self, Nat.choose_succ_self, mul_zero, add_zero, tsub_self, one_mul, Int.reduceSub,
                  sub_zero]
              next x_4 x_5 n k
                heq =>
                simp_all only [zero_add, Nat.succ_eq_add_one, Nat.right_eq_add, le_add_iff_nonneg_left, zero_le,
                  CharP.cast_eq_zero, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, one_mul, Nat.choose_zero_right, mul_one,
                  sub_zero, tsub_zero]
                subst heq
                ring
            next x_2 x_3 n =>
              split at h2_nat
              next x_4 x_5 heq =>
                simp_all only [Nat.succ_eq_add_one, nonpos_iff_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false]
              next x_4 x_5 n_1 heq heq_1 =>
                simp_all only [Nat.succ_eq_add_one, nonpos_iff_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false]
              next x_4 x_5 n_1 k heq heq_1 =>
                simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub,
                  Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false]
            next x_2 x_3 n k =>
              split at h2_nat
              next x_4 x_5 heq =>
                simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right, Nat.cast_add, Nat.cast_one, Nat.choose_zero_right,
                  mul_one, add_sub_add_right_eq_sub, zero_mul, zero_eq_mul, Nat.add_eq_zero, one_ne_zero, and_false, and_self,
                  false_or]
              next x_4 x_5 n_1 heq heq_1 =>
                simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub,
                  Nat.add_eq_zero, one_ne_zero, and_false]
              next x_4 x_5 n_1 k_1 heq
                heq_1 =>
                simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub,
                  Nat.add_right_cancel_iff]
                subst heq_1 heq
                simp_all only [Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub]
                ring

    _ = (n : ℤ) * (Nat.choose (n-1) (k-1) : ℤ)
          - (n : ℤ) * (Nat.choose (n-1) k : ℤ) := by
          rw [h1, h2]
    _ = (n : ℤ) * ( (Nat.choose (n-1) (k-1) : ℤ)
                   - (Nat.choose (n-1) k : ℤ) ) := by
          ring

/-- Tail の閉じ式： `t ≤ n-1` で  `TZ n t = n * C(n-1, t)` （整数）。 -/
lemma TZ_closed_form (n t : ℕ) (ht : t ≤ n - 1) :
    TZ n t = (n : ℤ) * (Nat.choose (n - 1) t : ℤ) := by
  classical
  -- まず n=0 を先に片付ける
  by_cases h0 : n = 0
  · -- n = 0 なら ht : t ≤ 0 → t = 0
    subst h0
    have ht0 : t = 0 := by exact Nat.eq_zero_of_le_zero ht
    subst ht0
    -- 左辺は Icc (1) 0 上の和なので空和＝0、右辺も 0 · C(0,0) = 0
    simp [TZ]
  · -- 以降は n ≠ 0（すなわち 0 < n）として、元の証明を続ける
    have hnpos : 0 < n := Nat.pos_of_ne_zero h0

    unfold TZ
    -- （ここから先は、あなたの現行コードの流れで OK）

    -- integrand の差分形
    have hDiff :
        ∀ ⦃k⦄, k ∈ Icc (t+1) n →
          wZ n k
          = (n : ℤ) * ( (Nat.choose (n-1) (k-1) : ℤ) - (Nat.choose (n-1) k : ℤ) ) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have := (mem_Icc.mp hk).left; omega
      have hkn : k ≤ n := (mem_Icc.mp hk).right
      exact wZ_eq_alt n k hk1 hkn

    -- 線形分解
    have hsplit :
        (∑ k ∈ Icc (t+1) n,
          (n : ℤ) * ((Nat.choose (n-1) (k-1) : ℤ) - (Nat.choose (n-1) k : ℤ)))
        =
        (∑ k ∈ Icc (t+1) n, (n : ℤ) * (Nat.choose (n-1) (k-1) : ℤ))
        - (∑ k ∈ Icc (t+1) n, (n : ℤ) * (Nat.choose (n-1) k : ℤ)) := by
      rw [← sum_sub_distrib]
      congr 1; ext k; ring

    -- 左側を wZ に戻す
    have hTZ :
        (∑ k ∈ Icc (t+1) n, wZ n k)
        =
        (∑ k ∈ Icc (t+1) n,
          (n : ℤ) * ((Nat.choose (n-1) (k-1) : ℤ) - (Nat.choose (n-1) k : ℤ))) := by
      apply sum_congr rfl
      intro k hk; exact hDiff hk

    -- choose(n-1,n) = 0 は n>0 のときにだけ使う
    have hTop0 : (Nat.choose (n-1) n : ℤ) = 0 := by
      have : Nat.choose (n-1) n = 0 := by
        apply Nat.choose_eq_zero_of_lt
        exact Nat.sub_one_lt_of_lt hnpos
      exact_mod_cast this

    -- インデックスシフト S1
    have S1 :
      (∑ k ∈ Icc (t+1) n, (Nat.choose (n-1) (k-1) : ℤ))
        = (∑ j ∈ Icc t (n-1), (Nat.choose (n-1) j : ℤ)) := by

      apply sum_bij (fun k _ => k - 1) ?mem ?rewrite ?jj ?surj
      · intro k hk
        have : k ∈ Icc (t+1) n := hk
        have hk1 : t+1 ≤ k := (mem_Icc.mp this).left
        have hk2 : k ≤ n := (mem_Icc.mp this).right
        have : t ≤ k - 1 := Nat.le_pred_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) hk1)
        have : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hk2 1
        exact mem_Icc.mpr ⟨‹t ≤ k - 1›, ‹k - 1 ≤ n - 1›⟩

      · intro k _;
        rename_i ha₁
        intro a₂ ha₂ a
        simp_all only [mem_Icc, and_imp, Int.natCast_eq_zero]
        simp_all only [mem_Icc]
        obtain ⟨left, right⟩ := ha₁
        obtain ⟨left_1, right_1⟩ := ha₂
        omega
      · intro j hj;
        use j + 1
        simp_all only [mem_Icc, and_imp, Int.natCast_eq_zero, add_tsub_cancel_right, add_le_add_iff_right, true_and,
          exists_prop, and_true]
        obtain ⟨left, right⟩ := hj
        omega

      · -- surj: 任意の j∈[t,n-1] に対し k=j+1 を取れば k∈[t+1,n] かつ (k-1)=j
        intro j hj
        rcases mem_Icc.mp hj with ⟨hj₁, hj₂⟩
        simp_all only [mem_Icc, and_imp, Int.natCast_eq_zero]

    -- 望遠差分で共通部分が消える
    have hTel :
      (∑ k ∈ Icc (t+1) n, (Nat.choose (n-1) (k-1) : ℤ))
        - (∑ k ∈ Icc (t+1) n, (Nat.choose (n-1) k : ℤ))
      = (Nat.choose (n-1) t : ℤ) := by
      rw [S1]
      -- Icc t (n-1) = {t} ∪ Icc (t+1) (n-1) and Icc (t+1) n = Icc (t+1) (n-1) ∪ {n}
      have split1 : (Icc t (n-1) : Finset ℕ) = insert t (Icc (t+1) (n-1)) := by
        ext j; simp [mem_Icc]; omega
      have split2 : (Icc (t+1) n : Finset ℕ) = (Icc (t+1) (n-1)) ∪ {n} := by
        ext j; simp [mem_Icc]; omega
      rw [split1, sum_insert, split2]
      rw [sum_union (by simp [disjoint_singleton_right]; omega), sum_singleton]
      simp [hTop0];
      ring_nf
      simp_all only [union_singleton, mem_insert, mem_Icc, forall_eq_or_imp, Nat.choose_self, Nat.cast_one, sub_zero, mul_one,
        and_imp, not_and, not_le, tsub_lt_self_iff, zero_lt_one, and_self, implies_true, sum_insert, mul_zero, zero_add,
        Int.natCast_eq_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, and_true, not_false_eq_true,
        add_le_iff_nonpos_left]

    -- まとめ
    calc
      TZ n t
          = (∑ k ∈ Icc (t+1) n,
              (n : ℤ) * ((Nat.choose (n-1) (k-1) : ℤ) - (Nat.choose (n-1) k : ℤ))) := by
            rw [← hTZ]
            exact rfl
      _ = (n : ℤ) * ((∑ k ∈ Icc (t+1) n, (Nat.choose (n-1) (k-1) : ℤ))
                      - (∑ k ∈ Icc (t+1) n, (Nat.choose (n-1) k : ℤ))) := by
            --rw [mul_sum]


            have hsplit' :
                ∑ k ∈ Icc (t + 1) n,
                  (@Nat.cast ℤ instNatCastInt n) * (@Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) - @Nat.cast ℤ instNatCastInt ((n - 1).choose k))
                  =
                (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt n) * @Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)))
                - (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt n) * @Nat.cast ℤ instNatCastInt ((n - 1).choose k)) := by

              let fs := (Finset.sum_sub_distrib
                  (s := Icc (t + 1) n)
                  (f := fun k => (@Nat.cast ℤ instNatCastInt n) * (@Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) : ℤ))
                  (g := fun k => (@Nat.cast ℤ instNatCastInt n) * (@Nat.cast ℤ instNatCastInt ((n - 1).choose k) : ℤ)))
              simp_all only [mem_Icc, and_imp, Int.natCast_eq_zero]


            -- ② 定数 ↑n を和の外へ（左右それぞれ）
            have hpullA :
                (∑ k ∈ Icc (t + 1) n, (↑n) * (↑((n - 1).choose (k - 1)) : ℤ))
                  =
                (@Nat.cast ℤ instNatCastInt n) * (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) : ℤ)) := by
              simp [Finset.mul_sum]

            have hpullB :
                (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt n) * (@Nat.cast ℤ instNatCastInt ((n - 1).choose k) : ℤ))
                  =
                (@Nat.cast ℤ instNatCastInt n) * (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt ((n - 1).choose k) : ℤ)) := by
              simp [Finset.mul_sum]

            -- ③ まとめて目標の形へ
            show ∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt n * (@Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) - ↑((n - 1).choose k)) =
              @Nat.cast ℤ instNatCastInt n * (∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) - ∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose k))
            calc
              ∑ k ∈ Icc (t + 1) n,
                  (@Nat.cast ℤ instNatCastInt n) * (@Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) -  @Nat.cast ℤ instNatCastInt ((n - 1).choose k))
                  =
                (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt n) * @Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)))
                - (∑ k ∈ Icc (t + 1) n, (@Nat.cast ℤ instNatCastInt n) * @Nat.cast ℤ instNatCastInt ((n - 1).choose k)) := hsplit'
              _ = (@Nat.cast ℤ instNatCastInt n) * (∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)))
                  - (@Nat.cast ℤ instNatCastInt n) * (∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose k)) := by
                rw [hpullA, hpullB]
              _ = @Nat.cast ℤ instNatCastInt n * (∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose (k - 1)) - ∑ k ∈ Icc (t + 1) n, @Nat.cast ℤ instNatCastInt ((n - 1).choose k)) := by
                exact Eq.symm
                  (Int.mul_sub (↑n) (∑ k ∈ Icc (t + 1) n, ↑((n - 1).choose (k - 1))) (∑ k ∈ Icc (t + 1) n, ↑((n - 1).choose k)))


      _ = (n : ℤ) * (Nat.choose (n-1) t : ℤ) := by
            rw [hTel]

/-- 尾和の下界： `t ≤ n-1` で `TZ n t ≥ n` （整数）。 -/
lemma TZ_ge_n (n t : ℕ) (ht : t ≤ n - 1) : TZ n t ≥ (n : ℤ) := by
  -- T = n * C(n-1,t) ≥ n（C ≥ 1）
  have hT := TZ_closed_form n t ht
  -- choose の正性：0 ≤ t ≤ n-1
  have hposNat : 0 < Nat.choose (n-1) t := by
    apply Nat.choose_pos
    omega
  have hpos : (Nat.choose (n-1) t : ℤ) ≥ 1 := by omega
  -- 仕上げ
  have : TZ n t = (n : ℤ) * (Nat.choose (n - 1) t : ℤ) := hT
  calc
    TZ n t = (n : ℤ) * (Nat.choose (n - 1) t : ℤ) := this
    _ ≥ (n : ℤ) * 1 := by
          exact mul_le_mul_of_nonneg_left hpos (by exact_mod_cast (Nat.zero_le n))
    _ = (n : ℤ) := by ring

/-- `PZ = -TZ` と `TZ ≥ n` から `PZ ≤ -n`。 -/
lemma PZ_le_neg_n (n t : ℕ) (ht : t ≤ n - 1) : PZ n t ≤ - (n : ℤ) := by
  have hPN := PZ_eq_neg_TZ n t (le_trans ht (Nat.pred_le _))
  have hT  := TZ_ge_n n t ht
  -- `PZ = -TZ` を代入
  have : PZ n t = - TZ n t := hPN
  -- 単調性（両辺に `-` を掛ける）
  exact
    calc
      PZ n t = - TZ n t := this
      _      ≤ - (n : ℤ) := by exact neg_le_neg hT

-- 望遠和（半開区間版）：すべての n, k≤n で成立
-- ∑_{t=k}^{n-1} (s t - s (t+1)) = s k - s n
open scoped BigOperators

open scoped BigOperators

private lemma telesc_Ico (s : ℕ → ℚ) {n k : ℕ} (hk : k ≤ n) :
    (∑ t ∈ Finset.Ico k n, (s t - s (t+1))) = s k - s n := by
  classical
  -- n に関する帰納法（強い形にするため k を戻す）
  revert k
  refine Nat.rec ?base ?step n
  · -- base: n = 0
    intro k
    simp_all only [Nat.zero_eq, nonpos_iff_eq_zero, le_refl, Ico_eq_empty_of_le, sum_sub_distrib, sum_empty, sub_self]
  · -- step: n → n.succ
    · intro n ih hk
      rename_i k
      classical
      by_cases hkn : k = n+1
      · -- 右端と左端が一致（空和）
        subst hkn
        simp
      · -- 右端を1つ伸ばすと {n} だけが増える
        have hk_le : k ≤ n :=
          Nat.le_of_lt_succ (lt_of_le_of_ne hk (by simpa using hkn))
        have ih' := ih (by exact hk_le)
        have hnot : n ∉ Finset.Ico k n := by
          -- Ico k n の「< n」条件を使って排中
          simp [Finset.mem_Ico]
        -- Ico k (n+1) = insert n (Ico k n)
        have hIco :
            Finset.Ico k (n+1) = insert n (Finset.Ico k n) := by
          -- `insert_Ico_right_eq_Ico_succ : insert n (Ico k n) = Ico k (succ n)`
          simpa [Nat.succ_eq_add_one] using
            (Finset.insert_Ico_right_eq_Ico_succ (a := k) (b := n) hk_le).symm
        calc
          ∑ t ∈ Finset.Ico k (n+1), (s t - s (t+1))
              = ∑ t ∈ insert n (Finset.Ico k n), (s t - s (t+1)) := by
                simp [hIco]
          _ = (s n - s (n+1)) + ∑ t ∈ Finset.Ico k n, (s t - s (t+1)) := by
                simpa using
                  (Finset.sum_insert (s := Finset.Ico k n) (a := n)
                    (f := fun t => (s t - s (t+1))) hnot)
          _ = (s n - s (n+1)) + (s k - s n) := by
                simp [ih']
          _ = s k - s (n+1) := by
                -- 加減の並べ替えで整理
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

-- n>0 のときだけ、Icc k (n-1) と Ico k n は同じ集合
private lemma Icc_pred_eq_Ico {k n : ℕ} (hn : 0 < n) :
    (Finset.Icc k (n-1) : Finset ℕ) = Finset.Ico k n := by
  classical
  ext t; constructor
  · intro ht
    rcases Finset.mem_Icc.mp ht with ⟨hkt, htn1⟩
    exact Finset.mem_Ico.mpr ⟨hkt, lt_of_le_of_lt htn1 (Nat.sub_one_lt_of_lt hn)⟩
  · intro ht
    rcases Finset.mem_Ico.mp ht with ⟨hkt, htn⟩
    exact Finset.mem_Icc.mpr ⟨hkt, Nat.le_pred_of_lt htn⟩



/-- NDS（ℚ）： `s : ℕ → ℚ` を 0..n で評価し，NDS(s) = ∑ (wZ : ℤ as ℚ) * s k。 -/
def NDSQ (n : ℕ) (s : ℕ → ℚ) : ℚ :=
  ∑ k ∈ Icc 0 n, (wZ n k : ℚ) * s k

/-- NDS の分部和（Abel）： `NDS = ∑_{t=0..n-1} (s t - s (t+1)) * PZ n t` -/
lemma NDSQ_by_parts (n : ℕ) (s : ℕ → ℚ) :
    NDSQ n s
  = ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ) := by
  classical
  have telesc_of_pos (hnpos : 0 < n) :
  ∀ k, k ≤ n →
    s k = s n + (∑ t ∈ Finset.Icc k (n-1), (s t - s (t+1))) := by
    intro k hk
    -- まず Ico 版を作ってから Icc に戻す
    have hIco := telesc_Ico s hk
    have h' : s k = s n + ∑ t ∈ Finset.Ico k n, (s t - s (t+1)) := by
      have := congrArg (fun x => s n + x) hIco
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
    simpa [Icc_pred_eq_Ico (k:=k) hnpos] using h'
  -- s k = s n + ∑_{t=k..n-1} (s t - s (t+1)) の望遠分解を使う
  by_cases h0 : n = 0
  · -- n = 0 は両辺とも 0 になる
    subst h0
    have hsum0 : (∑ k ∈ Icc 0 0, (wZ 0 k : ℚ)) = 0 := by
      exact mod_cast (sum_wZ_all_eq_zero 0)
    have wZ00_zero : (wZ 0 0 : ℚ) = 0 := by
      simpa using hsum0
    simp [NDSQ, PZ, wZ00_zero]
  · -- n ≠ 0
    have hnpos : 0 < n := Nat.pos_of_ne_zero h0
    unfold NDSQ
    -- k = n の項を分離
    have decomp :
      (∑ k ∈ Icc 0 n, ((wZ n k : ℚ) * s k))
      = (∑ k ∈ Icc 0 (n-1), ((wZ n k : ℚ) * s k)) + ((wZ n n : ℚ) * s n) := by
      have hsplit : (Icc 0 n : Finset ℕ) = (Icc 0 (n-1)) ∪ {n} := by
        classical
        ext k; constructor
        · intro hk
          rcases mem_Icc.mp hk with ⟨h0k, hk_le_n⟩
          by_cases hkn : k = n
          · simp [hkn]
          ·
            have hk_le_pred : k ≤ n - 1 :=
              Nat.le_pred_of_lt (lt_of_le_of_ne hk_le_n hkn)
            have : k ∈ Icc 0 (n-1) := mem_Icc.mpr ⟨h0k, hk_le_pred⟩
            simp [this, hkn]
        · intro hk
          have : k ∈ Icc 0 (n-1) ∨ k ∈ ({n} : Finset ℕ) := by
            simp_all only [sum_sub_distrib, forall_const, union_singleton, mem_insert, mem_Icc, zero_le, true_and, mem_singleton]
            cases hk with
            | inl h =>
              subst h
              simp_all only [or_true]
            | inr h_1 => simp_all only [true_or]

          rcases this with hleft | hright
          · rcases mem_Icc.mp hleft with ⟨h0k, hk_le_pred⟩
            have hk_le_n : k ≤ n := le_trans hk_le_pred (Nat.sub_le _ _)
            exact mem_Icc.mpr ⟨h0k, hk_le_n⟩
          · have : k = n := by simpa using hright
            subst this
            exact mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩
      have hdisj : Disjoint (Icc 0 (n-1)) ({n} : Finset ℕ) := by
        classical
        refine Finset.disjoint_left.2 ?_
        intro a ha ha'
        have : a = n := by simpa using ha'
        have : n ≤ n - 1 := by
          let mi := (mem_Icc.mp ha)
          rw [this] at mi
          exact mi.right
        exact (lt_irrefl n) (lt_of_le_of_lt this (Nat.sub_one_lt_of_lt hnpos))
      rw [hsplit, sum_union hdisj]; simp
    -- s k を望遠和形にする
    have step :
      (∑ k ∈ Icc 0 (n-1), ((wZ n k : ℚ) * s k))
      = (∑ k ∈ Icc 0 (n-1),
          (wZ n k : ℚ) * ( s n + (∑ t ∈ Icc k (n-1), (s t - s (t+1))) )) := by
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by
        exact le_trans (mem_Icc.mp hk).right (Nat.sub_le n 1)
      rw [telesc_of_pos hnpos k hk']
    -- 分配展開
    have step2 :
      (∑ k ∈ Icc 0 (n-1),
        (wZ n k : ℚ) * ( s n + (∑ t ∈ Icc k (n-1), (s t - s (t+1))) ))
      = s n * (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ))
        + (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1)))) := by
      -- まず和の中身で分配、次に和の外へ定数を出す
      have hdistrib :
        (∑ k ∈ Icc 0 (n-1),
          ((wZ n k : ℚ) * s n + (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1))))) =
        (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * s n)
          + (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1)))) := by
        simp [sum_add_distrib]
      have hpull :
        (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * s n)
          = s n * (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ)) := by
        -- ∑ f k * a = (∑ f k) * a; さらに交換法則で a * ∑ f k へ
        simpa [mul_comm] using
          (sum_mul (Icc 0 (n-1)) (fun k => (wZ n k : ℚ)) (s n)).symm
      -- まとめ
      calc
        (∑ k ∈ Icc 0 (n-1),
          (wZ n k : ℚ) * ( s n + (∑ t ∈ Icc k (n-1), (s t - s (t+1))) ))
            = (∑ k ∈ Icc 0 (n-1),
                ((wZ n k : ℚ) * s n
                  + (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1))))) := by
              apply sum_congr rfl; intro k hk; ring
        _ = s n * (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ))
              + (∑ k ∈ Icc 0 (n-1),
                  (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1)))) := by
          simpa [hpull] using hdistrib
    -- ∑_{0..n-1} w = -w n を使って s n の項を消す
    have hsum0 : (∑ k ∈ Icc 0 n, (wZ n k : ℚ)) = 0 := by
      exact mod_cast (sum_wZ_all_eq_zero n)
    have hn_split : (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ)) = - (wZ n n : ℚ) := by
      have hsplit : (Icc 0 n : Finset ℕ) = (Icc 0 (n-1)) ∪ {n} := by
        classical
        ext k; constructor
        · intro hk
          rcases mem_Icc.mp hk with ⟨h0k, hk_le_n⟩
          by_cases hkn : k = n
          · simp [hkn]
          ·
            have hk_le_pred : k ≤ n - 1 :=
              Nat.le_pred_of_lt (lt_of_le_of_ne hk_le_n hkn)
            have : k ∈ Icc 0 (n-1) := mem_Icc.mpr ⟨h0k, hk_le_pred⟩
            simp [this, hkn]
        · intro hk
          have : k ∈ Icc 0 (n-1) ∨ k ∈ ({n} : Finset ℕ) := by
            simp_all only [sum_sub_distrib, forall_const, union_singleton, mem_insert, mem_Icc, zero_le, true_and, mem_singleton]
            cases hk with
            | inl h =>
              subst h
              simp_all only [or_true]
            | inr h_1 => simp_all only [true_or]
          rcases this with hleft | hright
          · rcases mem_Icc.mp hleft with ⟨h0k, hk_le_pred⟩
            have hk_le_n : k ≤ n := le_trans hk_le_pred (Nat.sub_le _ _)
            exact mem_Icc.mpr ⟨h0k, hk_le_n⟩
          · have : k = n := by simpa using hright
            subst this
            exact mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩
      have hdisj : Disjoint (Icc 0 (n-1)) ({n} : Finset ℕ) := by
        classical
        refine Finset.disjoint_left.2 ?_
        intro a ha ha'
        have : a = n := by simpa using ha'
        have : n ≤ n - 1 := by
          let mi := (mem_Icc.mp ha)
          rw [this] at mi
          exact mi.right
        exact (lt_irrefl n) (lt_of_le_of_lt this (Nat.sub_one_lt_of_lt hnpos))
      have : (∑ k ∈ Icc 0 n, (wZ n k : ℚ)) =
              (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ)) + (wZ n n : ℚ) := by
        rw [hsplit, sum_union hdisj]; simp
      have : 0 = (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ)) + (wZ n n : ℚ) := by
        rw [hsum0] at this; exact this
      linarith
    calc
      NDSQ n s
          = (∑ k ∈ Icc 0 (n-1), ((wZ n k : ℚ) * s k)) + ((wZ n n : ℚ) * s n) := by
            rw [NDSQ, decomp]
      _ = s n * (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ))
          + (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1))))
          + ((wZ n n : ℚ) * s n) := by
            rw [step, step2]
      _ = (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1)))) := by
        -- s n の項が消える
        rw [hn_split]; ring
      _ = ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ) := by
        -- 二重和の順序交換 → PZ の定義
        have expand :
          (∑ k ∈ Icc 0 (n-1), (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1))))
          = (∑ k ∈ Icc 0 (n-1), ∑ t ∈ Icc 0 (n-1),
              if k ≤ t then (wZ n k : ℚ) * (s t - s (t+1)) else 0) := by
          classical
          apply sum_congr rfl
          intro k hk
          -- 内側の和を filter 化して if に変換
          have hFilt :
            (Icc k (n-1) : Finset ℕ) =
              (Icc 0 (n-1)).filter (fun t => k ≤ t) := by
            classical
            ext t; constructor
            · intro ht
              rcases mem_Icc.mp ht with ⟨hkt, htn1⟩
              exact mem_filter.mpr
                ⟨mem_Icc.mpr ⟨Nat.zero_le _, htn1⟩, hkt⟩
            · intro h
              rcases mem_filter.mp h with ⟨htIcc0, hk_le_t⟩
              rcases mem_Icc.mp htIcc0 with ⟨_, ht_le_n1⟩
              exact mem_Icc.mpr ⟨hk_le_t, ht_le_n1⟩
          calc
            (wZ n k : ℚ) * (∑ t ∈ Icc k (n-1), (s t - s (t+1)))
                = ∑ t ∈ Icc k (n-1), (wZ n k : ℚ) * (s t - s (t+1)) := by
                  simp
                  have hL :
                      (↑(wZ n k) : ℚ) *
                        ((∑ x ∈ Icc k (n - 1), s x) - (∑ x ∈ Icc k (n - 1), s (x + 1)))
                      =
                      (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s x)
                      - (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s (x + 1)) := by
                    simp [mul_sub]

                  have hA :
                      (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s x)
                      =
                      ∑ x ∈ Icc k (n - 1), (↑(wZ n k) : ℚ) * s x := by
                    simp [Finset.mul_sum]

                  have hB :
                      (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s (x + 1))
                      =
                      ∑ x ∈ Icc k (n - 1), (↑(wZ n k) : ℚ) * s (x + 1) := by
                    simp [Finset.mul_sum]

                  calc
                    (↑(wZ n k) : ℚ) *
                        (∑ x ∈ Icc k (n - 1), s x - ∑ x ∈ Icc k (n - 1), s (x + 1))
                        = (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s x)
                          - (↑(wZ n k) : ℚ) * (∑ x ∈ Icc k (n - 1), s (x + 1)) := hL
                    _ = (∑ t ∈ Icc k (n - 1), (↑(wZ n k) : ℚ) * s t)
                        - (∑ t ∈ Icc k (n - 1), (↑(wZ n k) : ℚ) * s (t + 1)) := by
                          simp [hA, hB]
                    _ = ∑ t ∈ Icc k (n - 1),
                          ((↑(wZ n k) : ℚ) * s t - (↑(wZ n k) : ℚ) * s (t + 1)) := by
                          -- （差の総和）↔（総和の差）
                          have := Finset.sum_sub_distrib
                            (s := Icc k (n - 1))
                            (f := fun t => (↑(wZ n k) : ℚ) * s t)
                            (g := fun t => (↑(wZ n k) : ℚ) * s (t + 1))
                          simp
                    _ = ∑ t ∈ Icc k (n - 1), (↑(wZ n k) : ℚ) * (s t - s (t + 1)) := by
                          simp [mul_sub]

            _ = ∑ t ∈ (Icc 0 (n-1)).filter (fun t => k ≤ t),
                    (wZ n k : ℚ) * (s t - s (t+1)) := by
                  simp [hFilt]
            _ = ∑ t ∈ Icc 0 (n-1),
                    (if k ≤ t
                      then (wZ n k : ℚ) * (s t - s (t+1))
                      else 0) := by
                  simp [Finset.sum_filter]

        -- 交換
        rw [expand, sum_comm]
        -- 各 t ごとに if を Icc 0 t で切る
        apply sum_congr rfl
        intro t ht
        have ht' : t ≤ n - 1 := (mem_Icc.mp ht).right
        have filter_sum :
          (∑ k ∈ Icc 0 (n-1),
              if k ≤ t then (wZ n k : ℚ) * (s t - s (t+1)) else 0)
          = (∑ k ∈ Icc 0 t, (wZ n k : ℚ) * (s t - s (t+1))) := by
          classical
          have : (filter (fun k => k ≤ t) (Icc 0 (n-1))) = Icc 0 t := by
            ext k; constructor
            · intro hk
              rcases mem_filter.mp hk with ⟨hkIcc, hk_le_t⟩
              rcases mem_Icc.mp hkIcc with ⟨h0k, hk_le_n1⟩
              exact mem_Icc.mpr ⟨h0k, hk_le_t⟩
            · intro hk
              rcases mem_Icc.mp hk with ⟨h0k, hk_le_t⟩
              have hk_le_n1 : k ≤ n - 1 := le_trans hk_le_t ht'
              have hkIcc : k ∈ Icc 0 (n-1) := mem_Icc.mpr ⟨h0k, hk_le_n1⟩
              exact mem_filter.mpr ⟨hkIcc, hk_le_t⟩
          -- sum over filter = sum with if
          simp [← sum_filter, this]
        -- 係数 (s t - s (t+1)) を外へ
        -- ∑ k (wZ n k : ℚ) * C = (∑ k (wZ n k : ℚ)) * C = C * (∑ k ...)
        -- 後者の形に合わせて mul_comm
        have : (∑ k ∈ Icc 0 t, (wZ n k : ℚ) * (s t - s (t+1)))
                = (s t - s (t+1)) * (∑ k ∈ Icc 0 t, (wZ n k : ℚ)) := by
          simpa [mul_comm] using
            (sum_mul (Icc 0 t) (fun i => (wZ n i : ℚ)) (s t - s (t + 1))).symm
        simpa [this, PZ] using filter_sum

/-- 一般化定理 A：`s 0 ≥ s 1 ≥ … ≥ s (n-1)` なら `NDS ≤ n (s n - s 0)` 。-/

theorem TheoremA
    (n : ℕ) (s : ℕ → ℚ)
    (hmono : ∀ k, k ≤ n-1 → s k ≥ s (k+1)) :
    NDSQ n s ≤ (n : ℚ) * (s n - s 0) := by
  classical
  -- Abel 型表示
  have hA := NDSQ_by_parts n s
  -- PZ ≤ -n を使った majorization
  have hP : ∀ t ∈ Icc 0 (n-1), (PZ n t : ℚ) ≤ - (n : ℚ) := by
    intro t ht
    have ht' : t ≤ n-1 := (Finset.mem_Icc.mp ht).right
    exact (Int.cast_le.mpr (PZ_le_neg_n n t ht')).trans_eq rfl  -- `mod_cast` 相当

  -- λ_t ≥ 0
  have h : ∀ t ∈ Icc 0 (n-1), 0 ≤ (s t - s (t+1)) := by
    intro t ht
    exact sub_nonneg.mpr (hmono t ((Finset.mem_Icc.mp ht).right))

  -- まず n=0 を別処理（この場合は -n = 0 なので望遠和は不要）
  by_cases h0 : n = 0
  · subst h0
    -- 右辺は 0
    have : (0 : ℚ) * (s 0 - s 0) = 0 := by ring
    have hmaj0 :
      (∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (PZ 0 t : ℚ))
        ≤ (∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (-(0:ℚ))) := by
      apply Finset.sum_le_sum
      intro t ht
      have : (PZ 0 t : ℚ) ≤ 0 := hP t (by simpa using ht)   -- ← ここ
      have : (s t - s (t+1)) * (PZ 0 t : ℚ)
                ≤ (s t - s (t+1)) * 0 := by
        exact mul_le_mul_of_nonneg_left this (by
          apply h; simpa using ht)                           -- ← ここ
      simpa using this

    calc
      NDSQ 0 s
          = ∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (PZ 0 t : ℚ) := hA
      _ ≤ ∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (-(0:ℚ)) := hmaj0
      _ = 0 := by simp
      _ ≤ 0 := le_rfl
      _ = (0 : ℚ) * (s 0 - s 0) := by simp

  -- 以降 n>0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
    -- majorization: 各項で (s t - s (t+1)) * PZ ≤ (s t - s (t+1)) * (-n)
    have hmaj :
      (∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ))
      ≤ (∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (-(n : ℚ))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hP t ht) (h t ht)

    -- 望遠和の評価（n>0 なので Icc→Ico に変換してから）
    have htel :
      (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) = s 0 - s n := by
      have hI : (Icc 0 (n-1) : Finset ℕ) = Ico 0 n :=
        Icc_pred_eq_Ico (k := 0) hnpos
      -- Ico 版の望遠和
      have := telesc_Ico s (k := 0) (n := n) (Nat.zero_le _)
      simpa [hI] using this

    -- 仕上げ
    calc
      NDSQ n s
          = ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ) := hA
      _ ≤ ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (-(n : ℚ)) := hmaj
      _ = (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) * (-(n : ℚ)) := by
            simpa using
              (Finset.sum_mul (Icc 0 (n-1)) (fun t => (s t - s (t+1))) (-(n:ℚ))).symm
      _ = (-(n : ℚ)) * (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) := by
            ring
      _ = (-(n : ℚ)) * (s 0 - s n) := by
            simp [htel]
      _ = (n : ℚ) * (s n - s 0) := by ring

/-- 全和が 0、末項が `n` なので、最後直前の部分和は `-n`。 -/
lemma PZ_last_eq_neg_n (n : ℕ) :
  PZ n (n - 1) = - (n : ℤ) := by
  classical
  -- n = 0 は別処理（どちらも 0）
  cases n with
  | zero =>
    -- ここは PZ 0 (0 - 1) があなたの定義で 0 になること（通常は `range 0` の和で 0）
    -- を使って閉じます。`simp` の代わりに明示的に書くなら：
    --   unfold PZ; -- 定義展開
    --   -- `range 0` の和は 0
    --   exact by decide  -- あるいは `rfl` / `simp` で落ちるはず
    -- 右辺も `- (0:ℤ) = 0`
    -- ここは環境依存ですが、だいたい `rfl` か `simp` で閉まります。
    -- 低レベル記法で：
    have : PZ 0 0 = (0:ℤ) := by
      -- PZ 0 0 の定義が「最初の1項の和（k=0）」なら、その値は 0 です。
      -- そうでなく「range 0 の和」定義ならもちろん 0。
      -- あなたの PZ 定義に合わせてここを置換してください。
      -- 仮に「range 0 の和」なら：
      --   unfold PZ; simp
      exact rfl
    -- `0 - 1 = 0`（自然数の飽和引き算）に合わせる
    have : PZ 0 (0 - 1) = 0 := by
      -- `by simpa` を避ける場合：
      -- `Nat.zero_sub 1 = 0` が使える環境ならそれで書き換えて上の等式へ
      -- なければ PZ の定義で直接 0 を出して構いません
      exact this
    -- 右辺は 0
    have : - (0 : ℤ) = (0 : ℤ) := by
      -- `simp` で落ちますが、明示するなら：
      exact rfl
    -- 仕上げ
    -- exact by rw [this₁, this₂] の形にしてください
    (expose_names; exact this_1)

  | succ m =>
    -- 記法
    let w : ℕ → ℤ := fun k => ((2 : ℤ) * k - (Nat.succ m)) * (Nat.choose (Nat.succ m) k : ℤ)

    -- 全体の重み和が 0 という恒等式（既出の補題を使うか、左右対称性で証明ずみのはず）
    --   ∑_{k=0}^{m+1} w k = 0
    have hsum_all : ∑ k ∈ Finset.range (Nat.succ m + 1), w k = 0 := by
      -- ここはあなたのファイルにある「PZ の基本恒等式（全体の和が 0）」に合わせて置き換えてください。
      -- 例：重みの反転対消で証明済みの補題。
      -- w と wZ が一致なら
      have hdom : (Icc 0 m.succ : Finset ℕ) = range (m.succ + 1) := by
        ext k
        constructor
        · intro hk
          -- k ∈ Icc 0 m.succ → k ≤ m.succ → k < m.succ + 1
          simp_all only [Nat.succ_eq_add_one, mem_Icc, zero_le, true_and, mem_range]
          omega

        · intro hk
          -- k < m.succ + 1 → 0 ≤ k ∧ k ≤ m.succ
          apply Finset.mem_Icc.mpr
          constructor
          · exact Nat.zero_le k
          · exact mem_range_succ_iff.mp hk

      have h0 : ∑ k ∈ range (m.succ + 1), wZ (m.succ) k = 0 := by
        -- さきの hdom を n := m.succ で使う
        have := sum_wZ_all_eq_zero (m.succ)
        simp_all only [Nat.succ_eq_add_one]

      let sz := sum_wZ_all_eq_zero (Nat.succ m + 1)
      simp_all only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, w]
      exact h0

    -- 末項 k = n の重みは n：w n n = n
    have w_last : w (Nat.succ m) = (Nat.succ m : ℤ) := by
      -- choose (n) (n) = 1 と (2n - n) = n を使うだけ
      -- 展開して：
      -- w (m+1) = ((2:ℤ)*(m+1) - (m+1)) * (Nat.choose (m+1) (m+1) : ℤ)
      --         = ((m+1):ℤ) * 1 = (m+1):ℤ
      -- この行は `simp [w, Nat.choose_self, two_mul, add_comm, add_left_comm, add_assoc]` で済みますが
      -- `simp` を避けるなら逐次 rw して構いません。
      simp_all only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.choose_self, mul_one, w]
      ring

    -- 「全和 = 0」から「最後の手前までの和 = - 最後の項」を取り出す
    have hsum_init :
      ∑ k ∈ Finset.range (Nat.succ m), w k = - (Nat.succ m : ℤ) := by
      -- range_succ で全和を「初めの n 項 + 最後の 1 項」に分ける
      have := Finset.sum_range_succ (f := w) m.succ
      -- `sum_range_succ : (∑ k < n+1, f k) = (∑ k < n, f k) + f n`
      -- 今は `n = m.succ` なので
      --   ∑_{k=0}^{m+1} w k = (∑_{k=0}^{m} w k) + w (m+1)
      -- これを hsum_all と w_last に代入して解く
      -- （`rw` 連鎖で丁寧に）
      -- 1) hsum_all を左辺に、2) w_last を右端に、3) 右辺を移項
      rw [hsum_all] at this
      rw [@eq_neg_iff_add_eq_zero]
      symm
      rw [w_last] at this
      exact this

    -- PZ の定義と一致させる
    -- ふつう PZ (m+1) ((m+1)-1) = ∑_{k=0}^{m} w k
    have hPZ :
      PZ (Nat.succ m) (Nat.succ m - 1) = ∑ k ∈ Finset.range (Nat.succ m), w k := by
      -- あなたの PZ 定義（部分和定義）を `unfold PZ` で展開して、この形に揃えてください
      have PZ_eq :
          PZ m.succ (m.succ - 1) = ∑ k ∈ range m.succ, wZ m.succ k := by
        -- (m.succ - 1) + 1 = m.succ
        have ht1 : (m.succ - 1) + 1 = m.succ := by
          -- succ_pred_eq_of_pos : 0 < a → (a - 1).succ = a
          -- を +1 版に直して使います
          have : (m.succ - 1).succ = m.succ :=
            Nat.succ_pred_eq_of_pos (Nat.succ_pos m)
          simp [Nat.succ_eq_add_one]

        -- PZ を定義で展開して上限を書き換え
        -- これで右辺が `∑ k ∈ range m.succ, wZ m.succ k` になります
        -- （PZ の定義を `unfold` / `simp` のどちらで展開するかは
        --   あなたの定義の置き方に合わせて調整してください）
        -- 例：
        --   unfold PZ
        --   rw [ht1]
        -- または
        --   simp [PZ, ht1]
        simp [PZ]
        simp_all only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.choose_self, mul_one,
          neg_add_rev, Int.reduceNeg, add_tsub_cancel_right, w]
        congr
        ext a : 1
        simp_all only [Int.reduceNeg, mem_Icc, zero_le, true_and, mem_range]
        apply Iff.intro
        · intro a_1
          linarith
        · intro a_1
          omega


      -- つぎに integrand を w に差し替え
      have integrand_swap :
          (∑ k ∈ range m.succ, wZ m.succ k)
        = (∑ k ∈ range m.succ, w k) := by
        -- 各項で wZ m.succ k = w k を示して総和の同値を書き換え
        refine Finset.sum_congr rfl ?_
        intro k hk
        -- 定義通り一致
        -- wZ の定義が ((2 : ℤ) * k - (m.succ : ℤ)) * (m.succ.choose k : ℤ)
        -- であれば、ちょうど w と一致します
        dsimp [wZ, w]

      -- 仕上げ： 2 つを連結
      have : PZ m.succ (m.succ - 1) = ∑ k ∈ range m.succ, w k := by
        -- PZ を wZ の和に直した等式と，integrand を w に差し替えた等式を合成
        -- PZ_eq : PZ = Σ wZ, integrand_swap : Σ wZ = Σ w
        -- よって PZ = Σ w
        -- （`rw` を2回）
        calc
          PZ m.succ (m.succ - 1)
              = ∑ k ∈ range m.succ, wZ m.succ k := PZ_eq
          _   = ∑ k ∈ range m.succ, w k       := integrand_swap

      -- 望んでいる結論
      exact this

    -- 仕上げ
    -- 2つの等式を合成
    -- PZ n (n-1) = (初めの n 項の和) = -n
    -- つまりゴール
    have : PZ (Nat.succ m) (Nat.succ m - 1) = - (Nat.succ m : ℤ) := by
      -- `calc` でつなぐか、`rw [hPZ, hsum_init]`
      simp_all only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.choose_self, mul_one, neg_add_rev, Int.reduceNeg,
        add_tsub_cancel_right, w]
    -- n = m+1 に戻す
    exact this

theorem TheoremA_upto_nsub2
    (n : ℕ) (s : ℕ → ℚ)
    (hmono' : ∀ k, k ≤ n-2 → s k ≥ s (k+1)) :
    NDSQ n s ≤ (n : ℚ) * (s n - s 0) := by
  classical
  -- Abel 型表示
  have hA := NDSQ_by_parts n s

  -- PZ の上界：PZ(n,t) ≤ -n （特に t = n-1 では等号）
  have hP : ∀ t ∈ Icc 0 (n-1), (PZ n t : ℚ) ≤ - (n : ℚ) := by
    intro t ht
    have ht' : t ≤ n-1 := (Finset.mem_Icc.mp ht).right
    -- Int 版の不等式を ℚ へキャストする
    have := PZ_le_neg_n n t ht'
    -- Int.cast ≤ へ通し、右辺は `rfl` で -n へ
    exact (Int.cast_le.mpr this).trans_eq rfl

  -- まず n=0 を枝分け（元の証明と同様）
  by_cases h0 : n = 0
  · -- n=0
    subst h0
    -- Icc 0 (0-1) = Icc 0 0 = {0}
    have hPZ0 : ∀ t ∈ Icc 0 0, (PZ 0 t : ℚ) = 0 := by
      intro t ht
      -- ここで t = 0 を取り出す
      have ht0 : t = 0 := by
        have h := Finset.mem_Icc.mp ht
        exact Nat.le_antisymm h.2 h.1
      subst ht0
      -- PZ(0,0) = -0 = 0
      -- （あなたの環境の補題名に合わせて：例えば `PZ_at_top_eq_neg_n` の n=0 特例など）
      -- なければ定義から直接 0 を計算して OK
      exact by
        -- 例：`by rfl` や `by simp` で落ちる形にしておく
        simp  -- ← PZ の定義に合わせて
        exact rfl

    -- すると和は 0
    have hsum0 :
      (∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (PZ 0 t : ℚ)) = 0 := by
      -- 台集合は {0}、各項は hPZ0 で 0
      simp_all only [zero_tsub, nonpos_iff_eq_zero, zero_add, ge_iff_le, forall_eq, Icc_self, mul_zero, sum_const_zero,
        mem_singleton, CharP.cast_eq_zero, neg_zero, le_refl, implies_true, Rat.intCast_eq_zero, sum_singleton,
        Int.cast_zero]

    -- 右辺も 0 * (s0 - s0) = 0
    have rhs0 : (0 : ℚ) * (s 0 - s 0) = 0 := by ring

    -- 仕上げ
    calc
      NDSQ 0 s
          = ∑ t ∈ Icc 0 (0-1), (s t - s (t+1)) * (PZ 0 t : ℚ) := hA
      _ = 0 := hsum0
      _ ≤ 0 := le_rfl
      _ = (0 : ℚ) * (s 0 - s 0) := by simp

  -- n > 0 の場合
  · have hnpos : 0 < n := Nat.pos_of_ne_zero h0

    -- 主要評価：各 t で
    --   (s_t - s_{t+1}) * PZ(n,t) ≤ (s_t - s_{t+1}) * (−n)
    -- を示して総和にかける。
    -- t = n-1 だけは PZ = −n が等号なので、単調性は不要。
    have hmaj :
      (∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ))
      ≤ (∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (-(n : ℚ))) := by
      apply Finset.sum_le_sum
      intro t ht
      -- t が最上段かどうかで分岐
      by_cases htop : t = n-1
      · -- 最上段 t = n-1：PZ(n,n-1) = -n の等号
        subst htop
        -- Int 版の等式を ℚ へキャスト
        have hEqZ : (PZ n (n-1) : ℤ) = - (n : ℤ) := by
          exact_mod_cast PZ_last_eq_neg_n n
        have hEqQ : (PZ n (n-1) : ℚ) = - (n : ℚ) := by
          exact_mod_cast hEqZ
        -- 等式なので、そのまま ≤ が成り立つ
        -- （係数の符号は関係なし）
        calc
           (s (n - 1) - s (n - 1 + 1)) * ↑(PZ n (n - 1))
              =
          (s (n-1) - s n) * (PZ n (n-1) : ℚ) := by
                simp_all only [ge_iff_le, mem_Icc, zero_le, true_and, le_refl, and_self, Int.cast_neg, Int.cast_natCast, mul_neg,
                  neg_inj, mul_eq_mul_right_iff, sub_right_inj, Rat.natCast_eq_zero, or_false]
                rw [tsub_add_cancel_of_le hnpos]
           _  = (s (n-1) - s n) * (-(n : ℚ)) := by
                    -- 置換
                    exact congrArg (fun x => (s (n-1) - s n) * x) hEqQ
           _ ≤ (s (n-1) - s n) * (-(n : ℚ)) := by
                    exact le_of_eq rfl
           _ = (s (n - 1) - s (n - 1 + 1)) * -↑n := by
                simp_all only [ge_iff_le, mem_Icc, zero_le, true_and, le_refl, and_self, Int.cast_neg, Int.cast_natCast, mul_neg,
                  neg_inj, mul_eq_mul_right_iff, sub_right_inj, Rat.natCast_eq_zero, or_false]
                rw [Nat.sub_add_cancel hnpos]

      · -- t ≤ n-2 の範囲：ここでだけ単調性を使う
        have t_le_n1 : t ≤ n-1 := (Finset.mem_Icc.mp ht).right
        have t_le_n2 : t ≤ n-2 := by
          -- t ≤ n-1 かつ t ≠ n-1 ⇒ t ≤ n-2
          -- つまり `t < n-1` を示してから `Nat.le_of_lt_succ`
          have : t < n-1 := lt_of_le_of_ne t_le_n1 htop
          apply  Nat.le_of_lt_succ
          simp_all only [ge_iff_le, mem_Icc, zero_le, true_and, and_self, Nat.succ_eq_add_one]
          omega
        -- λ_t ≥ 0
        have hnn : 0 ≤ (s t - s (t+1)) :=
          sub_nonneg.mpr (hmono' t t_le_n2)
        -- 係数非負で両辺に掛ける
        exact mul_le_mul_of_nonneg_left (hP t ht) hnn

    -- 望遠和（Icc→Ico）
    have htel :
      (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) = s 0 - s n := by
      have hI : (Icc 0 (n-1) : Finset ℕ) = Ico 0 n :=
        Icc_pred_eq_Ico (k := 0) hnpos
      -- Ico 版の望遠和（既存補題）
      have htel' := telesc_Ico s (k := 0) (n := n) (Nat.zero_le _)
      -- 書き換え
      -- `by` で等式の両辺を `hI` に沿って置換
      simp_all only [ge_iff_le, Nat.Ico_zero_eq_range, mem_range, mul_neg, sum_neg_distrib, sum_sub_distrib]

    -- 仕上げ（元の TheoremA と同じ）
    calc
      NDSQ n s
          = ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (PZ n t : ℚ) := hA
      _ ≤ ∑ t ∈ Icc 0 (n-1), (s t - s (t+1)) * (-(n : ℚ)) := hmaj
      _ = (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) * (-(n : ℚ)) := by
            -- 定数 (−n) を外へ
            -- `Finset.sum_mul` の左右向きを揃える
            have := (Finset.sum_mul (Icc 0 (n-1)) (fun t => (s t - s (t+1))) (-(n:ℚ))).symm
            exact this
      _ = (-(n : ℚ)) * (∑ t ∈ Icc 0 (n-1), (s t - s (t+1))) := by
            ring
      _ = (-(n : ℚ)) * (s 0 - s n) := by
            exact congrArg (fun x => (-(n:ℚ)) * x) htel
      _ = (n : ℚ) * (s n - s 0) := by
            ring



theorem TheoremA_nonpos_of_equal_ends_upto_nsub2
  (n : ℕ) (s : ℕ → ℚ)
  (hmono' : ∀ k, k ≤ n-2 → s k ≥ s (k+1))
  (hends : s 0 = s n) :
  NDSQ n s ≤ 0 := by
  have hA : NDSQ n s ≤ (n : ℚ) * (s n - s 0) :=
    TheoremA_upto_nsub2 n s hmono'
  -- s n - s 0 = 0  （端点が等しい）
  have hdiff0 : s n - s 0 = 0 := by
    -- sub_eq_zero.mpr : a = b → a - b = 0
    exact sub_eq_zero.mpr (Eq.symm hends)
  -- (n) * (s n - s 0) = 0
  have hmul0 : (n : ℚ) * (s n - s 0) = 0 := by
    have : (n : ℚ) * (s n - s 0) = (n : ℚ) * 0 := by
      exact congrArg (fun x => (n : ℚ) * x) hdiff0
    -- (n)*0 = 0
    exact Eq.trans this (by ring)
  -- 連鎖
  exact le_trans hA (by exact le_of_eq hmul0)


end LayerDensity
