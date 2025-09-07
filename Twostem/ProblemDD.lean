import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Int
--import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring.RingNF
import Twostem.General
import Twostem.Basic
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

namespace ThreadDD
open scoped BigOperators
variable {α : Type u} [DecidableEq α]

/- ルール (親, 親, 子) -/

--abbrev Rule (α) := α × α × α

variable
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (A : Finset (Finset α)) (w : Rule α → ℚ)

/- in-star：子が r のルール集合 -/

--def InStar (R : Finset (Rule α)) (r : α) : Finset (Rule α) := R.filter (fun t => t.2.2 = r) /-- 親集合：r の in-star 中に親として現れる点の集合（V で制限） -/

--def ParentSet (V : Finset α) (R : Finset (Rule α)) (r : α) : Finset α := V.filter (fun x => ∃ t ∈ InStar R r, t.1 = x ∨ t.2.1 = x) /-- χ_I(x) = 1 if x ∈ I, else 0（ℚ 版） -/

/- χ_I(x) = 1 if x ∈ I, else 0（ℚ 版） -/

--def chi (I : Finset α) (x : α) : ℚ := if x ∈ I then 1 else 0

-- 0/1 の非負性
lemma chi_nonneg (I : Finset α) (x : α) : 0 ≤ chi I x := by
  unfold chi; by_cases hx : x ∈ I <;> simp [hx]





-- S の左親/右親は P に入る（V で制限しているため、端点が V に入る仮定が必要）
lemma leftParent_mem_P
  (htS : ∀ t : Rule α, t ∈ (InStar (R.erase t0) t0.2.2) → t.1 ∈ V)
  {t : Rule α} (h : t ∈ (InStar (R.erase t0) t0.2.2)) :
  t.1 ∈ ParentSet V (R.erase t0) t0.2.2 := by
  have hex : ∃ t' ∈ (InStar (R.erase t0) t0.2.2), t'.1 = t.1 ∨ t'.2.1 = t.1 := ⟨t, h, Or.inl rfl⟩
  unfold ParentSet
  have hv : t.1 ∈ V := htS t h
  simp [Finset.mem_filter, hv, hex]

lemma rightParent_mem_P
  (htS : ∀ t, t ∈ (InStar (R.erase t0) t0.2.2) → t.2.1 ∈ V)
  {t : Rule α} (h : t ∈ (InStar (R.erase t0) t0.2.2)) :
  t.2.1 ∈  ParentSet V (R.erase t0) t0.2.2:= by
  have hex : ∃ t' ∈ (InStar (R.erase t0) t0.2.2), t'.1 = t.2.1 ∨ t'.2.1 = t.2.1 := ⟨t, h, Or.inr rfl⟩
  unfold ParentSet
  have hv : t.2.1 ∈ V := htS t h
  simp [Finset.mem_filter, hv, hex]

-- 片親の持ち上げ（x 側へ）
lemma parentLift_left
  (htS : ∀ t, t ∈ (InStar (R.erase t0) t0.2.2) → t.1 ∈ V)
  (t : Rule α) (ht : t ∈ (InStar (R.erase t0) t0.2.2)) :
  (∑ I ∈ A, chi I t.1)
    ≤ ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t := by
  classical
  -- 各 I ごとに単項が全和に ≤
  apply @finset_sum_le_finset_sum _ _ Rat _ _ _ (fun I => chi I t.1) (fun I => ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t) A

  intro I hI
  have hxP : t.1 ∈ ParentSet V (R.erase t0) t0.2.2 := by exact leftParent_mem_P V R t0 htS ht
  have hnonneg :
      ∀ x ∈ ParentSet V (R.erase t0) t0.2.2, 0 ≤ chi I x * isParentOf x t := by
    intro x hx; exact mul_nonneg (chi_nonneg I x) (isParentOf_nonneg x t)
  -- 1 項 ≤ 全和
  have hsingle :
      chi I t.1 * isParentOf t.1 t ≤ ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t := by
    exact Finset.single_le_sum hnonneg hxP
  -- isParentOf t.1 t = 1
  have hone : isParentOf t.1 t = 1 := by
    unfold isParentOf; simp
  -- 目標へ
  calc
    chi I t.1
        = chi I t.1 * (isParentOf t.1 t) := by simp_all only [Prod.forall, mul_one]
    _ ≤ ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t := hsingle

lemma parentLift_right
  (htS : ∀ t, t ∈ (InStar (R.erase t0) t0.2.2) → t.2.1 ∈ V)
  (t : Rule α) (ht : t ∈ (InStar (R.erase t0) t0.2.2)) :
  (∑ I ∈ A, chi I t.2.1)
    ≤ ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t := by
  classical
  refine Finset.sum_le_sum ?_
  intro I hI
  have hxP : t.2.1 ∈ ParentSet V (R.erase t0) t0.2.2 := by exact rightParent_mem_P V R t0 htS ht
  have hnonneg :
      ∀ x ∈ ParentSet V (R.erase t0) t0.2.2, 0 ≤ chi I x * isParentOf x t := by
    intro x hx; exact mul_nonneg (chi_nonneg I x) (isParentOf_nonneg x t)
  have hsingle :
      chi I t.2.1 * isParentOf t.2.1 t ≤ ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t := by
    exact Finset.single_le_sum hnonneg hxP
  have hone : isParentOf t.2.1 t = 1 := by
    unfold isParentOf; by_cases h : (t.1 = t.2.1 ∨ t.2.1 = t.2.1)
    · simp
    · simp_all only [Prod.forall, or_true, not_true_eq_false]
  simp_all only [Prod.forall, mul_one]


-- (a+b)/2 の総和を分解
lemma sum_pair_halves (t : Rule α) :
  (∑ I ∈ A, (chi I t.1 + chi I t.2.1) / 2)
    = (1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
    + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1) := by
  classical
  -- 各 I の被積分を (…)/2 = …/2 + …/2 と分解
  have h1 :
    (∑ I ∈ A, (chi I t.1 + chi I t.2.1) / 2)
      = (∑ I ∈ A, (chi I t.1) / 2) + (∑ I ∈ A, (chi I t.2.1) / 2) := by
    -- sum of (u+v) = sum u + sum v, かつ add_div
    have : (fun I => (chi I t.1 + chi I t.2.1) / 2)
         = (fun I => (chi I t.1) / 2 + (chi I t.2.1) / 2) := by

      funext I;
      show (chi I t.1 + chi I t.2.1) / 2 = chi I t.1 / 2 + chi I t.2.1 / 2
      dsimp [chi]
      rw [Rat.div_def]
      obtain ⟨fst, snd⟩ := t
      obtain ⟨fst_1, snd⟩ := snd
      simp_all only
      split
      next h =>
        simp_all only [one_div]
        split
        next h_1 =>
          simp_all only [one_div]
          rw [add_mul, one_mul]
          rfl
        next h_1 =>
          simp_all only [add_zero, one_mul, zero_div]
          rfl
      next h =>
        simp_all only [zero_add, ite_mul, one_mul, zero_mul, zero_div]
        split
        next h_1 =>
          simp_all only [one_div]
          rfl
        next h_1 => simp_all only [zero_div]

    simp_all only
    obtain ⟨fst, snd⟩ := t
    obtain ⟨fst_1, snd⟩ := snd
    simp_all only
    rw [Finset.sum_add_distrib]


  -- a/2 = (1/2)*a へ置換して係数を前へ
  calc
    (∑ I ∈ A, (chi I t.1 + chi I t.2.1) / 2)
        = (∑ I ∈ A, (chi I t.1) / 2) + (∑ I ∈ A, (chi I t.2.1) / 2) := h1
    _ = (1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
        + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1) := by
      simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]

-- メイン補題
lemma sum_over_t_using_capacity
  (hLP : LocalLPFeasible V (R.erase t0) t0.2.2 w)
  (hTpos : 0 < T)
  -- 支持仮定（必要）
  (hSuppL : ∀ t, t ∈ (InStar (R.erase t0) t0.2.2) → t.1 ∈ V)
  (hSuppR : ∀ t, t ∈ (InStar (R.erase t0) t0.2.2) → t.2.1 ∈ V) :
  ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, indParents t I)
    ≤ (1 / T) * ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x := by
  classical
  -- Step 1: indParents ≤ 1/2(∑χ) + 1/2(∑χ)
  have hStep1 :
    ∀ t ∈ (InStar (R.erase t0) t0.2.2),
      (∑ I ∈ A, indParents t I)
        ≤ (1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
          + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1) := by
    intro t ht
    have hLe :
      (∑ I ∈ A, indParents t I)
        ≤ (∑ I ∈ A, (chi I t.1 + chi I t.2.1) / 2) := by
      refine Finset.sum_le_sum ?_
      intro I hI
      exact indParents_le_half t I
    apply le_trans hLe
    rw [sum_pair_halves A t]

  -- Step 2: 各 t の不等式に (w t)/T ≥ 0 を掛けて合算
    -- Step 2: 点ごとの形にしてから線形性で並べ替える
  have hStep2_pointwise :
    ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, indParents t I)
      ≤ ∑ t ∈ (InStar (R.erase t0) t0.2.2),
          ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1)
          + (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
    classical
    refine Finset.sum_le_sum ?_
    intro t ht
    -- (w t)/T ≥ 0
    have hwT_nonneg : 0 ≤ (w t) / T := by
      have hw_nonneg : 0 ≤ w t := (hLP.1) t ht
      have h1 : 0 ≤ (1 : ℚ) / T := by
        have hpos : 0 < (1 : ℚ) / T := by
          exact div_pos (by exact rfl) hTpos
        exact le_of_lt hpos
      have : 0 ≤ (1 / T) * w t := mul_nonneg h1 hw_nonneg
      -- 書き換え：(w t)/T = (1/T) * w t
      have hrew : (w t) / T = (1 / T) * w t := by
        -- 係数の並べ替え
        have : (w t) / T = (w t) * (1 / T) := by
          -- div_eq_mul_inv と可換性で
          simp_all only [Prod.forall, one_div, inv_nonneg, inv_pos, mul_nonneg_iff_of_pos_left]
          exact rfl
        exact by
          -- より簡潔に
          have : (w t) / T = (1 / T) * w t := by
            simp [div_eq_mul_inv, mul_comm]
          exact this
      -- 0 ≤ (w t)/T
      exact
        (by
          -- 0 ≤ (1/T)*w t かつ (w t)/T = (1/T)*w t
          -- 等式で書き換えてから示す
          -- `calc` で明示
          calc
            0 ≤ (1 / T) * w t := this
            _ = (w t) / T := by
              simp [div_eq_mul_inv, mul_comm]
        )
    -- a ≤ b ⇒ c*a ≤ c*b （c≥0）を適用
    have h := hStep1 t ht
    have h' := mul_le_mul_of_nonneg_left h hwT_nonneg
    -- 右辺を展開して形を合わせる
    have hreshape :
      (w t) / T
        * ((1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
          + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1))
      =
      ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
      + ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
      calc
        (w t) / T
          * ((1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
            + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1))
            = (w t) / T * ((1/2 : ℚ) * (∑ I ∈ A, chi I t.1))
              + (w t) / T * ((1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1)) := by
              -- c*(x+y) = c*x + c*y
              simp [mul_add]
        _ = ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
            + ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
              -- 係数の並べ替え
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    -- まとめて点ごとの不等式を完成
    exact
      (by
        calc
          (w t) / T * (∑ I ∈ A, indParents t I)
              ≤ (w t) / T
                * ((1/2 : ℚ) * (∑ I ∈ A, chi I t.1)
                  + (1/2 : ℚ) * (∑ I ∈ A, chi I t.2.1)) := h'
          _ = ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
              + ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := hreshape
      )

  -- 線形性で右辺を希望の形に展開
  have hStep2 :
    ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, indParents t I)
      ≤ (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1))
        + (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
    classical
    -- まず「∑ g(t)」の形にした不等式
    have := hStep2_pointwise
    -- ∑(p t + q t) = ∑p t + ∑q t
    have hsum_add :
      ∑ t ∈ (InStar (R.erase t0) t0.2.2),
          ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1)
          + (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1))
      =
      (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
      + (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
      -- membership 付きの sum でも `sum_add_distrib` が使えます
      exact Finset.sum_add_distrib
    -- 左右の (1/2) を外へ
    have hfactor :
      (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
        = (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1)) := by
      calc
        (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
            = ∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * ((w t) / T * (∑ I ∈ A, chi I t.1)) := by
              simp [mul_comm, mul_left_comm]
              apply Finset.sum_congr rfl
              intro x hx
              have :w x * 2⁻¹ / T =  w x / T * 2⁻¹ := by
                simp [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
              rw [this]
              simp_all only [Prod.forall, one_div]
              simp only [mul_assoc]
        _ = (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1)) := by
              -- 左からの定数倍を外へ
              -- a * ∑ = ∑ a * …
              simp [Finset.mul_sum]
    /-have :(1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1))
       = ∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * ((w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
        exact
          Finset.mul_sum (InStar (R.erase t0) t0.2.2) (fun i => w i / T * ∑ I ∈ A, chi I i.2.1)
            (1 / 2)
    -/
    have rightside:∀ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1) = (1/2 : ℚ) * ((w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
      intro t ht
      simp [mul_comm, mul_left_comm]
      have :w t * 2⁻¹ / T =  w t / T * 2⁻¹ := by
        simp [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      rw [this]
      simp_all only [Prod.forall, one_div]
      simp only [mul_assoc]

    have hfactor' :
      (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1))
        = (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
      calc
        (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1))
            = ∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * ((w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
              exact Finset.sum_congr rfl rightside
        _ = (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
              simp [Finset.mul_sum]
    -- これで形が揃ったので結論
    -- left ≤ (∑ g) = … = 右辺
    exact
      (le_trans this
        (by
          -- 右辺を等式で二段階に並べ替え
          have := hsum_add
          -- hsum_add の両項に hfactor, hfactor' を代入
          -- 置換してから rfl
          -- 実装：書き換えで十分
          -- 1つ目の項を hfactor で置換
          -- 2つ目の項を hfactor' で置換
          -- 最後に `rfl`
          -- （書き換えは `rw` でも可）
          -- ここでは calc で明示します
          calc
            (∑ t ∈ (InStar (R.erase t0) t0.2.2),
                ((1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1) + (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)))
              = (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.1))
                  + (∑ t ∈ (InStar (R.erase t0) t0.2.2), (1/2 : ℚ) * (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
                  exact hsum_add
            _ = (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1))
                + (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1)) := by
                  -- それぞれ hfactor, hfactor' に置換
                  exact by
                    -- `simp` で一気に
                    simp_all only [Prod.forall, one_div]
          simp_all only [Prod.forall, one_div, Prod.mk.eta, le_refl]
        ))

  -- Step 3: 片親を x 側へ持ち上げて代入
  have hwT_nonneg_of (t : Rule α) (ht : t ∈ (InStar (R.erase t0) t0.2.2)) : 0 ≤ (w t)/T := by
    have hw_nonneg : 0 ≤ w t := (hLP.1) t ht
    have : 0 ≤ (1/T) := by
      have hpos : 0 < (1/T) := by exact div_pos (by exact rfl) hTpos
      exact le_of_lt hpos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg this hw_nonneg

  have hStep3 :
    ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, indParents t I)
      ≤ (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t))
        + (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t)):= by
    -- hStep2 の RHS の内側和を parentLift_* で上に抑える
    refine le_trans hStep2 ?_
    -- 各項で置換（単調性 × (w t)/T ≥ 0）
    have hwT_nonneg_of (t : Rule α) (ht : t ∈ (InStar (R.erase t0) t0.2.2)) : 0 ≤ (w t)/T := by
      have hw_nonneg : 0 ≤ w t := (hLP.1) t ht
      have : 0 ≤ (1/T) := by
        have hpos : 0 < (1/T) := by exact div_pos (by exact rfl) hTpos
        exact le_of_lt hpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg this hw_nonneg
    -- 左親分
    have hL :
      ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1)
        ≤ ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      have hlift := parentLift_left (V:=V) (R:=R) (t0:=t0) (A:=A) hSuppL t ht
      apply mul_le_mul_of_nonneg_left hlift
      (expose_names; exact hwT_nonneg_of_1 t ht)

    -- 右親分
    have hR :
      ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1)
        ≤ ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      have hlift := parentLift_right (V:=V) (R:=R) (t0:=t0) (A:=A) hSuppR t ht
      exact mul_le_mul_of_nonneg_left hlift (hwT_nonneg_of t ht)
    -- 1/2 を掛けた両辺を足す
    have : (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.1))
           + (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, chi I t.2.1))
           ≤
           (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t))
           + (1/2 : ℚ) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hL (by
        simp_all only [Prod.forall, one_div, inv_nonneg]
        rfl
      )) (mul_le_mul_of_nonneg_left hR (by exact one_div_nonneg.mpr rfl))
    exact this

  -- Step 4: (1/2)X + (1/2)X = X
  have hStep4 :
    ∀ X : ℚ, (1/2 : ℚ) * X + (1/2 : ℚ) * X = X := by
    intro X;
    simp_all only [Prod.forall, one_div]
    rw [← two_mul]
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀]

  -- Step 5: 和の入れ替えと容量
  have hSwap :
    ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t)
      = ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * isParentOf x t) := by
    classical
    -- (w t)/T を内側 sum に配って順序交換
    -- 左辺 = ∑t ∑I ( (w t)/T * ∑x ... ) = ∑I ∑x ( ∑t ( (w t)/T * ... ) ) にする
    calc
      _ = ∑ t ∈ (InStar (R.erase t0) t0.2.2), ∑ I ∈ A, (w t)/T * (∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t) := by
            simp [Finset.mul_sum]
      _ = ∑ t ∈ (InStar (R.erase t0) t0.2.2), ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, (w t)/T * (chi I x * isParentOf x t) := by
            simp [Finset.mul_sum]
      _ = ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t)/T * (chi I x * isParentOf x t) := by
            -- sum_comm を二度適用
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            exact fun x a => Eq.symm Finset.sum_comm
      _ = ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, ∑ t ∈ (InStar (R.erase t0) t0.2.2), chi I x * ((w t)/T * isParentOf x t) := by
            simp [mul_left_comm]
      _ = ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t)/T * isParentOf x t) := by
            apply Finset.sum_congr rfl
            intro h hx
            simp [Finset.mul_sum]

  have hCap :
    ∀ x ∈ ParentSet V (R.erase t0) t0.2.2, (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * isParentOf x t) ≤ (1 : ℚ) / T := by
    intro x hx
    -- (w t)/T * 1_{x親} = (1/T) * (if then w t else 0)
    have hcap := capacity_at_parent (V:=V) (R:=R.erase t0) (r:=t0.2.2) (w:=w) hLP hx
    have hscale_nonneg : 0 ≤ (1 : ℚ) / T := by
      have : 0 < (1 : ℚ) / T := by exact div_pos (by simp_all only [Prod.forall, one_div, zero_lt_one]) hTpos
      exact le_of_lt this
    -- 左辺を (1/T) * ∑ if … then w t else 0 と一致させる
    have hEq :
      (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t)/T * isParentOf x t)
        = (1 / T) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
      classical
      -- 展開して各項で一致
      calc
        (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t)/T * isParentOf x t)
            = (1/T) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) * isParentOf x t) := by
                simp [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
        _ = (1/T) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
                refine congrArg (fun z => (1/T) * z) ?_
                refine Finset.sum_congr rfl ?_
                intro t ht
                unfold isParentOf
                by_cases h : (t.1 = x ∨ t.2.1 = x) <;> simp [h]
      -- これで容量 ≤ 1 をスケール
    calc
      (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * isParentOf x t)
          = (1 / T) * (∑ t ∈ (InStar (R.erase t0) t0.2.2), if (t.1 = x ∨ t.2.1 = x) then w t else 0) := hEq
      _ ≤ (1 / T) * (1 : ℚ) := by
            exact mul_le_mul_of_nonneg_left hcap hscale_nonneg
      _ = (1 : ℚ) / T := by ring_nf

  -- まとめ：hSwap → (I,x) ごとに hCap を適用し、χ_I(x) ≥ 0 で係数付き総和の単調性
  have hDone :
    ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t)
      ≤ (1 / T) * ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x := by
    classical
    -- hSwap で順序交換
    have := congrArg id hSwap
    -- 右辺の形で評価
    -- ∑_{I,x} χ_I(x) * (∑_t …) ≤ ∑_{I,x} χ_I(x) * (1/T)
    have hBound :
      ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * (∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * isParentOf x t)
        ≤ ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * ((1 : ℚ)/T) := by
      refine Finset.sum_le_sum ?_
      intro I hI
      refine Finset.sum_le_sum ?_
      intro x hx
      have hcap := hCap x hx
      -- 係数非負
      have hcoef : 0 ≤ chi I x := chi_nonneg I x
      exact mul_le_mul_of_nonneg_left hcap hcoef
    -- 係数一定 (1/T) を前へ
    have hFactor :
      ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * ((1 : ℚ)/T)
        = (1/T) * ∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x := by
      simp [Finset.mul_sum, mul_comm]
      apply Finset.sum_congr rfl
      exact fun x a => Eq.symm (Finset.sum_mul (ParentSet V (R.erase t0) t0.2.2) (chi x) T⁻¹)

    -- hSwap を用いて左辺を書き替えた上で hBound, hFactor を適用
    simp_all only [Prod.forall, one_div, id_eq, ge_iff_le]

  -- 仕上げ： (1/2)X+(1/2)X = X を hStep3 に適用してから hDone
  have : ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, indParents t I)
        ≤ ∑ t ∈ (InStar (R.erase t0) t0.2.2), (w t) / T * (∑ I ∈ A, ∑ x ∈ ParentSet V (R.erase t0) t0.2.2, chi I x * isParentOf x t) := by
    -- hStep3 と hStep4
    have hx := hStep4
    -- hStep3 の右辺を (1/2)X+(1/2)X に見立てて等式差し替え
    exact
      le_trans hStep3
        (by
          simp_all only [Prod.forall, one_div, implies_true, le_refl]
        )
  exact
    le_trans this hDone
end ThreadDD
