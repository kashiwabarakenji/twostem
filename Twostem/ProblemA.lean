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

--引用なし
/-- Nat→Int の乗法キャスト。 -/
private lemma int_cast_mul (m n : ℕ) :
  ((m * n : ℕ) : ℤ) = (m : ℤ) * (n : ℤ) := by
  -- `Nat.cast_mul` を Int に特化して単純化
  simp [Nat.cast_mul]

--引用なし
/-- （任意）ViolSet メンバの展開。 -/
private lemma mem_ViolSet_iff
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
--メインから呼ばれる予定
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

/- 小技（Int 版の線形化）：∑(2|I|−|V|) = 2∑|I| − |V|·|A| -/
lemma nsmul_int_eq_mul (n : ℕ) (z : Int) : n • z = (n : Int) * z := by
  induction' n with n ih
  · simp
  · have : (Nat.succ n : Int) = (n : Int) + 1 := by
      norm_cast

    simp [this, add_mul]

omit [DecidableEq α] in
lemma sum_const_int_mul_card (S : Finset (Finset α)) (c : Int) :
  (∑ _hUnion ∈ S, c) = (S.card : Int) * c := by
  classical
  simp_all only [Finset.sum_const, Int.nsmul_eq_mul]

omit [DecidableEq α] in
lemma sum_linearize_card (V : Finset α) (A : Finset (Finset α)) :
  (∑ I ∈ A, ((2 : Int) * (I.card : Int) - (V.card : Int)))
  =
  (2 : Int) * (∑ I ∈ A, (I.card : Int))
  - (V.card : Int) * A.card := by
  classical
  have h1 :
    (∑ I ∈ A, ((2 : Int) * (I.card : Int) - (V.card : Int)))
    =
    (∑ I ∈ A, ((2 : Int) * (I.card : Int)))
    - (∑ I ∈ A, (V.card : Int)) := by
    change
      (∑ I ∈ A, ((2 : Int) * (I.card : Int) - (V.card : Int)))
      =
      (∑ I ∈ A, ((2 : Int) * (I.card : Int)))
      - (∑ I ∈ A, (V.card : Int))
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul]

  have h2 :
    (∑ I ∈ A, ((2 : Int) * (I.card : Int)))
    = (2 : Int) * (∑ I ∈ A, (I.card : Int)) := by
    change
      (∑ I ∈ A, ((2 : Int) * (I.card : Int)))
      = (2 : Int) * (∑ I ∈ A, (I.card : Int))
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul]
    simp [Finset.mul_sum]

  have h3 :
    (∑ I ∈ A, (V.card : Int)) = (V.card : Int) * A.card := by
    simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul]
    rw [mul_comm]
  calc
    (∑ I ∈ A, ((2 : Int) * (I.card : Int) - (V.card : Int)))
        = (∑ I ∈ A, ((2 : Int) * (I.card : Int)))
          - (∑ I ∈ A, (V.card : Int)) := h1
    _ = (2 : Int) * (∑ I ∈ A, (I.card : Int))
          - (∑ I ∈ A, (V.card : Int)) := by
            exact congrArg (fun z => z - (∑ I ∈ A, (V.card : Int))) h2
    _ = (2 : Int) * (∑ I ∈ A, (I.card : Int))
          - (V.card : Int) * A.card := by
            exact congrArg (fun z => (2 : Int) * (∑ I ∈ A, (I.card : Int)) - z) h3

/-- **peel 1歩は NDS 非減**（和の分割＋線形化）。
    ここでは「平均 ≥ |V|/2」を `avgHalf_added` という**定義依存の補題**に委ねる。 -/
theorem PeelStep_nondecrease_core
    (V : Finset α) (R : Finset (α × α × α)) (t0 : α × α × α)
    (avgHalf_added :
      (2 : Int) * (∑ I ∈ addedFamily V R t0, (I.card : Int))
      ≥ (V.card : Int) * (addedFamily V R t0).card) :
  NDS2 V (family V R) ≤ NDS2 V (family V (R.erase t0)) := by
  classical
  rcases family_drop_partition (V := V) (R := R) (t0 := t0) with ⟨hU, hDisj⟩
  have hDrop :
      NDS2 V (family V (R.erase t0))
      = ∑ I ∈ family V (R.erase t0),
          ((2 : Int) * (I.card : Int) - (V.card : Int)) :=
    NDS2_sum_formula (V := V) (F := family V (R.erase t0))
  have hOrig :
      NDS2 V (family V R)
      = ∑ I ∈ family V R,
          ((2 : Int) * (I.card : Int) - (V.card : Int)) :=
    NDS2_sum_formula (V := V) (F := family V R)
  have hSplit :
      (∑ I ∈ family V (R.erase t0),
          ((2 : Int) * (I.card : Int) - (V.card : Int)))
      =
      (∑ I ∈ family V R,
          ((2 : Int) * (I.card : Int) - (V.card : Int)))
      +
      (∑ I ∈ addedFamily V R t0,
          ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
    change
      (∑ I ∈ family V (R.erase t0),
          ((2 : Int) * (I.card : Int) - (V.card : Int)))
      =
      (∑ I ∈ family V R,
          ((2 : Int) * (I.card : Int) - (V.card : Int)))
      +
      (∑ I ∈ addedFamily V R t0,
          ((2 : Int) * (I.card : Int) - (V.card : Int)))

    rw [hU]; exact Finset.sum_union hDisj
  have hLin :
      (∑ I ∈ addedFamily V R t0,
          ((2 : Int) * (I.card : Int) - (V.card : Int)))
      =
      (2 : Int) * (∑ I ∈ addedFamily V R t0, (I.card : Int))
      - (V.card : Int) * (addedFamily V R t0).card :=
    sum_linearize_card (V := V) (A := addedFamily V R t0)
  have hAdd_nonneg :
      0 ≤ (∑ I ∈ addedFamily V R t0,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
    have h0 :
      0 ≤
        ((2 : Int) * (∑ I ∈ addedFamily V R t0, (I.card : Int))
         - (V.card : Int) * (addedFamily V R t0).card) :=
      sub_nonneg.mpr avgHalf_added
    -- 0 ≤ a − b かつ RHS = a − b
    exact le_of_le_of_eq h0 (id (Eq.symm hLin))
  have hAdd :
      NDS2 V (family V (R.erase t0))
      = NDS2 V (family V R)
        +
        (∑ I ∈ addedFamily V R t0,
          ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
    calc
      NDS2 V (family V (R.erase t0))
          = ∑ I ∈ family V (R.erase t0),
              ((2 : Int) * (I.card : Int) - (V.card : Int)) := hDrop
      _ = (∑ I ∈ family V R,
              ((2 : Int) * (I.card : Int) - (V.card : Int)))
          +
          (∑ I ∈ addedFamily V R t0,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) := hSplit
      _ = NDS2 V (family V R)
          +
          (∑ I ∈ addedFamily V R t0,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
            have horig' :
              (∑ I ∈ family V R,
                ((2 : Int) * (I.card : Int) - (V.card : Int)))
                = NDS2 V (family V R) := by
              exact Eq.symm hOrig
            rw [horig']
  have hbase :
      NDS2 V (family V R)
        ≤ NDS2 V (family V R)
          +
          (∑ I ∈ addedFamily V R t0,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) :=
    le_add_of_nonneg_right hAdd_nonneg
  have hgoal := hbase
  simp_all only [ge_iff_le, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_union_of_disjoint, Int.nsmul_eq_mul,
    Nat.cast_add, Int.sub_nonneg, le_add_iff_nonneg_right]

lemma addedFamily_char_left
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) :
  ∀ {I}, I ∈ addedFamily V R t0 →
    I ∈ family V (R.erase t0) ∧ Violates t0 I := by
  classical
  intro I hI
  -- 差集合の会員条件
  rcases Finset.mem_sdiff.mp hI with ⟨hInErase, hNotInR⟩
  -- `I ⊆ V` と `isClosed (R.erase t0) I`
  have hInErase' : I ⊆ V ∧ isClosed (R.erase t0) I := by
    exact (mem_family_iff V (R.erase t0)).mp hInErase

  have hSubV : I ⊆ V := hInErase'.1
  have hClosedErase : isClosed (R.erase t0) I := hInErase'.2
  -- `I ∉ family V R` から `¬ isClosed R I` を引き出す（`I ⊆ V` は既にある）
  have hNotClosedR : ¬ isClosed R I := by
    intro hClosedR
    have hInR : I ∈ family V R := by
      exact((mem_family_iff V R).mpr ⟨hSubV, hClosedR⟩)
    exact hNotInR hInR
  -- `¬ isClosed R I` から「ある t∈R が I を破る」ことを取り出す
  -- isClosed R I = ∀ t∈R, (parents→child)
  have hnc :
      ¬ ∀ t, t ∈ R → ((t.1 ∈ I ∧ t.2.1 ∈ I) → t.2.2 ∈ I) := by
    -- λ展開で `isClosed` へ戻す（`simpa using` は使わない）
    exact
      (fun h => hNotClosedR (by
        intro t ht hpar
        exact h t ht hpar))
  rcases not_forall.mp hnc with ⟨t, ht⟩
  rcases Classical.not_imp.mp ht with ⟨htR, hnot⟩
  rcases Classical.not_imp.mp hnot with ⟨hparents, hchildOut⟩
  -- `t ≠ t0` なら `t ∈ R.erase t0` なので閉性に矛盾。よって `t = t0`。
  by_cases hEq : t = t0
  · -- ちょうど `t0` が I を破る
    subst hEq
    exact ⟨hInErase, And.intro hparents.1 (And.intro hparents.2 hchildOut)⟩
  · -- `t ≠ t0` ⇒ `t ∈ R.erase t0`
    have htInErase : t ∈ R.erase t0 := by
      -- `mem_erase`: x ∈ s.erase a ↔ x ≠ a ∧ x ∈ s
      exact Finset.mem_erase.mpr ⟨hEq, htR⟩
    -- 閉性で `t.2.2 ∈ I`、矛盾
    have : t.2.2 ∈ I := hClosedErase t htInErase hparents
    exact (hchildOut this).elim

/-- 本命：`t0 ∈ R` の仮定の下での同値。 -/
lemma addedFamily_char
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) (hR : t0 ∈ R) :
  ∀ I, I ∈ addedFamily V R t0
      ↔ I ∈ family V (R.erase t0) ∧ Violates t0 I := by
  classical
  intro I
  constructor
  · -- (→) は仮定なし版でOK
    intro h
    exact addedFamily_char_left V R t0 h
  · -- (←) `t0 ∈ R` を使って `I ∉ family V R` を示す
    intro h
    rcases h with ⟨hInErase, hViol⟩
    -- まず差集合の左側
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · exact hInErase
    · -- 右側は「家族に属さない」を示す：`isClosed R I` と矛盾を作る
      intro hInR
      -- `I ⊆ V ∧ isClosed R I`
      rcases (mem_family_iff V R).mp hInR with ⟨_, hClosedR⟩
      -- `t0 ∈ R` と `Violates t0 I` から、`isClosed R I` に矛盾
      have : t0.2.2 ∈ I := hClosedR t0 hR ⟨hViol.1, hViol.2.1⟩
      exact hViol.2.2 this

-- Chatにもコードにもない。次の補題で使う。
theorem avgHalf_via_Barrier
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hB : BarrierHyp V R t0) :
  (2 : Int) * (∑ I ∈ addedFamily V R t0, (I.card : Int))
    ≥ (V.card : Int) * (addedFamily V R t0).card := by
  classical
  -- 記法を軽く
  let A := addedFamily V R t0
  -- 各 I∈A についての点wise不等式：LargeWhenParents を適用
  have hLW : LargeWhenParents V R t0 :=
    LargeWhenParents_of_CoreBarrier V R t0 hB
  have hpt :
      ∀ {I}, I ∈ A → (2 : Int) * (I.card : Int) ≥ (V.card : Int) := by
    intro I hI
    -- 追加族の特徴付け（片向き）：family (R.erase t0) かつ Violates
    have hmem : I ∈ family V (R.erase t0) ∧ Violates t0 I :=
      addedFamily_char_left V R t0 hI
    have hIcl : I ∈ family V (R.erase t0) := hmem.1
    have ha  : t0.1 ∈ I := hmem.2.1
    have hb  : t0.2.1 ∈ I := hmem.2.2.1
    have hr  : t0.2.2 ∉ I := hmem.2.2.2
    exact hLW I hIcl ha hb hr
  -- 両辺を和で足し上げる
  have hsum :
      ∑ I ∈ A, (V.card : Int) ≤ ∑ I ∈ A, (2 : Int) * (I.card : Int) := by
    refine Finset.sum_le_sum ?ineq
    intro I hI
    exact hpt hI
  -- 左辺：定数和 = |A| * |V|
  have hleft :
      ∑ I ∈ A, (V.card : Int) = (A.card : Int) * (V.card : Int) := by
    -- sum_const → nsmul → 乗法
    exact sum_const_int_mul_card A ↑V.card

  -- 右辺：定数 2 を外へ
  have hright :
      ∑ I ∈ A, (2 : Int) * (I.card : Int)
        = (2 : Int) * ∑ I ∈ A, (I.card : Int) := by
    -- いったん各項を右掛けにして sum_mul を使い、最後に順序を戻す
    have hsm :
        (∑ I ∈ A, (I.card : Int)) * (2 : Int)
          = ∑ I ∈ A, (I.card : Int) * (2 : Int) :=
      Finset.sum_mul (s := A) (f := fun I => (I.card : Int)) (a := (2 : Int))
    calc
      ∑ I ∈ A, (2 : Int) * (I.card : Int)
          = ∑ I ∈ A, (I.card : Int) * (2 : Int) := by
              refine Finset.sum_congr rfl ?_
              intro I hI; exact mul_comm _ _
      _ = (∑ I ∈ A, (I.card : Int)) * (2 : Int) := hsm.symm
      _ = (2 : Int) * ∑ I ∈ A, (I.card : Int) := by
              exact mul_comm _ _
  -- まとめ：|V|*|A| ≤ 2 * Σ|I|
  have hfin :
      (V.card : Int) * (A.card : Int)
        ≤ (2 : Int) * ∑ I ∈ A, (I.card : Int) := by
    calc
      (V.card : Int) * (A.card : Int)
          = ∑ I ∈ A, (V.card : Int) := by
              simp_all only [ge_iff_le, Finset.sum_const, Int.nsmul_eq_mul, A]
              rw [mul_comm]
      _ ≤ ∑ I ∈ A, (2 : Int) * (I.card : Int) := hsum
      _ = (2 : Int) * ∑ I ∈ A, (I.card : Int) := hright
  -- A = addedFamily … を戻して終了（`≥` は定義上 `≤` の反転）
  have hA : A = addedFamily V R t0 := rfl
  -- 目標は `2 * Σ ≥ |V| * |A|`（= `|V|*|A| ≤ 2 * Σ`）
  -- 左辺の因子順だけ揃える
  have hfinal :
      (V.card : Int) * (addedFamily V R t0).card
        ≤ (2 : Int) * ∑ I ∈ addedFamily V R t0, (I.card : Int) := by
    -- hfin を A = addedFamily に書き換える
    -- （`rw` で十分。`simpa using` は使いません。）
    -- まず両辺の A を置換
    -- 左（A.card）と右（∑ over A）を同時に置換
    -- （`rw` は複数箇所に作用します）
    rw [hA] at hfin
    -- さらに左辺の掛ける順序を合わせる（可換性）
    -- 現在 hfin は `(V.card:ℤ) * (addedFamily…).card ≤ 2 * Σ` の形
    exact hfin
  -- `≥` 形式で返す
  exact hfinal

-- コードにもないが、以下で完成？
theorem PeelWitness_from_Barrier
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hmem : t0 ∈ R) (hB : BarrierHyp V R t0) :
  PeelWitness V R t0 := by
  classical
  have avg := avgHalf_via_Barrier (V := V) (R := R) (t0 := t0) hB
  exact ⟨hmem, PeelStep_nondecrease_core (V := V) (R := R) (t0 := t0) avg⟩



end ThreadA
