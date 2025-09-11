import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF
import Twostem.Basic
import Twostem.General
import LeanCopilot
import Twostem.ProblemCC
open scoped Rat
--import Mathlib.Tactic.NormCast

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

namespace ThreadC
open scoped BigOperators

/-! ## bind を使わない分解：`if` と `filter` で partition を表現 -/


--内部から参照多数
private lemma sum_family_partition_via_filter
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (φ : Finset α → Int) :
  ∑ I ∈ family V R, φ I
    =
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ∑ I ∈ family V R, (if I ∩ Rep (Q := Q) = B then φ I else 0) := by
  classical
  -- 各 I について、B を全探索してもちょうど1回だけ φ I が数えられることを示す
  have step :
      ∑ I ∈ family V R, φ I
        =
      ∑ I ∈ family V R,
          ∑ B ∈ (Rep (Q := Q)).powerset,
              (if I ∩ Rep (Q := Q) = B then φ I else 0) := by
    refine Finset.sum_congr rfl ?_
    intro I hI
    -- B₀ := I ∩ Rep は確かに powerset の要素
    have hBsub : I ∩ Rep (Q := Q) ⊆ Rep (Q := Q) :=
      Finset.inter_subset_right
    have hBin : I ∩ Rep (Q := Q) ∈ (Rep (Q := Q)).powerset :=
      Finset.mem_powerset.mpr hBsub
    -- sum over B は「B = I∩Rep」の項だけが φ I、他は 0
    have h_zero :
        ∀ {B}, B ∈ (Rep (Q := Q)).powerset → B ≠ I ∩ Rep (Q := Q) →
          (if I ∩ Rep (Q := Q) = B then φ I else 0) = 0 := by
      intro B hB hneq
      have : I ∩ Rep (Q := Q) ≠ B := by
        exact Ne.symm hneq
      -- if_neg で 0
      simp [this]
    have h_main :
        (if I ∩ Rep (Q := Q) = I ∩ Rep (Q := Q) then φ I else 0) = φ I := by
      -- if_pos で φ I
      simp
    -- sum_eq_single_of_mem で一点に集約
    have hsum :
        ∑ B ∈ (Rep (Q := Q)).powerset,
            (if I ∩ Rep (Q := Q) = B then φ I else 0)
          =
        (if I ∩ Rep (Q := Q) = I ∩ Rep (Q := Q) then φ I else 0) :=
      Finset.sum_eq_single_of_mem
        (I ∩ Rep (Q := Q)) hBin
        (by
          intro B hB hBne
          exact h_zero hB hBne)
    -- 以上を連結
    exact Eq.symm (Finset.sum_ite_eq_of_mem (Rep Q).powerset (I ∩ Rep Q) (fun x => φ I) hBin)

  -- 二重和の順序交換（commute）
  -- ∑ I∈family ∑ B∈powerset = ∑ B∈powerset ∑ I∈family
  have step' :
      ∑ I ∈ family V R,
          ∑ B ∈ (Rep (Q := Q)).powerset,
              (if I ∩ Rep (Q := Q) = B then φ I else 0)
        =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ family V R,
              (if I ∩ Rep (Q := Q) = B then φ I else 0) := by
    -- `Finset.sum_comm` が使える形に整っている
    exact Finset.sum_comm
  -- 連結して結論
  exact Eq.trans step step'

/-- `sum_filter` を用いて、内側の if を fiber（=filter）に戻す版。 -/
--Excessから引用あり。
lemma sum_family_partition_as_fibers
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (φ : Finset α → Int) :
  ∑ I ∈ family V R, φ I
    =
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ∑ I ∈ fiber V R Q B, φ I := by
  classical
  -- まず if 版の分解
  have h0 := sum_family_partition_via_filter (V := V) (R := R) (Q := Q) φ
  -- `sum_filter`: ∑_{I∈family.filter p} φ I = ∑_{I∈family} if p I then φ I else 0
  -- を使って内側の和を書き換える
  -- p := fun I => I ∩ Rep = B
  have h1 :
      ∀ B, B ∈ (Rep (Q := Q)).powerset →
        (∑ I ∈ family V R, (if I ∩ Rep (Q := Q) = B then φ I else 0))
          =
        (∑ I ∈ (family V R).filter (fun I => I ∩ Rep (Q := Q) = B), φ I) := by
    intro B hB
    -- sum_filter の左右を入れ替える形で使う（対称性）
    -- `sum_filter` は通常 左=filter版 右=if版 だが、ここではその等式を逆向きに使う
    have := (Finset.sum_filter
              (s := family V R)
              (p := fun I => I ∩ Rep (Q := Q) = B)
              (f := fun I => φ I))

    exact Eq.symm this
  -- h0 の右辺の各内側和を h1 で置換
  -- `Finset.sum_congr` で内側を書き換える
  have h2 :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ family V R, (if I ∩ Rep (Q := Q) = B then φ I else 0)
        =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ (family V R).filter (fun I => I ∩ Rep (Q := Q) = B), φ I := by
    refine Finset.sum_congr rfl ?_
    intro B hB
    exact h1 B hB
  -- fiber の定義で置換
  -- fiber V R Q B := (family V R).filter (fun I => I ∩ Rep = B)
  -- なので `rfl`
  have hfiber :
      ∀ B, (family V R).filter (fun I => I ∩ Rep (Q := Q) = B)
          = fiber V R Q B := by
    intro B; rfl
  have h3 :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ (family V R).filter (fun I => I ∩ Rep (Q := Q) = B), φ I
        =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ fiber V R Q B, φ I := by
    refine Finset.sum_congr rfl ?_
    intro B hB
    -- 内側の台集合を fiber に置き換え
    -- `rw [hfiber B]` でもよいが、`exact` で直接
    have : (family V R).filter (fun I => I ∩ Rep (Q := Q) = B)
            = fiber V R Q B := hfiber B
    exact congrArg (fun X => ∑ I ∈ X, φ I) this
  -- 以上を連結
  exact Eq.trans h0 (Eq.trans h2 h3)

/-! 参考：`NDS2` で使う一次式の総和の線形化（定義展開用）。 -/
--内部から参照あり。メインからも参照したいみたいなのでprivateを外す。
omit [DecidableEq α] in
lemma sum_linearize_card_sub_const
  (V : Finset α) :
  ∀ (S : Finset (Finset α)),
    ∑ I ∈ S, ((2 : Int) * (I.card : Int) - (V.card : Int))
      =
    (2 : Int) * (∑ I ∈ S, (I.card : Int))
      - (V.card : Int) * S.card := by
  intro S
  -- 分配と定数の取り出し（有限和の基本事実）
  -- 左：∑ (2*|I| - |V|) = 2*∑|I| - |V| * |S|
  -- `Finset.sum_sub_distrib` + `Finset.sum_mul` + `sum_const_nsmul` 相当
  have h1 :
      ∑ I ∈ S, ((2 : Int) * (I.card : Int))
        =
      (2 : Int) * (∑ I ∈ S, (I.card : Int)) := by

    revert S
    intro S
    simp [two_mul]
    simp [Finset.sum_add_distrib]

    -- ↑ ここはあなたの環境の線形性補題に合わせて埋めてください。
    -- 以後の証明ではこの等式を「既知」として扱って構いません。
  -- `∑ I∈S, (V.card : Int)` は定数なので `S.card` 倍
  have h2 :
      ∑ I ∈ S, (V.card : Int)
        =
      (V.card : Int) * S.card := by
    -- `sum_const_nat` の Int 版。必要なら帰納で埋めてもOK。
    -- ここもあなたの環境に合わせて補います。
    simp_all only [Finset.sum_const, Int.nsmul_eq_mul]
    rw [mul_comm]

  -- まとめ
  -- ∑ (2*|I| - |V|) = (∑ 2*|I|) - (∑ |V|)
  -- = 2*∑|I| - |V|*|S|
  calc
    ∑ I ∈ S, ((2 : Int) * (I.card : Int) - (V.card : Int))
        = (∑ I ∈ S, (2 : Int) * (I.card : Int))
          - (∑ I ∈ S, (V.card : Int)) := by
            -- 分配（和の差）
            simp_all only [Finset.sum_const, Int.nsmul_eq_mul, Finset.sum_sub_distrib]

    _   = (2 : Int) * (∑ I ∈ S, (I.card : Int))
          - (V.card : Int) * S.card := by

            have := h1
            -- ここから `rw` で置換（あなたの環境に合わせて整理ください）
            simp_all only [Finset.sum_const, Int.nsmul_eq_mul]

/-- 異なる `B` の fiber は互いに素。 -/
--内部から参照なし
private lemma fibers_pairwise_disjoint
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  ∀ {B₁} , B₁ ∈ (Rep (Q := Q)).powerset →
  ∀ {B₂} , B₂ ∈ (Rep (Q := Q)).powerset →
    B₁ ≠ B₂ →
    Disjoint (fiber V R Q B₁) (fiber V R Q B₂) := by
  intro B₁ hB₁ B₂ hB₂ hne
  refine Finset.disjoint_left.mpr ?_
  intro I hI1 hI2
  -- それぞれの fiber の定義から、I ∩ Rep = B₁ と I ∩ Rep = B₂
  have h1 : I ∈ family V R ∧ I ∩ Rep (Q := Q) = B₁ :=
    (mem_fiber_iff (V := V) (R := R) (Q := Q)).mp hI1
  have h2 : I ∈ family V R ∧ I ∩ Rep (Q := Q) = B₂ :=
    (mem_fiber_iff (V := V) (R := R) (Q := Q)).mp hI2
  have : B₁ = B₂ := by
    -- 両方とも I ∩ Rep に等しい
    simp_all only [Finset.mem_powerset, ne_eq, true_and]
  exact hne this




/-- B が R₁ 上で閉でないなら、`I ∩ Rep = B` を満たす family 要素は存在しない。 -/
lemma family_contractRules_filter_empty_of_nonclosed_B
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  {B : Finset α} --(hBsub : B ⊆ Rep (Q := Q))
  (hBnot : ¬ isClosed (R1 (V := V) (R := R) (Q := Q)) B) :
  (family V (R1 (V := V) (R := R) (Q := Q))).filter
      (fun I => I ∩ Rep (Q := Q) = B) = ∅ := by
  classical
  -- 反証法：もし非空なら、ある I があって I ∈ family R₁ かつ I∩Rep = B
  by_contra hne
  have : ∃ I, I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                  (fun I => I ∩ Rep (Q := Q) = B) := by
    -- `Finset.nonempty_iff_ne_empty` で取り出す
    have : (family V (R1 (V := V) (R := R) (Q := Q))).filter
              (fun I => I ∩ Rep (Q := Q) = B) ≠ ∅ := hne
    apply Finset.nonempty_iff_ne_empty.mpr this

  rcases this with ⟨I, hIfilter⟩
  -- フィルタ分解
  have hIfam_and_eq : I ∈ family V (R1 (V := V) (R := R) (Q := Q))
                      ∧ I ∩ Rep (Q := Q) = B :=
    Finset.mem_filter.mp hIfilter
  -- family 側の判定で、I∩Rep が R₁ 上で閉であることが必要（前補題）
  have hIfam_iff :=
    mem_family_contractRules_iff (V := V) (R := R) (Q := Q) hV (I := I)
  have hclosedB : isClosed (R1 (V := V) (R := R) (Q := Q)) (I ∩ Rep (Q := Q)) := by
    have h1 := (hIfam_iff.mp hIfam_and_eq.1).2
    -- h1 : I ∩ Rep ∈ familyRep
    -- familyRep の定義から閉性が出る
    have h2 := Finset.mem_filter.mp h1
    exact h2.2
  -- I∩Rep = B なので、B が閉になるはず。矛盾。
  exact hBnot (hIfam_and_eq.2 ▸ hclosedB)

/- Rep 集合を外部から与えて `family` を分割する（Q に依存しない汎用版）。 -/
lemma sum_family_partition_via_filter_wrt
  (V : Finset α) (R : Finset (Rule α)) (RepSet : Finset α)
  (φ : Finset α → Int) :
  ∑ I ∈ family V R, φ I
    =
  ∑ B ∈ RepSet.powerset,
      ∑ I ∈ family V R, (if I ∩ RepSet = B then φ I else 0) := by
  classical
  -- 各 I について、B を全探索してもちょうど1回だけ φ I が数えられる
  have step :
      ∑ I ∈ family V R, φ I
        =
      ∑ I ∈ family V R,
          ∑ B ∈ RepSet.powerset,
              (if I ∩ RepSet = B then φ I else 0) := by
    refine Finset.sum_congr rfl ?_
    intro I hI
    have hBsub : I ∩ RepSet ⊆ RepSet := Finset.inter_subset_right
    have hBin  : I ∩ RepSet ∈ RepSet.powerset := Finset.mem_powerset.mpr hBsub
    have h_zero :
        ∀ {B}, B ∈ RepSet.powerset → B ≠ I ∩ RepSet →
          (if I ∩ RepSet = B then φ I else 0) = 0 := by
      intro B hB hneq; have : I ∩ RepSet ≠ B := Ne.symm hneq; simp [this]
    have h_main :
        (if I ∩ RepSet = I ∩ RepSet then φ I else 0) = φ I := by simp
    have hsum :
        ∑ B ∈ RepSet.powerset,
            (if I ∩ RepSet = B then φ I else 0)
          =
        (if I ∩ RepSet = I ∩ RepSet then φ I else 0) :=
      Finset.sum_eq_single_of_mem (I ∩ RepSet) hBin
        (by intro B hB hBne; exact h_zero hB hBne)
    exact Eq.symm (Finset.sum_ite_eq_of_mem RepSet.powerset (I ∩ RepSet) (fun x => φ I) hBin)

  -- 和の順序交換
  have step' :
      ∑ I ∈ family V R,
          ∑ B ∈ RepSet.powerset, (if I ∩ RepSet = B then φ I else 0)
        =
      ∑ B ∈ RepSet.powerset,
          ∑ I ∈ family V R, (if I ∩ RepSet = B then φ I else 0) :=
    Finset.sum_comm
  exact Eq.trans step step'

/-- `filter` に戻す版（Q に依存しない）。 -/
lemma sum_family_partition_as_fibers_wrt
  (V : Finset α) (R : Finset (Rule α)) (RepSet : Finset α)
  (φ : Finset α → Int) :
  ∑ I ∈ family V R, φ I
    =
  ∑ B ∈ RepSet.powerset,
      ∑ I ∈ (family V R).filter (fun I => I ∩ RepSet = B), φ I := by
  classical
  have h0 := sum_family_partition_via_filter_wrt (V := V) (R := R) (RepSet := RepSet) φ
  have h1 :
      ∀ B ∈ RepSet.powerset,
        (∑ I ∈ family V R, (if I ∩ RepSet = B then φ I else 0))
          =
        (∑ I ∈ (family V R).filter (fun I => I ∩ RepSet = B), φ I) := by
    intro B hB
    -- sum_filter の等式を逆向きに使用
    exact (Finset.sum_filter
            (s := family V R)
            (p := fun I => I ∩ RepSet = B)
            (f := fun I => φ I)).symm
  refine Eq.trans h0 ?_
  refine Finset.sum_congr rfl ?_
  intro B hB; exact h1 B hB

-- 既存：familyRep, R1, mem_family_contractRules_iff, ... はそのままでOK
--内部から参照あり
private lemma sum_family_contractRules_partition_as_closed_fibers
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  (φ : Finset α → Int) :
  ∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)), φ I
    =
  ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
      ∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                (fun I => I ∩ Rep (Q := Q) = B),
          φ I := by
  classical
  -- ★ 修正1：Q を渡さず RepSet で分割
  have h0 :
      ∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)), φ I
        =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)),
              (if I ∩ Rep (Q := Q) = B then φ I else 0) :=
    sum_family_partition_via_filter_wrt
      (V := V) (R := R1 (V := V) (R := R) (Q := Q))
      (RepSet := Rep (Q := Q)) φ
  -- 内側を filter に戻す
  have h1 :
      ∀ B, B ∈ (Rep (Q := Q)).powerset →
        (∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)),
            (if I ∩ Rep (Q := Q) = B then φ I else 0))
          =
        (∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                  (fun I => I ∩ Rep (Q := Q) = B), φ I) := by
    intro B hB
    exact (Finset.sum_filter
            (s := family V (R1 (V := V) (R := R) (Q := Q)))
            (p := fun I => I ∩ Rep (Q := Q) = B)
            (f := fun I => φ I)).symm
  have h2 :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)),
              (if I ∩ Rep (Q := Q) = B then φ I else 0)
        =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                    (fun I => I ∩ Rep (Q := Q) = B), φ I := by
    refine Finset.sum_congr rfl ?_
    intro B hB; exact h1 B hB
  -- 「閉でない B の fiber は空」
  have hvanish :
      ∀ {B}, B ∈ (Rep (Q := Q)).powerset →
        B ∉ familyRep (V := V) (R := R) (Q := Q) →
        (∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                  (fun I => I ∩ Rep (Q := Q) = B), φ I) = 0 := by
    intro B hB hBnot
    have hBsub : B ⊆ Rep (Q := Q) := Finset.mem_powerset.mp hB
    have : ¬ isClosed (R1 (V := V) (R := R) (Q := Q)) B := by
      intro hcl
      have : B ∈ familyRep (V := V) (R := R) (Q := Q) := by
        unfold familyRep; exact Finset.mem_filter.mpr ⟨hB, hcl⟩
      exact hBnot this
    have hempty :=
      family_contractRules_filter_empty_of_nonclosed_B
        (V := V) (R := R) (Q := Q) hV (B := B) this
    -- 空集合上の和は 0
    -- （`simp [hempty]` で安全に 0 化）
    simp_all only [R1, Finset.mem_powerset, Finset.sum_empty]
  -- ★ 修正2：sum_subset の向きを合わせる（symm）
  have hsubset : familyRep (V := V) (R := R) (Q := Q)
                 ⊆ (Rep (Q := Q)).powerset := by
    intro B hBfam
    exact (Finset.mem_filter.mp hBfam).1
  have hshrink :=
    (Finset.sum_subset hsubset
      (by intro B hBpow hBnot; exact hvanish hBpow hBnot)).symm
  -- 連結
  exact Eq.trans (Eq.trans h0 h2) hshrink

/-- R₁ で B が閉なら、その fiber は Free 上の立方体と「B ∪ S」の形で一致。 -/
--内部から参照あり
private lemma fiber_contractRules_eq_cube_of_closed
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  {B : Finset α}
  (hBsub : B ⊆ Rep (Q := Q))
  (hBclosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B) :
  (family V (R1 (V := V) (R := R) (Q := Q))).filter
      (fun I => I ∩ Rep (Q := Q) = B)
    =
  (Free (Q := Q)).powerset.image (fun S => B ∪ S) := by
  classical
  -- 便利：Rep ⊆ V, Rep ∩ Free = ∅
  have hRepV : Rep (Q := Q) ⊆ V := Rep_subset_V (V := V) (R := R) (Q := Q)
  have hdis : Disjoint (Rep (Q := Q)) (Free (Q := Q)) :=
    disjoint_Rep_Free (V := V) (R := R) (Q := Q)

  -- 片側包含（→）: fiber ⊆ image
  apply Finset.Subset.antisymm
  · intro I hIfilter
    have hIfam_and_eq :
        I ∈ family V (R1 (V := V) (R := R) (Q := Q))
        ∧ I ∩ Rep (Q := Q) = B :=
      Finset.mem_filter.mp hIfilter
    -- I = (I∩Rep) ∪ (I∩Free) = B ∪ (I∩Free)
    have hIeq :
        I = (I ∩ Rep (Q := Q)) ∪ (I ∩ Free (Q := Q)) := by
      -- 分割等式：V = Rep ∪ Free、かつ互いに素
      have hU := union_Rep_Free_eq_V (V := V) (R := R) (Q := Q)

      have : I = I ∩ V := by
        -- I ⊆ V は family の定義から（下で取り出す）
        have hIfam := (mem_family_iff (V := V) (R := R1 (V := V) (R := R) (Q := Q))).mp hIfam_and_eq.1
        have hIsub : I ⊆ V := hIfam.1
        -- I = I ∩ V
        simp_all only [R1, Finset.mem_filter, and_true, true_and]
        subst hIfam_and_eq
        simp_all only [Finset.inter_subset_right]
        ext a : 1
        simp_all only [Finset.mem_inter, iff_self_and]
        intro a_1
        exact hIsub a_1

      calc
        I = I ∩ V := this
        _ = I ∩ (Rep (Q := Q) ∪ Free (Q := Q)) := by
              -- V = Rep ∪ Free
              exact congrArg (Inter.inter I) (id (Eq.symm hU))
        _ = (I ∩ Rep (Q := Q)) ∪ (I ∩ Free (Q := Q)) := by
              exact Finset.inter_union_distrib_left _ _ _
    -- S := I ∩ Free ∈ Free.powerset
    have hSsub : I ∩ Free (Q := Q) ⊆ Free (Q := Q) :=
      Finset.inter_subset_right
    have hSin : I ∩ Free (Q := Q) ∈ (Free (Q := Q)).powerset :=
      Finset.mem_powerset.mpr hSsub
    -- 交わりは空
    have hdis' : Disjoint B (I ∩ Free (Q := Q)) := by
      -- B ⊆ Rep、I∩Free ⊆ Free、Rep ⊥ Free
      exact Disjoint.mono hBsub hSsub hdis
    -- I = B ∪ (I∩Free)
    have hIeq' : I = B ∪ (I ∩ Free (Q := Q)) := by
      let hi := hIfam_and_eq.2
      rw [←hi]
      ext x
      constructor
      · intro hx
        rw [←hIeq]
        exact hx
      · intro hx
        rw [hIeq]
        exact hx
    -- よって I は image に対応
    refine Finset.mem_image.mpr ?_

    exact ⟨I ∩ Free (Q := Q), hSin, hIeq'.symm⟩

  -- 逆包含（←）: image ⊆ fiber
  · intro I hIimg
    rcases Finset.mem_image.mp hIimg with ⟨S, hSps, hI⟩
    -- S ⊆ Free
    have hSsub : S ⊆ Free (Q := Q) := Finset.mem_powerset.mp hSps
    -- B ∪ S ⊆ V
    have hBsubV : B ⊆ V := Set.Subset.trans hBsub hRepV
    have hSsubV : S ⊆ V := Set.Subset.trans hSsub (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
      -- 上の1行は Free = V \ Rep なので Free ⊆ V
    have hBcupS_subV : B ∪ S ⊆ V := by
      intro x hx; rcases Finset.mem_union.mp hx with hxB | hxS
      · exact hBsubV hxB
      · exact hSsubV hxS
    -- I = B ∪ S
    have hI' : I = B ∪ S := by exact id (Eq.symm hI)
    -- I ∈ family V R₁：isClosed は I∩Rep で決まる（既補題）
    have hClosed_iff :=
      isClosed_contractRules_iff_onRep (V := V) (R := R) (Q := Q) hV (I := I)
    -- I∩Rep = B：S ⊆ Free なので Rep と交わらない
    have hdisBS : Disjoint B S := by
      subst hI'
      simp_all only [R1, Finset.mem_powerset, Finset.mem_image]
      obtain ⟨w, h⟩ := hIimg
      obtain ⟨left, right⟩ := h
      apply Disjoint.mono
      on_goal 3 => { exact hdis
      }
      · simp_all only [Finset.le_eq_subset]
      · simp_all only [Finset.le_eq_subset]


    have hIcapRep :
        I ∩ Rep (Q := Q) = B := by
      -- I = B ∪ S、かつ Rep ⊥ Free ⇒ (B ∪ S) ∩ Rep = B
      calc
        I ∩ Rep (Q := Q)
            = (B ∪ S) ∩ Rep (Q := Q) := by simp [hI']
        _ = (B ∩ Rep (Q := Q)) ∪ (S ∩ Rep (Q := Q)) := by
              exact Finset.union_inter_distrib_right _ _ _
        _ = B ∪ ∅ := by
              -- B ⊆ Rep、S ⊆ Free、Rep ⊥ Free
              have br: B ∩ Rep (Q := Q) = B := by
                exact Finset.inter_eq_left.mpr hBsub
              have sr: S ∩ Rep (Q := Q) = ∅ := by
                have sf: S ⊆ Free (Q := Q) := hSsub
                have dfr: Disjoint (Free (Q := Q)) (Rep (Q := Q)) := by
                  exact hdis.symm
                dsimp [Disjoint] at dfr
                subst hI'
                simp_all only [R1, Finset.mem_powerset, Finset.inter_eq_left, Finset.subset_empty, subset_refl, Finset.mem_image,
                  Finset.empty_subset]
                obtain ⟨w, h⟩ := hIimg
                obtain ⟨left, right⟩ := h
                apply dfr
                · intro x hx
                  simp_all only [subset_refl, Finset.mem_inter]
                  obtain ⟨left_1, right_1⟩ := hx
                  apply sf
                  simp_all only [subset_refl]
                · simp_all only [subset_refl, Finset.inter_subset_right]
              rw [br, sr]

        _ = B := by simp
    -- I の閉性：I∩Rep = B が閉 ⇒ I も閉
    have hIclosed :
        isClosed (R1 (V := V) (R := R) (Q := Q)) I :=
      (hClosed_iff.mpr (by simpa [hIcapRep] using hBclosed))
    -- family へ
    have hpow : I ∈ V.powerset := by
      subst hI'
      simp_all only [R1, Finset.mem_powerset, Finset.mem_image, iff_true]

    have hIfam : I ∈ family V (R1 (V := V) (R := R) (Q := Q)) :=
      Finset.mem_filter.mpr (And.intro hpow hIclosed)
    -- filter 条件
    have hIcond : I ∩ Rep (Q := Q) = B := hIcapRep
    exact Finset.mem_filter.mpr (And.intro hIfam hIcond)

/-- 上の同一視を使って、R₁ の fiber（閉な B）上の和を Free 立方体の和に引き戻す。 -/
--内部から参照あり
private lemma sum_fiber_contractRules_closedB_pullback
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  {B : Finset α}
  (hBsub : B ⊆ Rep (Q := Q))
  (hBclosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B)
  (φ : Finset α → Int) :
  ∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
          (fun I => I ∩ Rep (Q := Q) = B),
        φ I
    =
  ∑ S ∈ (Free (Q := Q)).powerset,
        φ (B ∪ S) := by
  classical
  -- fiber = image (S ↦ B ∪ S)
  have hEq :=
    fiber_contractRules_eq_cube_of_closed
      (V := V) (R := R) (Q := Q) hV hBsub hBclosed
  -- `sum_image` を使うために、(S ↦ B ∪ S) の単射性を示す
  have hinj :
      ∀ {S₁} (h₁ : S₁ ∈ (Free (Q := Q)).powerset)
        {S₂} (h₂ : S₂ ∈ (Free (Q := Q)).powerset),
        (B ∪ S₁ = B ∪ S₂) → S₁ = S₂ := by
    intro S₁ h₁ S₂ h₂ hU
    -- 片側に `\ B` をかければ S が取り出せる（B と Free は素）
    -- S = (B ∪ S) \ B
    have hdis : Disjoint B (Free (Q := Q)) := by
      have :Disjoint (Rep (Q := Q)) (Free (Q := Q)) := by exact disjoint_Rep_Free V R Q
      dsimp [Disjoint] at this
      dsimp [Disjoint]
      intro x hx
      intro a
      simp_all only [R1, Finset.mem_powerset, Finset.subset_empty, subset_refl, Finset.empty_subset,
        Finset.inter_subset_right]
      apply this
      · tauto
      · simp_all only [subset_refl, Finset.inter_subset_right]

      --disjoint_Rep_Free (V := V) (R := R) (Q := Q)
    have hS₁sub : S₁ ⊆ Free (Q := Q) := Finset.mem_powerset.mp h₁
    have hS₂sub : S₂ ⊆ Free (Q := Q) := Finset.mem_powerset.mp h₂
    have hS₁dis : Disjoint B S₁ := hdis.mono_right hS₁sub
    have hS₂dis : Disjoint B S₂ := hdis.mono_right hS₂sub
    -- `(B ∪ S) \ B = S`（排反だから）
    have hS₁eq : (B ∪ S₁) \ B = S₁ := by

      have : Disjoint B S₁ := hS₁dis
      -- `simp` で `by`：
      -- (Lean標準：`by`ブロック内 `simp` は許容)
      -- using は使わない
      ext x
      constructor
      · intro hx
        rw [Finset.union_sdiff_cancel_left hS₁dis] at hx
        exact hx
      · intro hx
        have : x ∉ B := by
          exact Disjoint.notMem_of_mem_left_finset (id (Disjoint.symm hdis)) (hS₁sub hx)
        rw [@Finset.mem_sdiff]
        constructor
        · exact Finset.mem_union_right B hx
        · exact this
    have hS₂eq : (B ∪ S₂) \ B = S₂ := by
      have : Disjoint B S₂ := hS₂dis
      rw [Finset.union_sdiff_cancel_left hS₂dis]

    -- 以上より
    have := congrArg (fun T => T \ B) hU
    -- 左右をそれぞれ S に簡約
    simpa [hS₁eq, hS₂eq] using this
  -- `sum_image` で和を引き戻す
  -- `hEq` で台集合を書き換え、`sum_image` 適用
  have : ∑ I ∈
            (family V (R1 (V := V) (R := R) (Q := Q))).filter
              (fun I => I ∩ Rep (Q := Q) = B),
            φ I
        =
        ∑ S ∈ (Free (Q := Q)).powerset.image (fun S => B ∪ S), φ S := by
    -- ここは台集合の等式に ∑ を適用するだけ
    exact congrArg (fun (s : Finset (Finset α)) => ∑ I ∈ s, φ I) hEq
  -- 右辺の image 和を powerset の和に戻す
  -- sum_image の仮定：単射性（上で示した hinj）
  have himage :
      ∑ S ∈ (Free (Q := Q)).powerset.image (fun S => B ∪ S), φ S
        =
      ∑ S ∈ (Free (Q := Q)).powerset, φ (B ∪ S) := by
    refine Finset.sum_image ?hInj
    intro S₁ h₁ S₂ h₂ hEq'
    exact hinj h₁ h₂ hEq'
  -- 連結
  exact Eq.trans this himage

-- 仮に Free Q と Rep Q を型として定義
--variable (Q : Type) (FreeQ RepQ : Type)

-- 証明したい等式
--内部から参照あり
private lemma check_eq (cFreeQ cRepQ : Nat) :
  @Nat.cast ℤ instNatCastInt cFreeQ * 2 ^ (cFreeQ - 1) * 2 + (- (cFreeQ * 2 ^ cFreeQ) - cRepQ * 2 ^ cFreeQ) =
  - (cRepQ * 2 ^ cFreeQ) :=
by
  -- 左辺の第1項を簡約
  have h1 : @Nat.cast ℤ instNatCastInt  cFreeQ * 2 ^ (cFreeQ - 1) * 2 = cFreeQ * 2 ^ cFreeQ := by
    rw [mul_assoc,mul_comm]
    rw [← pow_succ]
    rw [mul_comm]
    by_cases cf:cFreeQ = 0
    case pos =>
      rw [cf]
      exact rfl
    case neg =>
      simp_all only [mul_eq_mul_left_iff, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀,
        Int.natCast_eq_zero, or_false]
      omega

  -- 左辺全体を書き換え
  rw [h1]
  -- 括弧を展開し、項を整理
  simp only [sub_eq_add_neg]
  -- |Free Q| * 2 ^ |Free Q| - |Free Q| * 2 ^ |Free Q| = 0
  rw [add_neg_cancel_left]
  -- 残りは - cRepQ * 2 ^ cFreeQ で、右辺と一致

/- 立方体引き戻しを使って、`φ I = (2:ℤ)|I| - |V|` のときの fiber 和を
    明示計算する（B は R₁ 上で閉）。 -/
--内部から参照あり
private lemma sum_fiber_contractRules_closedB_NDS2
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  {B : Finset α}
  (hBsub : B ⊆ Rep (Q := Q))
  (hBclosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B) :
  ∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
          (fun I => I ∩ Rep (Q := Q) = B),
        ((2 : Int) * (I.card : Int) - (V.card : Int))
    =
  (2 : Int) ^ (Free (Q := Q)).card
    * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := by
  classical
  -- fiber 和を立方体の和へ
  have hpull :=
    sum_fiber_contractRules_closedB_pullback
      (V := V) (R := R) (Q := Q) hV hBsub hBclosed
      (φ := fun I => ((2 : Int) * (I.card : Int) - (V.card : Int)))
  -- 以降は `∑ S ⊆ Free` の計算
  -- |B ∪ S| = |B| + |S|（B ⊥ S）
  have hdis : Disjoint (Rep (Q := Q)) (Free (Q := Q)) :=
    disjoint_Rep_Free (V := V) (R := R) (Q := Q)
  -- `(2:ℤ)*|B∪S| - |V|` を和に分配
  -- まず `∑` の線形化
  have hlin :
      ∑ S ∈ (Free (Q := Q)).powerset,
          ((2 : Int) * ((B ∪ S).card : Int) - (V.card : Int))
        =
      (2 : Int) * (∑ S ∈ (Free (Q := Q)).powerset, ((B ∪ S).card : Int))
        - (V.card : Int) * ((Free (Q := Q)).powerset).card := by

    have := sum_linearize_card_sub_const (V := V)
      ((Free (Q := Q)).powerset.image (fun S => B ∪ S))

    simp
    rw [mul_comm]
    ring_nf
    rw [add_comm]
    --simp_all
    --norm_cast
    rw [@Int.add_neg_eq_sub]
    simp
    simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul,
      Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    rw [Finset.sum_mul]

  -- |B ∪ S| = |B| + |S|（B ⊥ S, S ⊆ Free）
  have hsum_card :
      ∑ S ∈ (Free (Q := Q)).powerset, ((B ∪ S).card : Int)
        =
      ((Free (Q := Q)).powerset).card • (B.card : Int)
        + ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := by
    -- 各 S ごとに card(B∪S) = card B + card S を足していけば良い
    -- ここは `Finset.sum_congr` で書き換え
    have hpoint :
        ∀ {S}, S ∈ (Free (Q := Q)).powerset →
          ((B ∪ S).card : Int) = (B.card : Int) + (S.card : Int) := by
      intro S hS
      have hSsub : S ⊆ Free (Q := Q) := Finset.mem_powerset.mp hS
      have hdis' : Disjoint B S := by exact Disjoint.mono hBsub hSsub hdis
      /-
        (disjoint_Rep_Free (V := V) (R := R) (Q := Q)).mono_right hSsub
      -/
      -- `card_union`（交わり無し）で Nat の等式を取り、Int に持ち上げる
      have hNat : (B ∪ S).card = B.card + S.card := by
        simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul,
          Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat, Finset.mem_powerset,
          Finset.card_union_of_disjoint]

     -- Int に持ち上げ
      exact congrArg (fun n : Nat => (n : Int)) hNat
    -- これを和に敷衍
    -- 左辺の和を右辺の和に変形
    -- ここも `Finset` 帰納＋分配で丁寧にやってもOK。簡潔のため `by`。
    have : ∑ S ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt (B ∪ S).card = ∑ S ∈ (Free Q).powerset, ( @Nat.cast ℤ instNatCastInt B.card  +  @Nat.cast ℤ instNatCastInt S.card) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [Int.ofNat_inj.mp (hpoint hS)]
      simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, Finset.mem_powerset, Nat.cast_add]
    rw [this]
    rw [Finset.sum_add_distrib]
    ring_nf
    have : ∑ x ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt B.card = @Nat.cast ℤ instNatCastInt B.card *  @Nat.cast ℤ instNatCastInt (Free Q).powerset.card := by
      simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, Finset.mem_powerset]
      rw [mul_comm]
    rw [this]
    exact Int.add_comm (↑B.card * ↑(Free Q).powerset.card) (∑ x ∈ (Free Q).powerset, ↑x.card)


  -- 二項恒等式（既知として利用可）：
  -- 1) card powerset：|𝒫(Free)| = 2^{|Free|}
  have hPow_nat :
      ((Free (Q := Q)).powerset.card : Int)
        = ( (2 : Nat) ^ (Free (Q := Q)).card : Nat ) := by
    -- `card_powerset` を Int に持ち上げ
    have h := Finset.card_powerset (Free (Q := Q))
    -- Nat 等式を Int cast
    exact congrArg (fun n : Nat => (n : Int)) h
  -- 2) ∑_{S⊆Free} |S| = |Free| · 2^{|Free|-1}
  have hSumCard_nat :
      ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int)
        =
      (2 : Int) ^ ((Free (Q := Q)).card - 1) * (Free (Q := Q)).card := by

    exact sum_card_powerset_int (Free Q)


  -- V.card = Rep.card + Free.card
  have hVcard :
      (V.card : Int) = (Rep (Q := Q)).card + (Free (Q := Q)).card := by
    -- `card_Rep_add_card_Free` の Int 版
    have hNat :=
      card_Rep_add_card_Free (V := V) (R := R) (Q := Q)
    -- Int に持ち上げ
    apply congrArg (fun n : Nat => (n : Int))
    exact id (Eq.symm hNat)


  have := hpull
  -- 立方体和を線形化
  have := this.trans hlin
  -- |B∪S| の和を分解
  have := this.trans (by
    -- 右辺の第1項の中身を書き換える
    -- 2 * (  (#P(Free)) • |B|  +  ∑ |S| )  - |V| * #P(Free)
    -- ここで #P(Free) は powerset の要素数、`•` は nsmul
    apply congrArg (fun z => z)
    exact id (Eq.symm hlin))
  rw [this]

  --この式で合っているのか確認する。
  -- ∑ S ∈ (Free Q).powerset, (2 * ↑(B ∪ S).card - ↑V.card) = 2 ^ (Free Q).card * (2 * ↑B.card - ↑(Rep Q).card)
  have : 2 * (∑ S ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt (B ∪ S).card) - (∑ S ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt V.card) = 2 ^ (Free Q).card * (2 * ↑B.card - @Nat.cast ℤ instNatCastInt (Rep Q).card) := by

    rw [hsum_card]
    have :2 *(∑ S ∈ (Free Q).powerset,  @Nat.cast ℤ instNatCastInt S.card) - ∑ S ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt V.card=  - (2 ^ (Free Q).card) * (@Nat.cast ℤ instNatCastInt (Rep Q).card) := by
      rw [hVcard, hSumCard_nat]
      simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
        Nat.cast_ofNat]
      ring_nf
      exact check_eq (Free Q).card (Rep Q).card

    simp
    rw [mul_add]
    rw [mul_sub]
    have this2: 2 * (2 ^ (Free Q).card *  @Nat.cast ℤ instNatCastInt B.card) = 2 ^ (Free Q).card * (2 *  @Nat.cast ℤ instNatCastInt B.card) := by
      exact Int.mul_left_comm 2 (2 ^ (Free Q).card) ↑B.card
    rw [this2]
    have this3:2 ^ (Free Q).card * (2 * @Nat.cast ℤ instNatCastInt B.card) + 2 * ∑ S ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt S.card - 2 ^ (Free Q).card * @Nat.cast ℤ instNatCastInt V.card =
  2 ^ (Free Q).card * (2 * @Nat.cast ℤ instNatCastInt B.card) + ((- 2 ^ (Free Q).card) *  @Nat.cast ℤ instNatCastInt (Rep Q).card) := by
      rw [←this]
      simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, neg_mul]
      symm
      omega
    simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
      Nat.cast_ofNat, neg_mul]
    rfl

  rw [←this]
  simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow,
    Nat.cast_ofNat]
  convert this using 2
  ring

/-- R₁ 側 NDS₂ の因数分解式（Free の寄与が 2^{|Free|} に“出る”版）。 -/
--excessの証明で使う。nondecからも参照されている。
theorem NDS2_family_contractRules_factorized
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) : --言明の両辺にhVは出てきてないが証明では出てきている。
  NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
    =
  (2 : Int) ^ (Free (Q := Q)).card
    * ( ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
          ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) ) := by
  classical
  -- R₁ の family の総和を「閉な B の fiber」の二重和に分解（bind なし版）
  have hpart :=
    sum_family_contractRules_partition_as_closed_fibers
      (V := V) (R := R) (Q := Q) hV
      (φ := fun I => ((2 : Int) * (I.card : Int) - (V.card : Int)))
  -- 右辺の各 fiber を `sum_fiber_contractRules_closedB_NDS2` で評価
  have hstep :
      ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
          ∑ I ∈ (family V (R1 (V := V) (R := R) (Q := Q))).filter
                    (fun I => I ∩ Rep (Q := Q) = B),
              ((2 : Int) * (I.card : Int) - (V.card : Int))
        =
      ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
          ( (2 : Int) ^ (Free (Q := Q)).card
              * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) ) := by
    refine Finset.sum_congr rfl ?_
    intro B hBfam
    -- familyRep の定義から B ⊆ Rep かつ B は R₁ 上で閉
    have hPow_and_closed := Finset.mem_filter.mp hBfam
    have hBsub : B ⊆ Rep (Q := Q) := Finset.mem_powerset.mp hPow_and_closed.1
    have hBclosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B := hPow_and_closed.2
    -- fiber 和の評価
    exact
      sum_fiber_contractRules_closedB_NDS2
        (V := V) (R := R) (Q := Q) hV hBsub hBclosed

  have := hpart.trans hstep
  -- 係数を取り出し
  -- ∑ B (c * f B) = c * ∑ B f B
  -- 既知：有限和の線形性
  -- ここも線形性補題を使って仕上げてください。
  have hEq :
      ∑ I ∈ family V (R1 (V := V) (R := R) (Q := Q)),
          ((2 : Int) * (I.card : Int) - (V.card : Int))
        =
      ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
          ((2 : Int) ^ (Free (Q := Q)).card
            * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) :=
    hpart.trans hstep

  -- 定数係数 2^{|Free|} を外へ（mul_sum の対称形を使用）
  have hfactor :
      ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
          ((2 : Int) ^ (Free (Q := Q)).card
            * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        =
      (2 : Int) ^ (Free (Q := Q)).card *
        ∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
            ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
    exact
      (Finset.mul_sum
        (a := (2 : Int) ^ (Free (Q := Q)).card)
        (s := familyRep (V := V) (R := R) (Q := Q))
        (f := fun B => ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))).symm

  -- 定義を書き戻して終了
  unfold NDS2
  exact hEq.trans hfactor

noncomputable def Missing
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (B : Finset α) : Int :=
  (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int)

/-- 重み（バイアス）`|V| - 2|B|`（Int 型）。 -/
def Bias
  (V : Finset α) (B : Finset α) : Int :=
  (V.card : Int) - (2 : Int) * (B.card : Int)


lemma card_contractRules_lt_of_nonninj
  (R : Finset (Rule α))
  {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α)
  (noninj :
    ∃ t₁ ∈ R, ∃ t₂ ∈ R, t₁ ≠ t₂ ∧
      (σ (π t₁.1), σ (π t₁.2.1), σ (π t₁.2.2))
        = (σ (π t₂.1), σ (π t₂.2.1), σ (π t₂.2.2))) :
  (contractRules (π := π) (σ := σ) R).card < R.card := by
  classical
  let f : Rule α → Rule α :=
    fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2))
  rcases noninj with ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩
  -- 像は t₂ を消しても変わらない
  have hsub₁ :
      (R.image f) ⊆ ((R.erase t₂).image f) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨s, hsR, hys⟩
    by_cases hs : s = t₂
    · -- s = t₂ の像は t₁ の像に等しいので、erase側にも入る
      have hs' : f s = f t₁ := by
        have : f t₂ = f t₁ := by exact Eq.symm heq
        exact (by cases hs; simpa using this)
      have ht₁erase : t₁ ∈ R.erase t₂ :=
        Finset.mem_erase.mpr ⟨Ne.symm hne.symm, ht₁⟩
      subst hs hys
      simp_all only [ne_eq, Prod.mk.injEq, Finset.mem_erase, not_false_eq_true, and_self, Finset.mem_image, Prod.exists, f]
      apply Exists.intro
      · tauto
    · have hsErase : s ∈ R.erase t₂ := Finset.mem_erase.mpr ⟨hs, hsR⟩
      exact Finset.mem_image.mpr ⟨s, hsErase, hys⟩

  have hsub₂ :
      ((R.erase t₂).image f) ⊆ (R.image f) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨s, hsErase, hys⟩
    exact Finset.mem_image.mpr ⟨s, (Finset.mem_erase.mp hsErase).2, hys⟩
  have himage_eq : (R.image f) = ((R.erase t₂).image f) :=
    Finset.Subset.antisymm hsub₁ hsub₂
  have hcard_le_erase :
      ((R.erase t₂).image f).card ≤ (R.erase t₂).card :=
    Finset.card_image_le (s := R.erase t₂) (f := f)
  have hle : (R.image f).card ≤ (R.erase t₂).card := by
    have hc : (R.image f).card = ((R.erase t₂).image f).card :=
      congrArg Finset.card himage_eq
    exact hc.le.trans hcard_le_erase
  have hlt_erase : (R.erase t₂).card < R.card := by
    exact Finset.card_erase_lt_of_mem ht₂
  exact lt_of_le_of_lt hle hlt_erase

/-!
Charging/Barrier の主張を、このスレッドでは **仮定（axiom）として使用可** とします。
Thread A/B で証明される内容をここから参照する位置付けです。
-/
/- ★ Charging/Barrier 不等式（供給用・このスレッドでは仮定可） -/
--まだどこでも証明されていない。スレッドAで証明されるのか？
/-
axiom charging_barrier_ineq
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      Missing (V := V) (R := R) (Q := Q) B * Bias (V := V) B
    ≤ 0

/-- 展開形（C′ がそのまま欲しい形）。 -/
--メインから参照する予定。公理依存
theorem charging_barrier_ineq_expanded
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
        * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
    ≤ 0 := by
  -- 定義を展開して公理を適用
  change
    ∑ B ∈ (Rep (Q := Q)).powerset,
        Missing (V := V) (R := R) (Q := Q) B * Bias (V := V) B
      ≤ 0
  exact charging_barrier_ineq (V := V) (R := R) (Q := Q) hV
-/
