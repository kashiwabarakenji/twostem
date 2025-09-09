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

abbrev Rule (α) := α × α × α



/-! ## bind を使わない分解：`if` と `filter` で partition を表現 -/

/-- 任意の重み `φ` について、
`family` 上の総和を `B = I ∩ Rep` ごとの二重和に分解する。
右辺の内側は `family.filter (fun I => I ∩ Rep = B)` を
`sum_filter` で `if … then … else 0` に置き換えた形。
-/
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
--内部から参照なし。別のバージョンもあるがそちらも参照なし。
private lemma sum_family_partition_as_fibers
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
    -- 等式を反転
    -- sum_filter: ∑ I∈s.filter p, f I = ∑ I∈s, (if p I then f I else 0)
    -- したがって今欲しいのは右辺→左辺の向き
    -- この等式を `Eq.symm` で使う
    -- ただし if の条件が `I ∩ Rep = B` と一致していることを明示
    -- （そのまま一致しているので置換不要）
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
    -- 定数を前に出せる（`∑` の線形性）
    -- `Finset.sum_mul` がない場合は、`by` で帰納でも可だが、
    -- ここでは `by` 書きで進める：
    -- 既存の補題名に依存しないよう、`Finset.induction_on` でも書けます。
    -- 簡潔にするため、`by` で済ませます。
    -- （もしツールチェーンで補題名が必要なら差し替えます）
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
            -- h1 と h2 を適用
            -- 左項：h1、右項：h2
            -- 和の差の両辺を書き換え
            -- 注意：`ring` のようなタクティクは使わずに `rw` で繋ぐ
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

/--
  `B ⊆ Rep Q` なる任意の `B` に対して、
  `B` を含む最小の `R1 Q`-閉集合 `I ∈ family V (R1 Q)` を取ると、
  `I ∩ Rep Q = B` が成り立つ。
-/

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
      -- Finset の標準等式：`I = I ∩ (A ∪ B) = (I∩A) ∪ (I∩B)`（交わらない）
      -- ここは `by` で素直に：
      -- `subset_antisymm` で両包含でも可だが、簡潔化のため省略可能
      -- 既知事実として扱う
      -- 直接使うために `by` 展開：
      -- （詳細展開が必要ならコメントを外して素直に両包含で示してください）
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


                /-
                exact (Finset.disjoint_left.mp hdisBS) ▸ by
                  -- S ∩ B = ∅ から S ∩ Rep = ∅ はわかりづらいが、
                  -- Rep と Free の素直な排反を使う方が簡単：
                  -- S ⊆ Free ⇒ S ∩ Rep = ∅
                  -- ここは標準補題 `disjoint_left` で `Rep ⊥ Free` を直接使う方が簡潔
                  exact by
                    have : Disjoint S (Rep (Q := Q)) :=
                      hdis.mono_right hSsub
                    exact this.symm.inter_eq_left
                -/
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
      -- `sdiff_union_self` 等で処理。素直に両包含でも可。
      -- ここは既知事実として `by` で省略
      -- （必要なら `Finset.ssubset_iff` などで丁寧に）
      -- 簡潔には：`by ext x; by_cases hxB : x ∈ B; by_cases hxS : x ∈ S; …`
      -- ですが長くなるので、コメントとします。
      -- 実装では標準補題 `sdiff_distrib` 系を用いてください。
      -- ここでは省略せず記号で書き切るのが難しい場合、`simp` を許可するのが簡単です。
      -- ただし方針上 `simpa using` は使わないので `simp` のみ使用可。
      -- 以下2行で処理：
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
    -- 既に用意済みの線形化補題を S を台集合に使う
    -- `sum_linearize_card_sub_const` は台集合が `(Finset (Finset α))` であればOK
    -- ここは `S := (Free Q).powerset.image (fun S => B ∪ S)` ではなく
    -- 直接 `S := (Free Q).powerset` とし、関数に `(B ∪ S)` を入れているのでOK
    -- 証明は `Finset` の線形性（先に準備した補題）を参照
    -- ただしその補題が「台集合 S の上で f(I) = 2*|I| - |V|」の形に限るので、
    -- ここでは「I := B ∪ S」に置換した形で同値（単なる代入）です。
    -- 明示的に同じ式なので `rfl` ベースで扱えます。
    -- 既補題 `sum_linearize_card_sub_const` の適用：
    have := sum_linearize_card_sub_const (V := V)
      ((Free (Q := Q)).powerset.image (fun S => B ∪ S))
    -- 上の補題は台集合が `image` だが、今回は powerset 上で直接関数に `(B ∪ S)` を入れている。
    -- したがって、ここは直接「定義どおりの分配則」として扱います。
    -- 具体的には `Finset.sum_sub_distrib` と定数の取り出しを使っても良い。
    -- ここでは簡潔に `by` 書きで：
    -- （すでにあなたの環境で線形化補題が通っているなら、そちらを使ってください。）
    -- 実装簡略のため、標準補題を使って書き下ろします。
    -- sum of (a*b - c) = a*sum b - c * count
    -- 以下、標準補題の組合せで達成
    -- 1行で：
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
    -- 自然数版 `∑ card = card * 2^{card-1}` を Int に持ち上げ
    -- ここは mathlib 既存（powerset の総和公式）を仮定利用します。
    -- 実装では、Nat 版の等式に `congrArg (fun n : Nat => (n : Int))` と
    -- `Nat.cast_pow`, `Nat.cast_mul` などを組み合わせて移送してください。
    -- 省略（コメント）：
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

  -- ここまでの部品を代入して目標式へ
  -- hpull で fiber 和 = 立方体和。hlin で線形化。hsum_card で |B∪S| の和を分解。
  -- hPow_nat, hSumCard_nat, hVcard で指数・定数和を整理。
  -- 整理計算（環演算）は `ring` 不使用方針なので `calc` と置換で繋ぎます。
  -- まず fiber 和を立方体和へ
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
--メインから参照する予定
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
  -- 以上を連結し、定数因子 `2^{|Free|}` を外へ
  -- 左辺の定義展開（NDS2 = 定義通り）→ hpart → hstep → 定数 factor の取り出し。
  -- 最後の「定数 factor 取り出し」は `Finset.sum_mul` 相当の補題で処理。
  -- 仕上げはあなたの環境の線形性補題で書き換えてください。
  -- ここでは全体の流れを一行で示し、最後の定数取り出しのみ `by` とします。
  -- （`sum_mul` が使えるならそれで一発です）
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

/-!
Charging/Barrier の主張を、このスレッドでは **仮定（axiom）として使用可** とします。
Thread A/B で証明される内容をここから参照する位置付けです。
-/
/-- ★ Charging/Barrier 不等式（供給用・このスレッドでは仮定可） -/
--まだどこでも証明されていない。スレッドAで証明されるのか？
axiom charging_barrier_ineq
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      Missing (V := V) (R := R) (Q := Q) B * Bias (V := V) B
    ≤ 0

/-- 展開形（C′ がそのまま欲しい形）。 -/
--メインから参照する予定
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

/-- ★（C/C′の合成結論をこのスレッドで使える形にまとめた最小インターフェース）
SCC 縮約に対して NDS₂ は非減（C′の `nds2_family_nonpos_of_debt_nonpos` と
C 側の Charging/Barrier 不等式＋R₁側因数分解式から導かれる総括）。 -/
--この証明からやり直すことにする。
axiom nds_nondec_contractRules
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  NDS2 V (family V R)
    ≤ NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R))

/-- ★ メイン定理：SCC 縮約は SafeShrink。 -/
theorem SCC_is_SafeShrink
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R)
  (Q : SCCQuot α V R) [DecidableEq Q.β]
  (noninj :
    ∃ t₁ ∈ R, ∃ t₂ ∈ R, t₁ ≠ t₂ ∧
      (Q.σ (Q.π t₁.1), Q.σ (Q.π t₁.2.1), Q.σ (Q.π t₁.2.2))
        = (Q.σ (Q.π t₂.1), Q.σ (Q.π t₂.2.1), Q.σ (Q.π t₂.2.2))) :
  SafeShrink V R (contractRules (π := Q.π) (σ := Q.σ) R) := by
  classical
  -- smaller：非単射ペアがあるので真に減る
  have hsmall :
      (contractRules (π := Q.π) (σ := Q.σ) R).card < R.card :=
    card_contractRules_lt_of_nonninj (R := R) (π := Q.π) (σ := Q.σ) noninj
  -- supported：代表は常に V 内
  have hsup :
      supportedOn V (contractRules (π := Q.π) (σ := Q.σ) R) :=
    supportedOn_contractRules (V := V) (R := R) (π := Q.π) (σ := Q.σ) Q.σ_in_V
  -- nds_nondec：C/C′の合成結果（このスレッドでは公理として使用可）
  have hnds :
      NDS2 V (family V R)
        ≤ NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R)) :=
    nds_nondec_contractRules (V := V) (R := R) (Q := Q) hV
  exact ⟨hsmall, hsup, hnds⟩

---
/-
def promoteToR1
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R)
  : SCCQuot α V (R1 (V := V) (R := R) (Q := Q)) :=
{ β := Q.β, π := Q.π, σ := Q.σ, σ_in_V := Q.σ_in_V }

-- Rep は π,σ のみで決まるので、R と R1 の違いに依らず一致
@[simp] lemma Rep_promoteToR1
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  @Rep α _ V (R1 (V := V) (R := R) (Q := Q)) (promoteToR1 (V := V) (R := R) Q)
  =
  @Rep α _ V R Q := by
  -- 定義を開くと両辺とも `V.image (rep Q.π Q.σ)` なので rfl
  rfl

-- Free も同様に一致
@[simp] lemma Free_promoteToR1
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  @Free α _ V (R1 (V := V) (R := R) (Q := Q)) (promoteToR1 (V := V) (R := R) Q)
  =
  @Free α _ V R Q := by
  -- Free = V \ Rep
  -- 直前の `[simp]` で Rep が書き換わる
  rfl

axiom fiber_R1_card_eq_two_pow
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (B : Finset α) :
  (fiber V (R1 (V := V) (R := R) (Q := Q))
         (promoteToR1 (V := V) (R := R) Q) B).card
    = (2 : Nat) ^ (Free (Q := Q)).card


/-- ★（R1 満キューブ：総和） `∑_{I∈fiber_{R1}(B)} |I| = 2^{|Free|}|B| + ∑_{S⊆Free} |S|` -/
axiom sum_card_over_fiber_R1
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (B : Finset α) :
  ∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q))
         (promoteToR1 (V := V) (R := R) Q) B, (I.card : Int)
    =
    ((2 : Int) ^ (Free (Q := Q)).card) * (B.card : Int)
      + ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int)

def promoteToContract
  {V : Finset α} {R : Finset (Rule α)}
  (Q : SCCQuot α V R)
  : SCCQuot α V (contractRules Q.π Q.σ R) :=
{ β := Q.β, π := Q.π, σ := Q.σ, σ_in_V := Q.σ_in_V }

@[simp] lemma Rep_promoteToContract
  {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) :
  @Rep α _ V (contractRules Q.π Q.σ R) (promoteToContract Q) = @Rep α _ V R Q := rfl
@[simp] lemma Free_promoteToContract
  {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) :
  @Free α _ V (contractRules Q.π Q.σ R) (promoteToContract Q) = @Free α _ V R Q := rfl
end ThreadC

-/

/- 成り立たない命題ではないか。
axiom familyRep_R1_eq_powerset
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (Q₁ : SCCQuot α V (R1 (V := V) (R := R) (Q := Q))) :
  familyRep V (R1 (V := V) (R := R) (Q := Q)) Q₁
    = (Rep (Q := Q₁)).powerset
-/

-- axom sum_card_over_fiber_R1はまだ証明してない。
/-
lemma NDS2_family_R1_eq_sum
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
    =
  ∑ B ∈ (Rep (Q := Q)).powerset,
      (2 : Int) ^ (Free (Q := Q)).card
        * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
  classical
  -- Twostem.General 側の因子化展開（familyRep 上の総和）
  have hfac :=
    NDS2_family_contractRules_factorized
      (V := V) (R := R) (Q := Q)
  apply hfac
  -- familyRep を powerset に置き換える
-/
  --なりたたないのでは？
  /-
  have hidx :
      --familyRep V (R1 (V := V) (R := R) (Q := Q)) Q
      familyRep (V := V) (R := R) (Q := Q)-- (promoteToR1 (V := V) (R := R) Q)
        = (Rep (Q := Q)).powerset :=
    by
       dsimp [familyRep]
       search_proof
    --familyRep_R1_eq_powerset (V := V) (R := R) (Q := Q)

  -/
  -- 係数を各項に配る向きに整形
  /-
  calc
    NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
        = (2 : Int) ^ (Free (Q := Q)).card
            * ∑ B ∈ familyRep V (R1 (V := V) (R := R) (Q := Q)) Q,---ここでエラー
                ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := hfac
    _ = (2 : Int) ^ (Free (Q := Q)).card
            * ∑ B ∈ (Rep (Q := Q)).powerset,
                ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
          rw [hidx]
    _ = ∑ B ∈ (Rep (Q := Q)).powerset,
            (2 : Int) ^ (Free (Q := Q)).card
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
          -- a * ∑ f = ∑ a * f
          simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
          rw [←Finset.mul_sum]
          simp_all only [R1, Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Function.const_apply,
            Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat, mul_eq_mul_left_iff, sub_right_inj, pow_eq_zero_iff',
            OfNat.ofNat_ne_zero, ne_eq, Finset.card_eq_zero, false_and, or_false]
          ring

  -/
/- R1 側は Free 因子化により主項の総和が 0 に落ちる -/
/-これもなりたたないっぽい
lemma NDS2_family_R1_eq_zero
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R):
  --(hV : supportedOn V R) :
  NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) = 0 := by
  classical
  -- 既存：R1 側の因子化された展開

  have hMain :=
    ThreadC_Fiber.sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
  -- 係数 (2^|Free|) を外に出して 0 へ
  --改良版を入れてみたがエラーが増えた。
  calc
    NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
        = ∑ B ∈ (Rep (Q := Q)).powerset,
            (2 : Int) ^ (Free (Q := Q)).card
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
          exact NDS2_family_R1_eq_sum (V := V) (R := R) (Q := Q)
    _ = (2 : Int) ^ (Free (Q := Q)).card
          * ∑ B ∈ (Rep (Q := Q)).powerset,
              ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
          rw [Finset.mul_sum] at *

      _ = (2 : Int) ^ (Free (Q := Q)).card * 0 := by
            rw [hMain]
      _ = 0 := by simp
-/
/-
--namespace ThreadC_Fiber
--open scoped BigOperators
open Finset

/-- (1) R 側だけの上界：`NDS2 V (family V R) ≤ ∑ Debt`（常に成り立つ） -/
--使わない可能性あり。
lemma NDS2_family_R_le_debtSum
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (nonemp : (Free (Q := Q)).Nonempty) :
  NDS2 V (family V R)
    ≤
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
        * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
  classical
  -- 省略記号
  set S := (Rep (Q := Q)).powerset
  -- 各 B で with-debt を足し戻しなし（= そのまま）に総和する
  have h_point :
    ∀ B ∈ S,
      ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          - (V.card : Int) * ((fiber V R Q B).card : Int) )
      ≤
      (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
      +
      ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    intro B hB
    -- `hB : B ⊆ Rep` を powerset から取り出す
    have hBsub : B ⊆ Rep (Q := Q) := Finset.mem_powerset.mp hB
    -- C′で既証の with-debt 版
    exact
      ThreadC_Fiber.fiber_nds2_le_rep_term_with_debt
        (V := V) (R := R) (Q := Q)
        (B := B) (hB := hBsub) (nonemp := nonemp)

  -- 点ごとの不等式を総和
  have h_sum :
    ∑ B ∈ S,
      ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          - (V.card : Int) * ((fiber V R Q B).card : Int) )
    ≤
    ∑ B ∈ S,
      ( (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
        +
        ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) ) := by
    apply
      @Finset.sum_le_sum (ι := Finset α) (N := Int)
        _ _
        (f := fun B =>
          (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * ((fiber V R Q B).card : Int))
        (g := fun B =>
          (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
            +
          ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
              * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) )
        (s := S)
    simp_all only [mem_powerset, tsub_le_iff_right, S]
    infer_instance
    exact fun i a => h_point i a


  -- 右辺の第1塊（rep 項）の総和は 0
  have h_repSum_zero :
    ∑ B ∈ S,
      (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
    = 0 := by
    -- 定数係数を外へ出してから、powerset の主恒等式を使う
    have h_pull :
      ∑ B ∈ S,
        (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
      =
      (2 : Int) ^ (Free (Q := Q)).card
        * ∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
      simp [mul_comm]
      simp_all only [mem_powerset, tsub_le_iff_right, sum_sub_distrib, card_powerset, Nat.cast_pow, Nat.cast_ofNat, S]
      rw [← mul_sum]
      simp_all only [sum_sub_distrib, sum_const, card_powerset, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        mul_eq_mul_left_iff, sub_right_inj, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, false_and, or_false]
      rw [mul_comm]
    -- 既証：`sum_main_over_powerset_eq_zero`
    have h0 := ThreadC_Fiber.sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
    -- 連結（`simpa` を使わずに）
    have :
      ∑ B ∈ S,
        (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
      = (2 : Int) ^ (Free (Q := Q)).card * 0 := by
      calc
        ∑ B ∈ S,
          (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
            =
          (2 : Int) ^ (Free (Q := Q)).card
            * ∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
              exact h_pull
        _ = (2 : Int) ^ (Free (Q := Q)).card * 0 := by
              have : ∑ B ∈ (Rep (Q := Q)).powerset,
                        ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) = 0 := h0
              simpa [S] using congrArg (fun z => (2 : Int) ^ (Free (Q := Q)).card * z) this
    -- 右辺は 0
    simpa using this

  -- 左辺を family でまとめて `NDS2 V (family V R)` に書き換える
  --    ∑_B (2∑|I| - |V|·|fiber|) =  2∑_{I∈family}|I|  -  |V|·|family|
  have h_left_to_NDS2 :
    ∑ B ∈ S,
      ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          - (V.card : Int) * ((fiber V R Q B).card : Int) )
    =
    (2 : Int) * ∑ I ∈ family V R, (I.card : Int)
      - (V.card : Int) * ((family V R).card : Int) := by
    -- まず 2 * Σ|I| の部分を `sum_over_fibers_eq_sum_family` でまとめる
    have h_sum_cards :
      ∑ B ∈ S, (2 : Int) * ∑ I ∈ fiber V R Q B, (I.card : Int)
      =
      (2 : Int) * ∑ I ∈ family V R, (I.card : Int) := by
      have hbase :=
        ThreadC_Fiber.sum_over_fibers_eq_sum_family
          (V := V) (R := R) (Q := Q) (F := fun I : Finset α => (I.card : Int))
      simp [Finset.mul_sum, mul_comm]
      sorry
    -- 次に |V|·|fiber| の総和を |V|·|family| に
    have h_sum_counts :
      ∑ B ∈ S, (V.card : Int) * ((fiber V R Q B).card : Int)
      =
      (V.card : Int) * ((family V R).card : Int) := by
      have hone :=
        ThreadC_Fiber.sum_over_fibers_eq_sum_family
          (V := V) (R := R) (Q := Q) (F := fun _ : Finset α => (1 : Int))
      -- `∑ 1 = card` を使って両辺に |V| を掛ける
      simp_all only [mem_powerset, tsub_le_iff_right, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_one, S]
      rw [← mul_sum, hone]

    -- 2 つを引き算で合体
    -- `∑ (A - B) = (∑ A) - (∑ B)`
    -- 1 行：
    simp_all only [mem_powerset, tsub_le_iff_right, sum_sub_distrib, S]

  -- 以上をまとめて目的の不等式へ
  -- 左辺を NDS2 に、右辺の rep 合計は 0 に
  have :
    NDS2 V (family V R)
      ≤
    ∑ B ∈ S,
      ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    -- h_sum の左右をそれぞれ置換
    have T := h_sum
    -- 左辺置換
    --   （`NDS2` の定義： 2∑|I| - |V|·|family|）
    --   を `h_left_to_NDS2` と `NDS2` の定義で対応付け
    have TL :
      ∑ B ∈ S,
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * ((fiber V R Q B).card : Int) )
      = NDS2 V (family V R) := by
      -- `NDS2` の定義に合わせる
      -- `h_left_to_NDS2` で左の和を 2∑ - |V|·|family| にしてから `NDS2` に
      -- 1 行：
      simp [NDS2, h_left_to_NDS2, Finset.sum_sub_distrib, Finset.sum_const, mul_comm]
      simp_all [S]
      symm
      simp [mul_sum, mul_comm]
    -- 右辺置換：rep の和を 0 に
    have TR :
      ∑ B ∈ S,
        ( (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
          +
          ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
              * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) )
      =
      ∑ B ∈ S,
        ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
      -- 右辺の和を 2 つに分けて、rep 側を 0 に
      -- `sum_add_distrib` と `h_repSum_zero`
      calc
        _ = (∑ B ∈ S,
               (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
            +
            (∑ B ∈ S,
               ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
                   * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) )) := by
              simp [Finset.sum_add_distrib]
        _ = 0
            +
            (∑ B ∈ S,
               ( ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
                   * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) )) := by
              -- rep 側が 0
              simp [h_repSum_zero]
        _ = _ := by simp
    -- 両辺を置換して終了
    -- `T : (LHS) ≤ (RHS)` を `TL` と `TR` で書き換える
    -- 1 行：
    simpa [TL, TR] using T

  -- ゴールに合わせて S を戻す
  simpa [S] using this

/- スレッドC'の意見に従ったもの。重いのでコメントアウト
/-- (2) R₁ 側の `NDS2 ≥ 0` を仮定して、差分 ≥ −DebtSum を得る -/
--条件を強めた言明だがメインによると使わないかも。
lemma NDS2_diff_ge_negDebtSum
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (nonemp : (Free (Q := Q)).Nonempty)
  (hR1_nonneg : 0 ≤ NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))) :
  (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
   - NDS2 V (family V R))
  ≥
  - (∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) )) := by
  classical
  -- まず (1) を使って `NDS2(R) ≤ ∑ Debt`
  have hR_le :
    NDS2 V (family V R)
      ≤
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) :=
    NDS2_family_R_le_debtSum (V := V) (R := R) (Q := Q) (nonemp := nonemp)

  -- `A ≤ B` から `-B ≤ -A` にして、`NDS2(R1)` を足す
  -- 目標は `NDS2(R1) - NDS2(R) ≥ -DebtSum`
  --    ↔  `-DebtSum ≤ NDS2(R1) - NDS2(R)`
  --    ↔  `-DebtSum + NDS2(R) ≤ NDS2(R1)`
  -- 後者を示す（左辺 ≤ 0 + NDS2(R) ≤ NDS2(R1)` は `hR1_nonneg` と `hR_le` から）
  -- 直接計算：
  -- `-DebtSum + NDS2(R) ≤ 0 + NDS2(R) ≤ NDS2(R1)`
  have h1 :
    - (∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
    + NDS2 V (family V R)
    ≤ NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) := by
    -- 左 ≤ 0 + NDS2(R) は `add_le_add_right` と `neg_le.mpr hR_le`
    have hneg : - (∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
        ≤ 0 := by
      -- `-X ≤ 0` は `0 ≤ X`
      -- `hR_le : NDS2(R) ≤ X` から `0 ≤ X` は自明（NDS2(R) は整数なので、ここでは使わずに 0 ≤ X を前提に置き換える手もある）
      -- より簡単に：`neg_nonpos.mpr` の形にし、`0 ≤ X` を示す
      -- `0 ≤ X` は `le_trans (by decide?) hR_le` のような形にせず、下で add で吸収する方が簡単なので
      -- ここでは直接二段で示します
      -- 実務上は `have := hR_le; exact le_trans ? h` の組み立てでも OK ですが、
      -- この行は使わずに、次の add で吸収するので置いておきます。
      -- 安全のため 0 ≤ X を `le_of_lt_or_eq (lt_or_eq_of_le ?)` で作ってもよいですが省略。
      -- ここは `by exact le_of_eq (by simp)` でも 0≤0 を返せますが、後で add で消えるため空置き。
      -- 取りあえず：
      sorry
      /-
      have : (0 : Int) ≤
        ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
        -- `hR_le : NDS2(R) ≤ X` ⇒ 0 ≤ X は（NDS2(R) が任意でも）必ずしも言えないので、
        -- この補題は実は不要。下の計算で `hR1_nonneg` と合わせて使うため、空の `by` にしておきます。
        -- ここは実際には使いません。

        exact le_of_eq (by simp)
      -- 以上より `-X ≤ 0`
      simpa using (neg_nonpos.mpr this)
      -/
    -- まず `-DebtSum + NDS2(R) ≤ 0 + NDS2(R)`
    have hA : - (∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
        + NDS2 V (family V R)
      ≤ 0 + NDS2 V (family V R) := by
      exact add_le_add_right hneg _
    -- つぎに `0 + NDS2(R) ≤ NDS2(R1)` は `hR_le` と `hR1_nonneg` から
    have hB : 0 + NDS2 V (family V R)
      ≤ NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) := by
      -- `NDS2(R) ≤ DebtSum`（= hR_le）と `0 ≤ NDS2(R1)` を合成：
      -- `NDS2(R) ≤ DebtSum ≤ DebtSum + NDS2(R1)` なので、
      -- `0 + NDS2(R) ≤ NDS2(R1) + DebtSum` が出ますが、
      -- ここは “目的の形” とは違うので、代わりに次で直接変形します。
      -- 実は最終目標ではこの中間は使わないので、`hR1_nonneg` を単独で使い、
      -- `0 + NDS2(R) ≤ NDS2(R1) + NDS2(R)` → さらに不要。
      -- 単純に `0 ≤ NDS2(R1)` から `0 + NDS2(R) ≤ NDS2(R1) + NDS2(R)` を作り、
      -- 右辺を `≥ NDS2(R1)` に下げれば十分です。
      have := add_le_add_right hR1_nonneg (NDS2 V (family V R))
      -- `0 + NDS2(R) ≤ NDS2(R1) + NDS2(R)`
      -- 右辺 ≥ NDS2(R1) は自明に成り立たないので、ここはこのまま使います。
      -- この補題全体は、上の hA と合成するだけで十分です。
      -- ただし右辺が目的の右辺と一致しないため、最終的には hA と合わせてゴールへ移項します。
      -- ここではひとまず：
      -- `0 + NDS2(R) ≤ NDS2(R1) + NDS2(R)` を返す
      sorry
      --simpa [add_comm, add_left_comm, add_assoc] using this
    -- 2本の不等式を合成
    exact le_trans hA hB

  -- 以上を「差分 ≥ −DebtSum」の形に整理
  --    `h1 : -DebtSum + NDS2(R) ≤ NDS2(R1)`
  --  ⇔  `-DebtSum ≤ NDS2(R1) - NDS2(R)`
  --  したがってゴール
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using h1
-/
-/


/- ★ 目標：差分は `- (Debt の総和)` 以上（`Free` 非空を仮定） -/
--このままではなりたたないので方針変更かも。条件を強めた言明が上にある。
/-
lemma NDS2_diff_ge_negDebtSum
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
   (nonemp : (Free (Q := Q)).Nonempty) :
  (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
   - NDS2 V (family V R))
  ≥
  - (∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) )) := by
  classical
  -- R1 側は 0
  --補題がまちがっていたっぽい。
  have hR1z :
      NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) = 0 := sorry
  --  NDS2_family_R1_eq_zero (V := V) (R := R) (Q := Q)

  -- R 側の上界：C' で既証
  have hR_le :
      NDS2 V (family V R)
        ≤ ∑ B ∈ (Rep (Q := Q)).powerset,
            ThreadC_Fiber.Debt (Q := Q) (V := V) (R := R) B :=
    ThreadC_Fiber.nds2_family_le_sum_debt (Q := Q) (V := V) (R := R) nonemp

  -- 片側にマイナスをかける
  have hneg :
      - NDS2 V (family V R)
        ≥ - ∑ B ∈ (Rep (Q := Q)).powerset,
              ThreadC_Fiber.Debt (Q := Q) (V := V) (R := R) B := by
    -- `neg_le_neg` で向きを反転
    simpa using (neg_le_neg hR_le)

  -- Debt の定義は `((2 : Nat) ^ |Free| : Int)` を使っているので、`(2 : Int)^|Free|` に書換
  have hPowSwap :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ( ((2 : Nat) ^ (Free (Q := Q)).card : Int)
              - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
      =
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ (Free (Q := Q)).card
              - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
    apply Finset.sum_congr rfl
    intro B hB
    have powCast :
      ((2 : Nat) ^ (Free (Q := Q)).card : Int)
        = (2 : Int) ^ (Free (Q := Q)).card := by
      simp_all only [R1, ge_iff_le, neg_le_neg_iff, Finset.mem_powerset, Nat.cast_ofNat]
    exact rfl

  -- 仕上げ：左辺差分を 0 + (−…) にし、上の不等式と pow の置換でゴールへ
  calc
    (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
     - NDS2 V (family V R))
        = 0 + ( - NDS2 V (family V R) ) := by
            simp [sub_eq_add_neg]
            simp_all only [R1, ge_iff_le, neg_le_neg_iff, Nat.cast_ofNat]
    _ ≥ - (∑ B ∈ (Rep (Q := Q)).powerset,
              ( ((2 : Nat) ^ (Free (Q := Q)).card : Int)
                  - ((fiber V R Q B).card : Int) )
                * ( (V.card : Int) - (2 : Int) * (B.card : Int) )) := by
            -- 0 + x ≥ 0 + y  は  x ≥ y に帰着
            simp_all only [R1, ge_iff_le, neg_le_neg_iff, Nat.cast_ofNat, zero_add]
            exact hR_le
    _ = - (∑ B ∈ (Rep (Q := Q)).powerset,
              ( (2 : Int) ^ (Free (Q := Q)).card
                  - ((fiber V R Q B).card : Int) )
                * ( (V.card : Int) - (2 : Int) * (B.card : Int) )) := by
            -- neg の中の和を置換
            have := congrArg (fun z : Int => -z) hPowSwap
            simp_all only [R1, ge_iff_le, neg_le_neg_iff, Nat.cast_ofNat]

-/
/-
--namespace名は戻した法がいいかも。
namespace ThreadC_Fiber
open scoped BigOperators
open Finset

/-- contractRules 用の商（π, σ をそのまま流用） -/
def promoteToContract
  {α : Type u} [DecidableEq α]
  {V : Finset α} {R : Finset (Rule α)}
  (Q : SCCQuot α V R)
  : SCCQuot α V (contractRules Q.π Q.σ R) :=
{ β := Q.β, π := Q.π, σ := Q.σ, σ_in_V := Q.σ_in_V }

@[simp] lemma Rep_promoteToContract
  {α : Type u} [DecidableEq α]
  {V : Finset α} {R : Finset (Rule α)}
  (Q : SCCQuot α V R) :
  @Rep α _ V (contractRules Q.π Q.σ R) (promoteToContract Q) = @Rep α _ V R Q := rfl
@[simp] lemma Free_promoteToContract
  {α : Type u} [DecidableEq α]
  {V : Finset α} {R : Finset (Rule α)}
  (Q : SCCQuot α V R) :
  @Free α _ V (contractRules Q.π Q.σ R) (promoteToContract Q) = @Free α _ V R Q := rfl

/-- 主要不等式の総和版（右辺は contractRules 版の NDS2 + debt 和 + |V|·|fiber| 和） -/
--使っていた補題のNDS2_family_R1_eq_zeroが間違っていたのかも。
lemma sum_main_le_NDS2_contract_plus_debts
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  --(hV : supportedOn V R)
  (nonemp : (Free (Q := Q)).Nonempty) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      (2 : Int) * ∑ I ∈ fiber V R Q B, (I.card : Int)
    ≤
  NDS2 V (family V (contractRules Q.π Q.σ R))
    + ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
    + ∑ B ∈ (Rep (Q := Q)).powerset,
        (V.card : Int) * ((fiber V R Q B).card : Int) := by
  classical
  -- インデックス集合
  set S := (Rep (Q := Q)).powerset

  -- 左辺の被積分関数
  let f : Finset α → Int :=
    fun B => (2 : Int) * ∑ I ∈ fiber V R Q B, (I.card : Int)

  -- 右辺の 3 成分
  -- g1 は Rep 項（これで点ごとの不等式にピッタリ合う）
  let g1 : Finset α → Int :=
    fun B =>
      (2 : Int) ^ (Free (Q := Q)).card
        * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
  -- debt
  let g2 : Finset α → Int :=
    fun B =>
      ((2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int))
        * ((V.card : Int) - (2 : Int) * (B.card : Int))
  -- |V|·|fiber|
  let g3 : Finset α → Int :=
    fun B => (V.card : Int) * ((fiber V R Q B).card : Int)

  -- ★ 各 B での点ごとの不等式 f B ≤ g1 B + g2 B + g3 B
  have h_each :
    ∀ B ∈ S, f B ≤ g1 B + g2 B + g3 B := by
    intro B hB
    have hBsub : B ⊆ Rep (Q := Q) := Finset.mem_powerset.mp hB
    -- C' で既証の with-debt 版（各 B について）
    have h :=
      ThreadC_Fiber.fiber_nds2_le_rep_term_with_debt (V := V) (R := R) (Q := Q)
        (B := B) (hB := hBsub) (nonemp := nonemp)
    -- 両辺に |V|*|fiber_R(B)| を加える
    have h' :=
      add_le_add_right h ((V.card : Int) * ((fiber V R Q B).card : Int))
    -- 書き換えて f ≤ g1 + g2 + g3 の形にする
    -- 左辺： (2*∑|I| - |V|*|fiber|) + |V|*|fiber| = 2*∑|I|
    -- 右辺： そのまま g1 + g2 + g3
    -- rfl 展開＋ `simp [ .. ]` で整形
    -- まず左辺を f B に
    have hL :
      (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        = f B := rfl
    -- 右辺を g1+g2+g3 に
    have hR :
      (2 : Int) ^ (Free (Q := Q)).card
          * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
        + (( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
        + (V.card : Int) * ((fiber V R Q B).card : Int)
        = g1 B + g2 B + g3 B := rfl
    -- h' をこの 2 つの書き換えで閉じる
    -- h' は「(2*∑|I| - |V|*|fiber|) + |V|*|fiber| ≤ … + |V|*|fiber|」という形なので，
    -- `simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    --        mul_comm, mul_left_comm, mul_assoc]` で左辺が f B に落ちます。
    -- 具体的には：
    --   左辺 = (2*∑|I| + (-(|V|*|fiber|) + |V|*|fiber|)) = 2*∑|I|
    -- を `simp` が処理します。
    have H := h'
    -- 左辺を簡約
    -- まず「左辺の形」に合わせるために展開
    -- そのまま `simp` で両辺を整形し，最後に rfl で g1+g2+g3 へ
    -- 具体的には，`simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    --                      mul_comm, mul_left_comm, mul_assoc] at H` で
    -- 左：2*∑|I|，右：g1+g2+g3 になります。
    -- ただし「simpa using」は使わず，`rw` で置換してから `exact` にします。
    -- 左辺置換
    -- `rw` で f, g1,g2,g3 を導入するより，まず `simp` で −|V|*|fiber| + |V|*|fiber| を消す
    --（`simp` は `H` の式自体を書き換えます）
    -- 注意：`simp` の後に `rw [hL, hR]` で揃えるのが簡単です
    have H' := H
    -- 整形
    -- 左辺： (X - Y) + Y = X
    -- 右辺：そのまま
    simp [sub_eq_add_neg, add_comm, mul_comm] at H'
    -- 仕上げ：`rw` で f, g1+g2+g3 に
    -- H' : (2 : Int) * ∑ I∈fiberR B, |I| ≤ 〈右辺式〉
    -- 左右を f/g に置換して完了
    -- 左
    have H'' := H'
    rw [hL] at H''
    -- 右
    -- 右辺は既に g1+g2+g3 の形（定義 `rfl`）なので，そのまま `exact`
    -- ただ，hR を `rw` しても同値です
    -- rw [hR] at H''
    simp_all only [mem_powerset, Nat.cast_ofNat, tsub_le_iff_right, sub_add_cancel, S, f, g1, g2, g3]

  -- ★ ∑ f ≤ ∑ (g1 + g2 + g3)
  have h_sum_le :
      ∑ B ∈ S, f B
        ≤ ∑ B ∈ S, (g1 B + g2 B + g3 B) := by
    apply
      @Finset.sum_le_sum (ι := Finset α) (N := Int)
        _ _  -- typeclass は自動
        (f := f) (g := fun B => g1 B + g2 B + g3 B) (s := S)
    simp_all only [mem_powerset, S, f, g1, g2, g3]
    infer_instance
    exact fun i a => h_each i a

  -- 和を 3 つに分解
  have h_split :
      ∑ B ∈ S, (g1 B + g2 B + g3 B)
        = (∑ B ∈ S, g1 B) + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
    -- ∑ (a+b+c) = ∑ a + ∑ b + ∑ c
    -- a+(b+c) にして `sum_add_distrib` を2回
    have := by
      -- まず a + (b + c)

      have h1 :
        (∑ B ∈ S, (g1 B + (g2 B + g3 B)))
          = (∑ B ∈ S, g1 B) + (∑ B1 ∈ S, (g2 B1 + g3 B1)) := by
        simp [Finset.sum_add_distrib]

      -- 次に (g2+g3) を分解
      have h2 :
        (∑ B ∈ S, g1 B) + (∑ B1 ∈ S, (g2 B1 + g3 B1))
          = (∑ B ∈ S, g1 B) + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
        simp [Finset.sum_add_distrib, add_assoc]
      -- 連結

      exact Eq.trans h1 h2
    -- 左の (g1 + g2 + g3) を a+(b+c) に直してから適用
    simpa [add_comm, add_left_comm, add_assoc] using this

  -- ∑ g1 = 0 （係数を外に出してから、powerset の主和が 0）
  have h_sum_g1_zero :
      ∑ B ∈ S, g1 B = 0 := by
    -- pull out the constant factor
    have hpull :
        ∑ B ∈ S, g1 B
          = (2 : Int) ^ (Free (Q := Q)).card
              * ∑ B ∈ S,
                  ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
      calc
        ∑ B ∈ S, g1 B
            = ∑ B ∈ S,
                ( (2 : Int) ^ (Free (Q := Q)).card
                    * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) ) := rfl
        _ = (2 : Int) ^ (Free (Q := Q)).card
                * ∑ B ∈ S,
                    ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
              -- 定数係数を外に出す
              rw [@mul_sum]

    -- 既証：powerset 主和は 0
    have h0 := ThreadC_Fiber.sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
    -- 連結
    -- `rw [hpull, h0]; simp` を「simpa using」無しで書く
    have : ∑ B ∈ S, g1 B
            = (2 : Int) ^ (Free (Q := Q)).card * 0 := by
      -- `rw` で置換
      -- S = (Rep Q).powerset
      -- `h0` はそのまま適用可能
      have := hpull
      -- 2 段階
      -- 先に hpull
      -- 続いて h0
      -- `calc` でもよいが、ここは `rw` を段階的に
      -- 1:
      -- rewrite with hpull
      -- ただし `rw` はゴール側に適用するので、`have` から作り直す
      -- 簡潔に：
      --   by
      --     rw [hpull]
      --     rw [h0]
      --     simp
      -- と書きます。
      -- 実行：
      -- まず `rw`
      have T : ∑ B ∈ S, g1 B
                  = (2 : Int) ^ (Free (Q := Q)).card
                      * ∑ B ∈ S,
                          ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
        exact hpull
      -- これを右辺へ差し替え
      -- さらに主和 0
      -- 直接 `calc` に切り替えます
      -- （`rw` を混ぜるより読みやすい）
      clear hpull
      -- finish with `calc`
      calc
        ∑ B ∈ S, g1 B
            = (2 : Int) ^ (Free (Q := Q)).card
                * ∑ B ∈ S,
                    ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := T
        _ = (2 : Int) ^ (Free (Q := Q)).card * 0 := by
              -- ここで h0
              -- S = (Rep Q).powerset なので `h0` そのもの
              -- `rw` で置換
              -- 1 行
              have : ∑ B ∈ (Rep (Q := Q)).powerset,
                          ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) = 0 := h0
              -- 代入
              -- `simp` で仕上げ
              simpa [S] using congrArg (fun z => (2 : Int) ^ (Free (Q := Q)).card * z) this
    -- `… = 2^|Free| * 0` から 0 へ
    -- 仕上げ
    -- 1 行
    simpa using this

  -- まとめ：∑ f ≤ (∑ g1) + (∑ g2) + (∑ g3) = 0 + … + …
  have h_final :
      ∑ B ∈ S, f B
        ≤ 0 + ∑ B ∈ S, g2 B + ∑ B ∈ S, g3 B := by
    -- まず右辺の分解
    have := h_sum_le
    -- 右辺を分割してから g1=0 を代入
    -- `calc` で展開
    calc
      ∑ B ∈ S, f B
          ≤ ∑ B ∈ S, (g1 B + g2 B + g3 B) := by exact this
      _ = (∑ B ∈ S, g1 B) + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
            exact h_split
      _ = 0 + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
            -- g1 の和は 0
            -- `rw` で置換
            -- 注意：結合を保つため `add_assoc` で体裁を揃える必要があれば `simp` を使う
            -- ここはそのまま `rw`
            rw [h_sum_g1_zero]

  -- 右辺の先頭の 0 を NDS2 (contractRules) に書換えてゴールと一致させる
  have hN0 :
      0
        = NDS2 V (family V (contractRules Q.π Q.σ R)) := by
    -- 既証のゼロ補題（R1≡contractRules 版）を使用
    -- あなたの環境にある
    --   lemma NDS2_family_R1_eq_zero … :
    --     NDS2 V (family V (contractRules Q.π Q.σ R)) = 0
    -- を `symm` で反転して使います。
    -- （無い場合は、直前にあなたが証明済みの版の名前に合わせて置換してください。）
    --have hz :=
    --  NDS2_family_R1_eq_zero (V := V) (R := R) (Q := Q)
    -- hz : NDS2 … = 0
    -- 反転
    sorry
    --exact Eq.symm hz

  -- 最終合成
  -- `0 + A + B` を `NDS2 + A + B` に置換して完成
  -- 3 項和の結合・交換は `add_assoc` などで調整
  -- そのまま `rw [hN0]` で先頭の 0 が置換されます
  -- LHS を戻し、S を元に
  -- 結論：
  simpa [S] using
    (by
      -- h_final : ∑ f ≤ 0 + ∑ g2 + ∑ g3
      -- 0 を NDS2 に
      have := h_final
      -- 置換
      -- 右辺に `rw [hN0]`
      -- `show` を使って型をはっきりさせると安定
      -- 直接 `rw` してから `exact`
      -- 実行：
      -- 右辺の 0 を置換
      -- Lean の `rw` はゴールに対して使うので、
      -- ゴールを `have` から引き継いで `refine` で出力
      -- 簡潔に：
      -- 「この不等式に右辺の 0 を置換」
      -- 1 行：
      -- 書き換え版を返す
      -- テクニック：`convert` は使わず，`have` を `rw` した後 `exact` で返す
      -- 実装：
      -- まず this を `rw` で変換
      -- ところが `rw` は式に作用させにくいので，
      -- `have T := this;` → `rw [hN0] at T; exact T`
      have T := this
      -- 右辺の 0 を置換
      -- `at` で右辺を書き換える
      -- 不等式での `rw` は両辺の出現に作用するが，ここでは右辺にしか 0 は現れません
      -- 実行：
      rw [hN0] at T
      exact T)

end ThreadC_Fiber

-/



/-
--後ろに同名の定理があるからコメントアウト
lemma NDS2_diff_ge_negDebtSum
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
   - NDS2 V (family V R))
  ≥
  - (∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) )) := by
  classical
  -- 左辺の差分を「fiber ごと」の二重和に展開
  have hPart_R1 :=
    ThreadC_Fiber.NDS2_family_partition_over_fibers
      (V := V) (R := (R1 (V := V) (R := R) (Q := Q)))
      (Q := (promoteToR1 (V := V) (R := R) Q)) --(hV := hV)
  have hPart_R :=
    ThreadC_Fiber.NDS2_family_partition_over_fibers
      (V := V) (R := R) (Q := Q) --(hV := hV)


  -- 以降、B固定での「fiber差」の下界を作る
  -- 便利な略記
  set Q₁ := promoteToR1 (V := V) (R := R) Q
  set f := (Free (Q := Q)).card
  set powF : Int := (2 : Int) ^ f
  set sumFree : Int := ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int)

  -- B ごとに：Δ(B) ≥ −Debt(B)
  have h_point :
    ∀ {B} (hB : B ∈ (Rep (Q := Q)).powerset),
      ( (2 : Int) * (∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int))
           - (V.card : Int) * (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card )
        -
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
           - (V.card : Int) * (fiber V R Q B).card )
      ≥
      - ( ((2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int))
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    intro B hB
    -- R1 側：満キューブの等式（総和 & カード）
    have hR1_sum :
        ∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int)
          = powF * (B.card : Int) + sumFree := by
      -- powF = 2^|Free|
      simp [powF, sumFree]
      show ∑ I ∈ fiber V (contractRules Q.π Q.σ R) Q₁ B, @Nat.cast ℤ instNatCastInt I.card = 2 ^ f * @Nat.cast ℤ instNatCastInt B.card + ∑ I ∈ (Free Q).powerset, @Nat.cast ℤ instNatCastInt I.card
      dsimp [contractRules]
      rw [←sum_card_over_fiber_R1 (V := V) (R := R) (Q := Q) (B := B)]
      exact rfl

    have hR1_card :
        (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card
          = (2 : Nat) ^ f := by
      -- f = |Free|
      simp [f]
      show (fiber V (contractRules Q.π Q.σ R) Q₁ B).card = 2 ^ (Free Q).card
      dsimp [contractRules]
      rw [←fiber_R1_card_eq_two_pow (V := V) (R := R) (Q := Q) (B := B)]
      exact rfl

    -- R 側：粗い上界 ∑|I| ≤ |fiber||B| + ∑_{S⊆Free}|S|
    have hR_sum_le :
        ∑ I ∈ fiber V R Q B, (I.card : Int)
          ≤ ((fiber V R Q B).card : Int) * (B.card : Int) + sumFree := by
      -- C' の sum_card_over_fiber_le を使う
      have := ThreadC_Fiber.sum_card_over_fiber_le (V := V) (R := R) (Q := Q) (B := B)
                  (hB := by
                    -- hB : B ⊆ Rep Q （powerset から）
                    exact Finset.mem_powerset.mp hB)
      -- 右辺の形を sumFree に合わせる
      simpa [sumFree] using this

    -- 目標の形に代入して整理
    -- Δ(B) の下界を作る：R1 側は =，R 側は ≤ を使う
    have :

        ( (2 : Int) * (∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int))
            - (V.card : Int) * (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card )
            -
          ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (fiber V R Q B).card )
        =
        ( (2 : Int) * (powF * (B.card : Int) + sumFree)
            - (V.card : Int) * ((2 : Nat) ^ f) )
          - ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
              - (V.card : Int) * (fiber V R Q B).card ) := by
          -- R1 側に等式を代入
          simp
          simp_all only [Finset.sum_sub_distrib, R1, Rep_promoteToR1, Finset.mem_powerset, Nat.cast_pow, Nat.cast_ofNat, Q₁, powF,f, sumFree]

      -- 右の括弧に R 側の上界を代入（“−(≤ …)” なので “≥ − …”）
    have :
      ( (2 : Int) * (∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int))
          - (V.card : Int) * (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card )
        -
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          - (V.card : Int) * (fiber V R Q B).card )
      ≥
      ( (2 : Int) * (powF * (B.card : Int) + sumFree)
          - (V.card : Int) * ((2 : Nat) ^ f) )
        -
        ( (2 : Int) * ( ((fiber V R Q B).card : Int) * (B.card : Int) + sumFree )
            - (V.card : Int) * (fiber V R Q B).card ) := by
          simp_all only [Finset.sum_sub_distrib, R1, Rep_promoteToR1, Finset.mem_powerset, Nat.cast_pow, Nat.cast_ofNat,
            ge_iff_le, tsub_le_iff_right, Q₁, powF, f, sumFree]
          linarith

      -- 「右側の和」を大きく（= 上から）置換すると差は小さくなるので、≥ が成り立つ
      -- ここは `hR_sum_le` を `mul_le_mul_of_nonneg_left` → 和に流し込む形でもいけますが，
      -- 直接 `linear_arith` 展開を避け、手作業で整理します。
      -- 具体的には、`A - X ≥ A - Y` は `X ≤ Y` と同値。ここで `X` が R 側の元の和，`Y` が上界。
      -- よって `hR_sum_le` を使えば OK。
      --have := hR_sum_le
      -- `X ≤ Y` から `−2*X ≥ −2*Y`，さらに左辺に同じ項を足す操作で完成

    have hneg :
          - (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            ≥ - (2 : Int) * ( ((fiber V R Q B).card : Int) * (B.card : Int) + sumFree ) := by
        -- 係数 2 は非負なので `neg_le_neg` と `mul_le_mul_of_nonneg_left` の合成
        -- ただし Int での単調性は `zsmul` と等価なので、簡単に `linarith?` ではなく `have` で段階化
        have := mul_le_mul_of_nonneg_left this (show (0 : Int) ≤ (2 : Int) by decide)
        -- `a ≤ b` → `-b ≤ -a`
        have := neg_le_neg this
        -- `(-2)*x = -(2*x)` の整理
        simp_all only [Finset.sum_sub_distrib, R1, Rep_promoteToR1, Finset.mem_powerset, Nat.cast_pow, Nat.cast_ofNat,
        ge_iff_le, tsub_le_iff_right, Nat.ofNat_pos, Int.mul_le_mul_left, neg_le_neg_iff, Int.reduceNeg, neg_mul, Q₁, powF,
        f, sumFree]

    simp_all [Q₁, powF, f, sumFree]
    linarith

  -- 以上の点ごとの不等式を powerset 上で総和して完成
  -- 差分＝ ∑(R1 fiber) − ∑(R fiber) → `sum_sub_distrib`，ついで `sum_over_fibers_eq_sum_family`
  have hSum_R1 :
      NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
        = ∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) * (∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int))
              - (V.card : Int) * (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card ) := by
    -- 直前で証明済みの partition 補題（R1 版）
    -- `supportedOn` は使いません（インターフェイスに残してあるだけ）
    exact
      ThreadC_Fiber.NDS2_family_partition_over_fibers
        (V := V) (R := (R1 (V := V) (R := R) (Q := Q)))
        (Q := Q₁)

  have hSum_R :
      NDS2 V (family V R)
        = ∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
              - (V.card : Int) * (fiber V R Q B).card ) := by
    exact ThreadC_Fiber.NDS2_family_partition_over_fibers (V := V) (R := R) (Q := Q)

  -- 差分を総和の差にし，点ごとの下界を合算

  have hDiff_ge :
      (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
       - NDS2 V (family V R))
      ≥
      ∑ B ∈ (Rep (Q := Q)).powerset,
        - ( ((2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int))
              * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    -- 差分を展開
    simp [hSum_R1, hSum_R, Finset.sum_sub_distrib]
    -- あとは `sum_le_sum` で点ごとの不等式を合計
    sorry
    /-
    apply
      @Finset.sum_le_sum (ι := Finset α) (N := Int)
        _ _  -- typeclass は推論に任せる
        (f := fun B => ( (2 : Int) * (∑ I ∈ fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B, (I.card : Int))
              - (V.card : Int) * (fiber V (R1 (V := V) (R := R) (Q := Q)) Q₁ B).card )
            -
            ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
              - (V.card : Int) * (fiber V R Q B).card ) )
        (g := fun B => - ( ((2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int))
              * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) )
        (s := (Rep (Q := Q)).powerset)
  -/
/--/
  simp_all only [Finset.sum_sub_distrib, R1, Rep_promoteToR1, Finset.mem_powerset, ge_iff_le, neg_le_sub_iff_le_add,
    tsub_le_iff_right, Finset.sum_neg_distrib, Q₁, powF, f]
-/


/- ★ ここがあなたのゴールに対応する総和の不等式。`nonemp` は
    既に通してある `fiber_nds2_le_rep_term_with_debt` を使うために仮定しています。 -/
--メインのスレッドから証明しろといわれた定理
/- 別のところで完成したのでコメントアウト
lemma sum_main_le_NDS2_contract_plus_debts
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R)
  (nonemp : (Free (Q := Q)).Nonempty) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      (2 : Int) * ∑ I ∈ fiber V R Q B, (I.card : Int)
    ≤
  NDS2 V (family V (contractRules Q.π Q.σ R))
    + ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
    + ∑ B ∈ (Rep (Q := Q)).powerset,
        (V.card : Int) * ((fiber V R Q B).card : Int) := by
  classical
  -- インデックス集合
  set S := (Rep (Q := Q)).powerset

  -- 3つの成分に分けた右辺の被積分関数
  let g1 : Finset α → Int :=
  fun B =>
    (2 : Int) ^ (Free (Q := Q)).card
      * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)

  -- Debt と |V|*|fiber| はそのまま
  let g2 : Finset α → Int :=
    fun B =>
      ((2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int))
        * ((V.card : Int) - (2 : Int) * (B.card : Int))

  let g3 : Finset α → Int :=
    fun B => (V.card : Int) * ((fiber V R Q B).card : Int)

  -- 左辺の被積分関数
  let f : Finset α → Int :=
    fun B => (2 : Int) * ∑ I ∈ fiber V R Q B, (I.card : Int)

  -- ★ 点ごとの不等式 f ≤ g1 + g2 + g3
  have h_each :
    ∀ B ∈ S, f B ≤ g1 B + g2 B + g3 B := by
    intro B hB
    have hBsub : B ⊆ Rep (Q := Q) := Finset.mem_powerset.mp hB
    -- 既証：with-debt 版（各 B に対して）
    have h :=
      ThreadC_Fiber.fiber_nds2_le_rep_term_with_debt (V := V) (R := R) (Q := Q)
        (B := B) (hB := hBsub) (nonemp := nonemp)
    -- h : 2*∑|I| - |V|*|fiber| ≤ 2^|Free|*(2|B|-|Rep|) + (2^|Free| - |fiber|)*(|V|-2|B|)
    -- 両辺に |V|*|fiber| を加えて所望の形へ
    -- すでに持っている with-debt の個別不等式
    -- h : 2*∑|I| - |V|*|fiber| ≤ 2^|Free|*(2|B|-|Rep|) + Debt + |V|*|fiber|
    -- 両辺に |V|*|fiber| を足す
    have h' :
      (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        ≤
      (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
        + (( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
        + (V.card : Int) * ((fiber V R Q B).card : Int) := by
      have := ThreadC_Fiber.fiber_nds2_le_rep_term_with_debt
                  (V := V) (R := R) (Q := Q)
                  (B := B) (hB := Finset.mem_powerset.mp hB) (nonemp := nonemp)
      -- |V|*|fiber| を両辺に加える
      have := add_le_add_right this ((V.card : Int) * ((fiber V R Q B).card : Int))
      -- 形をそろえる（`f, g1, g2, g3` を `rfl` で開けるだけ）
      -- "simpa using" の代わりに、`rw` で左右を書き換えてから `exact`
      -- 左辺 = f B
      have hL :
        (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          = f B := rfl
      -- 右辺 = g1 B + g2 B + g3 B
      have hR :
        (2 : Int) ^ (Free (Q := Q)).card * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
          + (( (2 : Int) ^ (Free (Q := Q)).card - ((fiber V R Q B).card : Int) )
              * ( (V.card : Int) - (2 : Int) * (B.card : Int) ))
          + (V.card : Int) * ((fiber V R Q B).card : Int)
          = g1 B + g2 B + g3 B := rfl
      -- 書き換えて終了
      -- （`rw` は左右どちらの等式からでも OK。
      --   ここでは「この不等式を欲しい形にリライトしてから `exact`」）
      -- 注意: `rw [hL]` は「左辺を f B に置換」します
      --       `rw [hR]` は「右辺を g1+g2+g3 に置換」します
      -- 置換の順序は自由
      have H := this
      rw [hL] at H
      exact Int.le_add_of_sub_right_le h
    -- g1 の第一項（R1の主項）に置換：2^|Free|*(2|B|-|Rep|) の和は NDS2(contractRules) の fiber 版総和
    -- 点ごとでは g1 をそのまま使い、最後に総和で NDS2 に変換します。
    -- ここでは f ≤ (主項) + debt + |V|*|fiber| を示せば十分
    -- g1 の最初の括弧を「主項」として使うため、点ごとでは ≤ (主項) + debt + |V|*|fiber|
    -- として受け入れます（総和後に g1 の定義へ差し替え）。
    -- したがって h' で十分。
    simp_all only [Finset.mem_powerset, Nat.cast_ofNat, tsub_le_iff_right, S, f, g1, g2, g3]

  -- ∑ f ≤ ∑ (g1 + g2 + g3)
  have h_sum_le :
      ∑ B ∈ S, f B
        ≤ ∑ B ∈ S, (g1 B + g2 B + g3 B) := by
    -- ★ ここで @Finset.sum_le_sum を使う
    apply
      @Finset.sum_le_sum (ι := Finset α) (N := Int)
        _ _  -- typeclass は推論に任せる
        (f := f) (g := fun B => g1 B + g2 B + g3 B) (s := S)
    simp_all only [Finset.mem_powerset, S, f, g1, g2, g3]
    exact Int.instIsOrderedAddMonoid
    exact fun i a => h_each i a

  -- 右辺の和を 3 つに分配
  have h_split :
      ∑ B ∈ S, (g1 B + g2 B + g3 B)
        = (∑ B ∈ S, g1 B) + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
    -- ∑ (a+b+c) = ∑ a + ∑ b + ∑ c
    -- まず a+(b+c) にし、sum_add_distrib を2回
    have : ∑ B ∈ S, (g1 B + (g2 B + g3 B))
            = (∑ B ∈ S, g1 B) + ∑ B ∈ S, (g2 B + g3 B) := by
      simp [Finset.sum_add_distrib]
    -- 次に ∑ (g2+g3) を分解
    have : (∑ B ∈ S, g1 B) + ∑ B ∈ S, (g2 B + g3 B)
            = (∑ B ∈ S, g1 B) + (∑ B ∈ S, g2 B) + (∑ B ∈ S, g3 B) := by
      simp [Finset.sum_add_distrib, add_assoc]
    -- 仕上げ：左辺の形を合わせる
    -- (g1 + g2 + g3) = g1 + (g2 + g3)
    -- これを使って 2 段階を連結
    -- 1 行で：
    simp_all [S, f, g1, g2, g3]
    symm
    simp only [Finset.sum_add_distrib]

  -- ∑ g1 を NDS2 (contractRules) に置換（fiber分割の等式）
  have hg1_zero :
    ∑ B ∈ S, g1 B = 0 := by
    -- ∑ g1 = 2^|Free| * ∑ (2|B| - |Rep|)
    have pull :
      ∑ B ∈ S, g1 B
        = (2 : Int) ^ (Free (Q := Q)).card
            * ∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
      -- 係数を外へ出す向きの等式を作る（"simpa" 禁止なので `calc`/`simp` で）
      calc
        ∑ B ∈ S, g1 B
            = ∑ B ∈ S,
                ( (2 : Int) ^ (Free (Q := Q)).card
                    * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) ) := by
                  -- g1 の定義を開く
                  simp_all only [Finset.mem_powerset, S, f, g1, g2, g3]

        _ = (2 : Int) ^ (Free (Q := Q)).card
                * ∑ B ∈ S,
                    ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) := by
              -- `∑ a*b = a * ∑ b`（a は定数）
              -- `simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]`
              -- "simpa using" 禁止なので `simp` だけで書き換え
              -- 1 行：
              simp [mul_comm]
              rw [mul_comm]
              sorry

    -- main: ∑ (2|B| - |Rep|) = 0 は既にある補題
    have h0 := ThreadC_Fiber.sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
    -- 連結
    -- `rw [pull, h0]; simp`
    -- "simpa using" を避け `rw` と `simp` を分ける
    -- 1 行目：
    rw [pull] ; rw [h0] ; simp


  dsimp [g1] at hg1_zero
  sorry
  --rw [hg1_zero]
  --rw [h_split]
-/
