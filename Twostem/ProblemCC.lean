import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Int
import Twostem.General
import Twostem.Basic
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

instance decidableFinsetEq : DecidableEq (Finset α) :=
  inferInstance

instance decidableFinsetFinset : DecidableEq (Finset (Finset α)) :=
  inferInstance

namespace ThreadC_Fiber

/- ルールは `(親, 親, 子)` -/
--abbrev Rule (α) := α × α × α

/- `I` が `R`-閉：すべての `(a,b,r) ∈ R` で `a ∈ I ∧ b ∈ I → r ∈ I` -/
--def isClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
--  ∀ t ∈ R, (t.1 ∈ I ∧ t.2.1 ∈ I) → t.2.2 ∈ I

/- Provide decidable instance for isClosed using classical reasoning -/
--noncomputable instance isClosedDecidable (R : Finset (Rule α)) (I : Finset α) : Decidable (isClosed R I) := by
--  classical infer_instance

/- 閉包族：`V` の冪集合を `isClosed R` でフィルタ -/
--noncomputable def family (V : Finset α) (R : Finset (Rule α)) : Finset (Finset α) := by
--  classical
--  exact V.powerset.filter (fun I => isClosed R I)

/- NDS₂ 便利定義：`∑ (2|I| - |V|)` -/
--def NDS2 (V : Finset α) (F : Finset (Finset α)) : Int :=
--  ∑ I ∈ F, ((2 : Int) * (I.card : Int) - (V.card : Int))

/- SCC 商（最小限情報） -/



/-! ## (1) 定数和（Int 版） -/
lemma sum_const_int {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (c : Int) :
  ∑ _ ∈ s, c = (s.card : Int) * c := by
  classical
  calc
    ∑ i ∈ s, c = ∑ i ∈ s, c := rfl
    _ = (s.card : Nat) • c := by
          -- `∑ const = card • const`
          simp [Finset.sum_const]
    _ = (s.card : Int) * c := by
          -- `n • a = (n:Int) * a` for `Int`
          exact rfl

/-! ## (2) 画像への書き換え（`sum_image` 版） -/
lemma sum_image_diff_card
  (A : Finset (Finset α)) (B : Finset α)
  (hInj :
    ∀ {I} (_ : I ∈ A) {J} (_ : J ∈ A),
      I \ B = J \ B → I = J) :
  ∑ I ∈ A, ((I \ B).card : Int)
    = ∑ S ∈ A.image (fun I : Finset α => I \ B), (S.card : Int) := by
  classical
  -- `sum_image` は「像の和 = 元集合の像を取った和」
  -- 目標はその対称形なので `Eq.symm` で向きを揃える

  have h :=  @Finset.sum_image _ _ Int _ (fun S : Finset α => (S.card : Int)) _ A
      (fun I : Finset α => (I \ B))
      (by
        intro x hx y hy hxy
        exact hInj hx hy hxy)
  -- h : ∑ S ∈ A.image f, g S = ∑ I ∈ A, g (f I)
  -- 目標は左右を入れ替えた等式
  exact Eq.symm h

/-! ## (3) 包含で和が増える（Int 版・非負性） -/
lemma sum_le_sum_of_subset_of_nonneg_int
  {β : Type*} [DecidableEq β]
  {s t : Finset β} (hsub : s ⊆ t)
  (f : β → Int) (h0 : ∀ x ∈ t, 0 ≤ f x) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  classical
  -- 既存補題をそのまま使う（`∈` と `in` は記法の違いで同じ）
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      hsub
      (by
        intro x hx
        exact fun a => h0 x hx
      )




/-! ### A 系：分解・単射・粗い上界 -/

section A_block
variable {V R} {Q : SCCQuot α V R}

lemma rep_subset_V : Rep (Q := Q) ⊆ V := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hxV, hrep⟩
  cases hrep
  exact Q.σ_in_V (Q.π x)

lemma fiber_mem_family {B I : Finset α}
  (hI : I ∈ fiber V R Q B) :
  I ∈ family V R := (Finset.mem_filter.mp hI).1

lemma fiber_trace_eq {B I : Finset α}
  (hI : I ∈ fiber V R Q B) :
  I ∩ Rep (Q := Q) = B := (Finset.mem_filter.mp hI).2

omit [DecidableEq α] in
lemma mem_family_sub_V {I : Finset α}
  (hI : I ∈ family V R) : I ⊆ V := by
  have h := (Finset.mem_filter.mp hI).1
  exact (Finset.mem_powerset.mp h)

lemma B_subset_of_fiber {B I : Finset α}
  (hI : I ∈ fiber V R Q B) :
  B ⊆ I := by
  intro x hxB
  have htrace := fiber_trace_eq (Q := Q) (B := B) (I := I) hI
  have hx : x ∈ I ∩ Rep (Q := Q) := by
    -- x ∈ B = I ∩ Rep
    have : x ∈ B := hxB
    simpa [htrace] using this
  exact (Finset.mem_inter.mp hx).1

/-- **A1（分解）**：`I = B ∪ (I \ B)` かつ `I \ B ⊆ Free` -/
lemma fiber_split
  {B I : Finset α} (hB : B ⊆ Rep (Q := Q)) (hI : I ∈ fiber V R Q B) :
  (I \ B) ⊆ Free (Q := Q) ∧ B ∪ (I \ B) = I := by
  classical
  have hI_family : I ∈ family V R := fiber_mem_family (Q := Q) hI
  have hI_subV : I ⊆ V := mem_family_sub_V (V := V) (R := R) hI_family
  have htrace : I ∩ Rep (Q := Q) = B := fiber_trace_eq (Q := Q) (B := B) (I := I) hI
  constructor
  · intro x hx
    have hxI : x ∈ I := (Finset.mem_sdiff.mp hx).1
    have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    have hxV : x ∈ V := hI_subV hxI
    have hxnotRep : x ∉ Rep (Q := Q) := by
      intro hxRep
      have hxIR : x ∈ I ∩ Rep (Q := Q) := by
        exact Finset.mem_inter.mpr ⟨hxI, hxRep⟩
      have : x ∈ B := by simpa [htrace] using hxIR
      exact hxnotB this
    exact Finset.mem_sdiff.mpr ⟨hxV, hxnotRep⟩
  · simp
    subst htrace
    simp_all only [Finset.inter_subset_right, Finset.inter_subset_left]

/-! ## (5) `image (I ↦ I \ B)` が `powerset Free` に入る -/
lemma image_diff_subset_powerset_free
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α} (hB : B ⊆ Rep (Q := Q)) :
  (fiber V R Q B).image (fun I : Finset α => I \ B)
    ⊆ (Free (Q := Q)).powerset := by
  classical
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨I, hIf, rfl⟩
  rw [Finset.mem_powerset]

  obtain ⟨hSsub, _hUnion⟩ :=
    fiber_split (Q := Q) (V := V) (R := R) (B := B) (I := I) hB hIf

  exact hSsub

/-- **A2（単射）**：`I ↦ I \ B` は fiber 上で単射 -/
lemma fiber_inj_on_diff
  {B : Finset α} (hB : B ⊆ Rep (Q := Q)) :
  ∀ {I} (_ : I ∈ fiber V R Q B) {J} (_ : J ∈ fiber V R Q B),
    I \ B = J \ B → I = J := by
  classical
  intro I hI J hJ hEq
  obtain ⟨_, hUI⟩ := fiber_split (Q := Q) (B := B) (I := I) hB hI
  obtain ⟨_, hUJ⟩ := fiber_split (Q := Q) (B := B) (I := J) hB hJ
  -- I = B ∪ (I\B) = B ∪ (J\B) = J
  have : B ∪ (I \ B) = B ∪ (J \ B) := by
    rw [hEq]
  have h1 : B ∪ (I \ B) = I := by
    exact hUI
  have h2 : B ∪ (J \ B) = J := by
    exact hUJ
  -- 変形
  have : I = J := by
    have := congrArg id (show B ∪ (I \ B) = B ∪ (J \ B) from this)
    -- 直前の等式を使って I, J に書き換え
    -- （`rw` で両辺を I, J に）
    have hL : B ∪ (I \ B) = I := h1
    have hR : B ∪ (J \ B) = J := h2
    -- `this : B ∪ (I\B) = B ∪ (J\B)` に対し，左を hL，右を hR に書き換える
    have : I = J := by
      -- `rw [hL]` は左辺に、`rw [hR]` は右辺に適用
      -- 簡単にするため calc を使う
      have : B ∪ (I \ B) = J := by
        -- 右辺だけ書き換え
        -- いったん等式 `B ∪ (I\B) = B ∪ (J\B)` を使ってから `= J`
        exact Eq.trans this hR
      -- さらに左辺を I に
      exact Eq.trans (Eq.symm hL) this
    exact this
  exact this

/-- **A2'（カード上界）**：`|fiber| ≤ 2^{|Free|}` -/
lemma fiber_card_le_two_pow
  {B : Finset α} (hB : B ⊆ Rep (Q := Q)) :
  (fiber V R Q B).card ≤ (2 : Nat) ^ (Free (Q := Q)).card := by
  classical
  set A := fiber V R Q B
  set f : Finset α → Finset α := fun I => I \ B
  have h_inj :
    ∀ {x} (hx : x ∈ A) {y} (hy : y ∈ A),
      f x = f y → x = y :=
    fun hx hy h => fiber_inj_on_diff (Q := Q) (V := V) (R := R) (B := B) hB hx (by exact h)


  have himg_sub : A.image f ⊆ (Free (Q := Q)).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨I, hIA, rfl⟩
    obtain ⟨hSsub, _⟩ := fiber_split (Q := Q) (B := B) (I := I) hB hIA
    exact Finset.mem_powerset.mpr hSsub
  -- `card (A.image f) = card A` （sum_imageを1で使う）
  have h_card_img_eq : (A.image f).card = A.card := by
    have hsum := (A.image f).card
      --Finset.sum_image (s := A) (f := f) (g := fun (_ : Finset α) => (1 : Nat))
      --  (fun x hx y hy hxy => fiber_inj_on_diff (Q := Q) (V := V) (R := R) (B := B) hB hx hy hxy)
    · -- 両辺を card に直す
      -- 左辺：card (A.image f) = ∑_{S∈image} 1
      -- 右辺：card A          = ∑_{I∈A} 1
      have hL : (A.image f).card = ∑ _S ∈ A.image f, (1 : Nat) := by
        -- card_eq_sum_ones は `Nat` 版は `by` で書く
        -- 既知：`Finset.card_eq_sum_ones` は `Nat` で `simp` できる
        -- ここでは素直に書く
        -- （`by` で `simp` 可能：`by simpa using (Finset.card_eq_sum_ones _)` だが「simpa using」禁止のため直接）
        -- 簡潔に `by` 内 `simp` を使う
        simp_all only [Finset.sum_const, smul_eq_mul, mul_one, A, f]

      have hR : A.card = ∑ _I ∈ A, (1 : Nat) := by
        simp_all only [Finset.sum_const, smul_eq_mul, mul_one, A, f]
      -- 置換して等式にする
      -- sum_image の等式を流用
      -- （`rw` を2回）
      have := hsum
      -- 左右を書き換え
      -- 先に左辺
      have : ∑ _S ∈ A.image f, (1 : Nat) = ∑ _I ∈ A, (1 : Nat) := by
        rw [←hL, hR.symm]
        simp_all only [Finset.sum_const, smul_eq_mul, mul_one, A, f]
        rw [Finset.card_image_of_injOn]
        dsimp [Set.InjOn]
        intro x₁ a x₂ a_1 a_2
        simp_all only [Finset.mem_coe]
        exact h_inj a a_1 a_2

      -- card 等式へ
      exact by
        -- いったん目標の形に整える
        -- from hL,hR とこの等式から
        -- (A.image f).card = A.card
        -- を示す
        -- 直接 `calc` でつなぐ
        calc
          (A.image f).card = ∑ _S ∈ A.image f, (1 : Nat) := by exact hL
          _ = ∑ _I ∈ A, (1 : Nat) := by exact this
          _ = A.card := by exact hR.symm

  -- あとは包含からカード比較
  have hcard_le : (A.image f).card ≤ ((Free (Q := Q)).powerset).card := by
    exact Finset.card_le_card himg_sub

  -- 2^{|Free|}
  have hpow : ((Free (Q := Q)).powerset).card = (2 : Nat) ^ (Free (Q := Q)).card :=
    Finset.card_powerset _
  -- まとめ
  calc
    A.card = (A.image f).card := by exact h_card_img_eq.symm
    _ ≤ ((Free (Q := Q)).powerset).card := hcard_le
    _ = (2 : Nat) ^ (Free (Q := Q)).card := hpow

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

/-- **A3（和の粗い上界）**：
`∑ I∈fiber |I| ≤ |fiber||B| + ∑_{S⊆Free} |S|` （Int 版）
-/
lemma sum_card_over_fiber_le
  {B : Finset α} (hB : B ⊆ Rep (Q := Q)) :
  ∑ I ∈ fiber V R Q B, (I.card : Int)
    ≤ ((fiber V R Q B).card : Int) * (B.card : Int)
      + (∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int)) := by
  classical
  set A := fiber V R Q B
  -- 点ごとの上界：|I| ≤ |B| + |I\B|
  have h_point :
    ∀ {I} (hI : I ∈ A), (I.card : Int) ≤ (B.card : Int) + ((I \ B).card : Int) := by
    intro I hI
    obtain ⟨_, hU⟩ := fiber_split (Q := Q) (B := B) (I := I) hB hI
    -- |I| = |B ∪ (I\B)| ≤ |B| + |I\B|
    have h₁ : I.card ≤ (B ∪ (I \ B)).card := by
      -- 等式 `I = B ∪ (I\B)` から ≤ は自明
      -- ここは `rw [hU]` と `exact le_of_eq rfl` でよい
      have : I = B ∪ (I \ B) := by exact hU.symm
      -- 置換
      have : I.card = (B ∪ (I \ B)).card := by
        -- `rw` のみで
        rw [this]
        simp

      -- `≤` へ
      exact le_of_eq this
    have h₂ : (B ∪ (I \ B)).card ≤ B.card + (I \ B).card :=
      Finset.card_union_le _ _
    have : (I.card : Int) ≤ ((B ∪ (I \ B)).card : Int) := by
      exact_mod_cast h₁
    have : (I.card : Int) ≤ (B.card : Int) + ((I \ B).card : Int) := by
      exact le_trans this (by exact_mod_cast h₂)
    exact this
  -- 合計へ
  have h_sum1 :
    ∑ I ∈ A, (I.card : Int)
      ≤ ∑ I ∈ A, ( (B.card : Int) + ((I \ B).card : Int) ) := by

    exact finset_sum_le_finset_sum (fun I hI => h_point hI)
  /-
  -- 定数の和を分離
  have h_sum2 :
    ∑ I ∈ A, ( (B.card : Int) + ((I \ B).card : Int) )
      = ((A.card : Nat) : Int) * (B.card : Int)
        + ∑ I ∈ A, ((I \ B).card : Int) := by
    -- 分配
    have : (∑ I ∈ A, (B.card : Int))
            = ((A.card : Nat) : Int) * (B.card : Int) := by
      -- `sum_const`（Int 版）
      -- `Finset.sum_const` は `Semiring` で使える。Intは可換環。
      -- `Nat` の card を Int にキャストする必要あり。
      -- ここは既存の等式を `by` で示す。
      -- `∑ 1 = card` を使ってからスカラー倍。
      have : ∑ _I ∈ A, (1 : Int) = (A.card : Nat) := by
        -- `by` で `simp` 可能
        -- `by` の中で `simp` はOK（「simpa using」は使わない）
        -- `Finset.card_eq_sum_ones` の Int 版は `(1:Int)` で同様に効く
        -- より直に：`by` で `simp [Finset.card_eq_sum_ones]` でもよい
        -- ただし安全のため：
        -- 変換：`∑ _∈A, (1:Int)` は `((A.card : Nat))`
        have : ∑ _I ∈ A, (1 : Int) = (A.card : Nat) := by
          -- `by` の中 `simp`：
          simp_all only [Finset.sum_const, Int.nsmul_eq_mul, mul_one, A]

        exact this
      -- 上式を `B.card` 倍
      calc
        ∑ I ∈ A, (B.card : Int)
            = (B.card : Int) * ∑ _I ∈ A, (1 : Int) := by
                -- 和の定数因子は「定数×個数」
                -- ここは `by` で `simp`：`sum_const` を使うより展開派
                -- 直接：`by` で `simp` のほうが短い
                simp
                exact Int.mul_comm ↑A.card ↑B.card
        _ = (B.card : Int) * (A.card : Nat) := by
                -- 直前の `have` を使う
                -- `by` に `rw` で代入
                -- ただ整数×自然の並びを Int に
                -- `(A.card : Nat)` は Nat、式は Int×Int が欲しいので、実際上は
                -- 上の等式が `= (A.card : Int)` になっている必要がある
                -- すでに `(A.card : Nat)` と書いたので、整合のため `(A.card : Int)` に直す
                -- 書き直し
                -- 差分回避のため、上の等式を `= (A.card : Int)` にしておくほうがよかったが、
                -- ここで手直しする：
                -- 置換：`(A.card : Nat)` を `(A.card : Int)` に
                -- これは成立しないので、前の `have` を最初から `= (A.card : Int)` に取るべきだった。
                -- 仕切り直し。
                admit
      -- 上の admit は、`∑ _∈A, (1:Int) = (A.card : Int)` と取っておけば消せます。
      -- 書き直します。
      admit
    -- いったん上のブロックをやり直す（簡潔版）
    -- 最初からやり直し：
    -- `simp` で十分に分配と和の定数化ができます。
    -- ここから別解で示します：
    -- （この `have h_sum2` 全体を書き直すほうが簡単）
    admit
  -- 画像へ移して上から抑える
  -/
  have h_inj :
    ∀ {x} (hx : x ∈ A) {y} (hy : y ∈ A),
      (x \ B) = (y \ B) → x = y := by
      intro hx hy h
      apply fiber_inj_on_diff (Q := Q) (V := V) (R := R) (B := B) hB
      exact hy

  have h_sum_image :
    ∑ I ∈ A, ((I \ B).card : Int)
      = ∑ S ∈ A.image (fun I : Finset α => I \ B), (S.card : Int) := by
    -- `sum_image`（Int 版）
    simp_all only [A]
    rw [Finset.sum_image]
    dsimp [Set.InjOn]
    intro x₁ a x₂ a_1 a_2
    simp_all only [Finset.mem_coe]
    exact h_inj a a_1 a_2

  have himg_sub :
    A.image (fun I : Finset α => I \ B) ⊆ (Free (Q := Q)).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨I, hIA, rfl⟩
    obtain ⟨hSsub, _⟩ := fiber_split (Q := Q) (B := B) (I := I) hB hIA
    exact Finset.mem_powerset.mpr hSsub
  have h_nonneg :
    ∀ ⦃S⦄, S ∈ (Free (Q := Q)).powerset → (0 : Int) ≤ (S.card : Int) := by
    intro S hS
    exact_mod_cast (Nat.zero_le _)
  have h_sum_img_le :
    ∑ S ∈ A.image (fun I : Finset α => I \ B), (S.card : Int)
      ≤ ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := by
  -- 部分集合関係を使って証明
    let s := A.image (fun I : Finset α => I \ B)
    let t := (Free (Q := Q)).powerset

    -- s ⊆ t なので、t の和は s の和と (t \ s) の和に分解できる
    have h_subset : s ⊆ t := himg_sub
    rw [← Finset.sum_sdiff h_subset]

    -- (t \ s) の和が非負であることを示す
    have h_nonneg_diff : 0 ≤ ∑ S ∈ t \ s, (S.card : Int) :=
      Finset.sum_nonneg (fun S hS => Int.natCast_nonneg S.card)


    -- 全体の和 = s の和 + (t \ s) の和 ≥ s の和
    simp_all only [Finset.mem_powerset, Int.ofNat_zero_le,implies_true, Finset.sum_sdiff_eq_sub, Int.sub_nonneg, sub_add_cancel, A, s, t]

  have h_sum_img_le :
    ∑ S ∈ A.image (fun I : Finset α => I \ B), (S.card : Int)
      ≤ ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := by
  -- 自然数での和の不等式をまず示す
    have h_sum_nat_le :
        (∑ S ∈ A.image (fun I : Finset α => I \ B), S.card : ℕ) ≤
        ∑ S ∈ (Free (Q := Q)).powerset, S.card := by

      --let fs := finset_sum_le_finset_sum (fun i hi => h_nonneg hi)
      exact Finset.sum_le_sum_of_ne_zero fun x a a_1 => himg_sub a

    exact_mod_cast h_sum_nat_le
    --Finset.sum_le_sum_of_subset_of_nonneg himg_sub h_nonneg  -- まとめ

  have h_sum_bound :
    ∑ I ∈ A, ((I \ B).card : Int)
      ≤ ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := by
    -- `rw` で画像和に書き換え、包含で上から抑える
    have := h_sum_image
    -- `this : ∑ I∈A, ... = ∑ S∈image, ...`
    -- 右辺で ≤ powerset 和
    -- `calc` でつなぐ
    calc
      ∑ I ∈ A, ((I \ B).card : Int)
          = ∑ S ∈ A.image (fun I : Finset α => I \ B), (S.card : Int) := this
      _ ≤ ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := h_sum_img_le
  -- 目的式へ
  -- `h_sum1` と `h_sum2`（定数分離）、`h_sum_bound` を合成
  -- 上で `h_sum2` を `admit` にしてしまったので、簡潔な別証を与える：
  -- 「定数和の分離」は `sum_add_distrib` と `sum_const_nat`/`sum_const` を使えば一行です。
  -- 再構築：
  have h_separate :
    ∑ I ∈ A, ((B.card : Int) + ((I \ B).card : Int))
      = (A.card : Int) * (B.card : Int)
        + ∑ I ∈ A, ((I \ B).card : Int) := by
    classical
    calc
      _ = (∑ I ∈ A, (B.card : Int)) + (∑ I ∈ A, ((I \ B).card : Int)) := by
            simp [Finset.sum_add_distrib]
      _ = (A.card : Int) * (B.card : Int)
            + ∑ I ∈ A, ((I \ B).card : Int) := by
            -- ここで (1) を適用
            have := ThreadC_Fiber.sum_const_int (s := A) (c := (B.card : Int))
            -- `∑ I ∈ A, (B.card:Int) = (A.card:Int) * (B.card:Int)`
            -- `rw` で代入
            simp_all only [ Finset.mem_powerset, Int.ofNat_zero_le,implies_true, Finset.sum_const, Int.nsmul_eq_mul, A]

  -- 最後の合成
  calc
    ∑ I ∈ A, (I.card : Int)
      ≤ ∑ I ∈ A, ((B.card : Int) + ((I \ B).card : Int)) := h_sum1
    _ = ((A.card : Nat) : Int) * (B.card : Int)
          + ∑ I ∈ A, ((I \ B).card : Int) := h_separate
    _ ≤ ((A.card : Nat) : Int) * (B.card : Int)
          + ∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int) := by
            have := h_sum_bound
            exact add_le_add_left this _
end A_block

/--（参考）`|V| = |Rep| + |Free|`（Int 版） -/
lemma cardV_as_Rep_plus_Free {V : Finset α} {R : Finset (Rule α)} {Q : SCCQuot α V R} :
  (V.card : Int) = (Rep (Q := Q)).card + (Free (Q := Q)).card := by
  classical
  have hsub : Rep (Q := Q) ⊆ V := rep_subset_V (Q := Q) (V := V)
  have hNat :
    (V \ Rep (Q := Q)).card = V.card - (Rep (Q := Q)).card :=
    Finset.card_sdiff hsub
  have : (V.card : Int) - (Rep (Q := Q)).card = (Free (Q := Q)).card := by
    -- `Free = V \ Rep`
    change (V.card : Int) - (Rep (Q := Q)).card = ((V \ Rep (Q := Q)).card : Nat)
    -- `hNat` を Int へ
    rw [Finset.card_sdiff hsub]
    norm_cast
    have : V.card >= (Rep (Q := Q)).card := by
      exact Finset.card_le_card hsub
    simp_all only [ge_iff_le, Nat.cast_sub]
    rw [Int.subNatNat_eq_coe]

  -- `a - b = c` から `a = b + c`
  have := sub_eq_iff_eq_add.mp this
  (expose_names; exact Int.sub_eq_iff_eq_add'.mp this_1)

omit [DecidableEq α] in
lemma sum_card_powerset_int (S : Finset α):-- (nonempty : S.Nonempty) :
  ∑ T ∈ S.powerset, (T.card : Int)
    = (2 : Int) ^ (S.card - 1) * (S.card : Int) := by
  classical
  by_cases hS : S.card = 0
  · -- S = ∅ の場合
    simp_all only [Finset.card_eq_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.cast_zero,
    zero_tsub, pow_zero, mul_zero]
  · -- S ≠ ∅ の場合

  -- powerset 上の「サイズだけに依存する」総和を階数別（card = k）に並べ替える
  --   ∑_{T⊆S} (|T| : ℤ)
  -- = ∑_{k=0..|S|} (|S| choose k) • (k : ℤ)
    have h₁ :
        ∑ T ∈ S.powerset, (T.card : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) • (k : Int) := by

      simpa using
        (Finset.sum_powerset_apply_card
          (α := Int) (f := fun k => (k : Int)) (x := S))

    -- `•`（nsmul）を通常の積に直す
    have h₂ :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) • (k : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) * (k : Int) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp

    -- 二項係数の恒等式：
    --   ∑_{k=0..n} k * (n choose k) = n * 2^{n-1}
    -- を ℤ へキャストして適用
    have h₃ :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) * (k : Int)
          =
        ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int) := by
      -- `range (n+1)` を `0` と `range n` に分解し、k ↦ k.succ で付け替え
      have hk0 :
        (S.card.choose 0 : Int) * (0 : Int) = 0 := by simp
      -- 分解
      have :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) * (k : Int)
        =
        (S.card.choose 0 : Int) * (0 : Int)
        + ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int) := by
        -- `range_succ` で末尾を分解 → 先頭の k=0 を取り出し、残りは k.succ で表す
        -- ここは等式を書いてから両辺を `simp` で整える
        -- 左辺
        have : Finset.range (S.card + 1)
                = insert 0 ((Finset.range S.card).map ⟨Nat.succ, Nat.succ_injective⟩) := by
          -- 標準事実： {0,1,...,n} = {0} ∪ {1,...,n}、後者は succ の像
          -- mathlib 既存の性質を `ext`/`simp` で示す
          apply Finset.ext
          intro k
          constructor <;> intro hk
          · by_cases hk0' : k = 0
            · subst hk0'; simp
            · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0'
              have hklt : k ≤ S.card := by
                -- `k ∈ range (n+1)` → `k < n+1`
                simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Finset.mem_range]
                omega
              rcases Nat.exists_eq_succ_of_ne_zero hk0' with ⟨j, rfl⟩
              simp [Finset.mem_range]
              exact hklt
          · -- 逆向き：画像にあれば range (n+1) に入る
            simp [Finset.mem_range] at hk
            rcases hk with hk | ⟨j, hj, rfl⟩
            · subst hk
              simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Finset.mem_range, lt_add_iff_pos_left,
                  add_pos_iff, Finset.card_pos, zero_lt_one, or_true]
            · have : j.succ < S.card + 1 := Nat.succ_lt_succ hj
              simpa [Finset.mem_range] using this
        -- これで右辺の形が得られる
        -- `sum` を `insert` と `map` に分解（0 は像に含まれないので `sum_insert` 可）
        -- ただしこの詳細展開は長くなるので、ここでは等式として採用
        -- 実務上は既存の reindex 補題 (`sum_bij`) で同値変換できる
        -- ここでは完成形だけ用いる
        -- （必要なら、この等式の証明を補題として別途立てる）
        simp_all only [Int.zsmul_eq_mul, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one,
          Nat.add_eq_zero, one_ne_zero, and_false, exists_const, not_false_eq_true, Finset.sum_insert, Nat.choose_zero_right,
          Nat.cast_one, Nat.cast_zero, mul_zero, Finset.sum_map, Nat.cast_add, zero_add]
          -- k=0項を消して完成
      simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Nat.succ_eq_add_one, Nat.cast_add,
      zero_add]

    -- 3b) 各項を書き換え： `(k+1) * C(n, k+1) = n * C(n-1, k)`
    have h₄ :
        ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int)
          =
        (S.card : Int) *
          ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int) := by
      rw [@Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      -- 自然数等式 `(k+1) * choose n (k+1) = n * choose (n-1) k`
      have hnat :
          (k.succ) * S.card.choose k.succ
            = S.card * (S.card - 1).choose k := by

        let nsm := (Nat.succ_mul_choose_eq (S.card - 1) k).symm
        simp
        simp at nsm
        have : S.card > 0 := by
          exact Nat.zero_lt_of_ne_zero hS
        have :S.card -1 + 1 = S.card := by
          exact Nat.sub_add_cancel this
        rw [this] at nsm
        rw [mul_comm] at nsm
        exact nsm
      -- 整数へキャストして左右を並べ替え
      -- まず両辺を `Int` に
      have hZ :
          ( (S.card.choose k.succ : Int) * (k.succ : Int) )
            = (S.card : Int) * ((S.card - 1).choose k : Int) := by
        -- `hnat` を `congrArg` でキャストし、`simp` で整形
        have hZ' := congrArg (fun n : ℕ => (n : Int)) hnat
        -- 左右を見かけの形に揃える
        -- （ここは `ring` 的な交換結合のみ）
        simpa [Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc]
          using hZ'
      -- 各項を書き換え
      simpa [hZ]
    -- 3c) 残った和は二項定理： `∑_{k=0}^{n-1} (n-1 choose k) = 2^{n-1}`
    have h₅ :
        ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int)
          = (2 : Int) ^ (S.card - 1) := by
      -- 自然数版を取得
      have hNat :
          ∑ k ∈ Finset.range S.card, (S.card - 1).choose k
            = 2 ^ (S.card - 1) := by
        -- `Nat.sum_range_choose` は `∑_{m=0}^{n} choose n m = 2^n`
        -- ここでは `n := S.card - 1`、かつ `range S.card = range (n+1)`
        -- よってそのまま適用できる
        -- 具体的には両辺を `Finset.range (S.card - 1 + 1)` に直して一致
        have := Nat.sum_range_choose (n := S.card - 1)
        -- `range (n+1) = range S.card` を使って形を合わせる
        -- ※ `Nat.sub_add_cancel` は `S.card ≥ 1` が必要だが、
        --    左右とも同じ `range (n+1)` 形にすることで回避できる
        -- ここではそのまま採用（`this` の右辺はちょうど必要な形）
        simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        have eq: (S.card - 1 + 1)= S.card := by
          exact Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero hS)
        rw [eq] at this
        exact this

      -- 両辺を `Int` へキャストして整形
      -- （`simp` のみで、`using` は使わない）
      have hInt : ((∑ k ∈ Finset.range S.card, (S.card - 1).choose k : ℕ) : Int)
                  = (2 : Int) ^ (S.card - 1) := by
        -- 右辺は自動で `Nat.cast_pow` に展開される
        -- 左辺は `Nat.cast_sum` 等で展開される
        -- ここでも `simp` のみ
        simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]


      -- 目的の左辺は最初から `Int` なので、これで一致
      -- なお `Finset.sum` の型は変わっていない（被積分関数を `Int` にしただけ）
      simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Nat.cast_sum]
      simp_all only [Nat.cast_pow, Nat.cast_ofNat]
    -- 4) 連結して整理
    calc
      ∑ T ∈ S.powerset, (T.card : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) • (k : Int) := h₁
      _   = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) * (k : Int) := h₂
      _   = ∑ k ∈ Finset.range S.card,
              (S.card.choose k.succ : Int) * (k.succ : Int) := h₃
      _   = (S.card : Int) *
              ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int) := h₄
      _   = (S.card : Int) * (2 : Int) ^ (S.card - 1) := by
              -- h₅ を右辺に代入
              exact congrArg (HMul.hMul ↑S.card) h₅

      _   = (2 : Int) ^ (S.card - 1) * (S.card : Int) := by
              simp [mul_comm]


/-- 常に真の“誤差（debt）付き”版。
LHS ≤ 2^|Free| (2|B| − |Rep|) + (2^|Free| − |fiber|)(|V| − 2|B|) -/
lemma fiber_nds2_le_rep_term_with_debt {Q : SCCQuot α V R}
  (B : Finset α) (hB : B ⊆ Rep (Q := Q))(nonemp: (Free Q).Nonempty) :
  (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
      - (V.card : Int) * (fiber V R Q B).card
    ≤
  (2 : Int) ^ ( (Free (Q := Q)).card )
      * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
    + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
      * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
  classical
  -- A3 の粗い上界：
  --   ∑|I| ≤ |fiber||B| + ∑_{S⊆Free} |S|
  have hsum :=
    sum_card_over_fiber_le (Q := Q) (V := V) (R := R) (B := B) hB
  -- ∑_{S⊆Free} |S| = 2^{|Free|-1}|Free|
  have hbin :=
    sum_card_powerset_int (S := Free (Q := Q))
  -- |V| = |Rep| + |Free|
  have hVF : (V.card : Int) = (Rep (Q := Q)).card + (Free (Q := Q)).card :=
    cardV_as_Rep_plus_Free (Q := Q) (V := V)
  -- |fiber| ≤ 2^{|Free|}
  have hcard_le : (fiber V R Q B).card ≤ (2 : Nat) ^ (Free (Q := Q)).card :=
    fiber_card_le_two_pow (Q := Q) (V := V) (R := R) (B := B) hB
  -- 2 を掛けて |V||fiber| を引く（代数整理は `ring` / `linarith` 不使用で書けます）
  -- 以下、計算をまとめて書きます（骨子：以前の式変形と同じ）
  have : (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
           - (V.card : Int) * (fiber V R Q B).card
        ≤
         ((fiber V R Q B).card : Int) * ((2 : Int) * (B.card : Int) - (V.card : Int))
         + (2 : Int) * (∑ S ∈ (Free (Q := Q)).powerset, (S.card : Int)) := by
    -- hsum に 2 を掛けて −|V||fiber| を足し込む
    -- （A3 をそのまま拡張した形）
    -- 省略可：ここを小補題に切り出してもよいです
    simp_all only [tsub_le_iff_right]
    linarith

  -- ∑_{S⊆Free}|S| と |V| の置換
  -- さらに、右辺を
  --   = |fiber|*(2|B| − |Rep| − |Free|) + 2^|Free||Free|
  -- に直す（hbin, hVF を使用）
  have ps: (Free Q).card > 0 := by
    exact Finset.card_pos.mpr nonemp

  have : (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
           - (V.card : Int) * (fiber V R Q B).card
        ≤
        ((fiber V R Q B).card : Int) * ( (2 : Int) * (B.card : Int)
              - (Rep (Q := Q)).card - (Free (Q := Q)).card )
        + ((2 : Int) ^ ((Free (Q := Q)).card - 1) * ( (Free (Q := Q)).card : Int )) * 2 := by
    -- 直前の `have` に hbin,hVF を代入
    rw [hbin, hVF] at this
    simp_all only [tsub_le_iff_right]
    refine this.trans ?_
    simp_all only [add_le_add_iff_right]
    linarith



  -- 2 * 2^{F-1} = 2^F、そして右辺を
  --   = |fiber|*(2|B|−|V|) + 2^F*|Free|
  -- と書き直す
  have : (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
           - (V.card : Int) * (fiber V R Q B).card
        ≤
        ((fiber V R Q B).card : Int) * ( (2 : Int) * (B.card : Int) - (V.card : Int) )
        + ((2 : Int) ^ ((Free (Q := Q)).card)) * ((Free (Q := Q)).card : Int) := by
    ring_nf
    ring_nf at this

    have hV: V.card = (Rep Q).card + (Free Q).card := by
      simp_all only [tsub_le_iff_right]
      symm
      omega

    have hPow:2 ^ ((Free Q).card - 1) * 2 = 2 ^ (Free Q).card := by
      rw [← pow_succ, Nat.sub_add_cancel]
      simp_all only [Nat.cast_add, tsub_le_iff_right, Finset.one_le_card]


    have fc: ↑(Free Q).card * (2 : ℤ) ^ ((Free Q).card - 1) * 2 = ↑(Free Q).card * (2 : ℤ) ^ (Free Q).card := by
      norm_cast
      rw [←hPow]
      exact Nat.mul_assoc (Free Q).card (2 ^ ((Free Q).card - 1)) 2

    simp_all only [Nat.cast_add, tsub_le_iff_right, ge_iff_le]
    rw [← fc]
    simp_all only
    linarith
/-
  set F  := (fiber V R Q B).card
  set R₀ := (Rep Q).card
  set Fr := (Free Q).card
  have hPack :
    (-( (F : Int) * (R₀ : Int) ) - (F : Int) * (Fr : Int))
  = -( (V.card : Int) * (F : Int) ) := by
  -- -(F*R₀) - F*Fr = -(F*R₀ + F*Fr) = -(F*(R₀+Fr)) = -(F*V)
    have : (F : Int) * ((R₀ : Int) + (Fr : Int))
          = (F : Int) * (R₀ : Int) + (F : Int) * (Fr : Int) := by
      simp [mul_add]
    calc
      (-( (F : Int) * (R₀ : Int) ) - (F : Int) * (Fr : Int))
          = -((F : Int) * (R₀ : Int)) + (-(F : Int) * (Fr : Int)) := by
                simp [sub_eq_add_neg]
      _   = -((F : Int) * (R₀ : Int) + (F : Int) * (Fr : Int)) := by
                simp
                exact Int.add_comm (-(↑F * ↑R₀)) (-(↑F * ↑Fr))
      _   = -((F : Int) * ((R₀ : Int) + (Fr : Int))) := by
                exact congrArg Neg.neg (id (Eq.symm this))
      _   = -((F : Int) * (V.card : Int)) := by
                simp
                simp_all only [tsub_le_iff_right, Finset.card_eq_zero, true_or, F, R₀, Fr]

      _   = -((V.card : Int) * (F : Int)) := by
                simp [mul_comm]
  -/

  simp_all only [tsub_le_iff_right, Nat.cast_ofNat, ge_iff_le]
  linarith


open Finset

/-- ★ debt=0 になる立方体ケース（|fiber| = 2^{|Free|}） -/
lemma fiber_nds2_le_rep_term_of_fullCube
  {V : Finset α} {R : Finset (Rule α)} {Q : SCCQuot α V R}
  (B : Finset α) (hB : B ⊆ Rep (Q := Q)) (nonemp : (Free (Q := Q)).Nonempty)
  (hCard : (fiber V R Q B).card = (2 : Nat) ^ (Free (Q := Q)).card) :
  (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
      - (V.card : Int) * (fiber V R Q B).card
    ≤
  (2 : Int) ^ ( (Free (Q := Q)).card )
      * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := by
  classical
  -- with_debt を呼ぶ
  have base :=
    fiber_nds2_le_rep_term_with_debt (Q := Q) (V := V) (R := R)
      (B := B) hB nonemp
  -- ((2^F:Int) − |fiber|) = 0 を作る
  have hCardCast :
      ((fiber V R Q B).card : Int)
        = ((2 : Nat) ^ (Free (Q := Q)).card : Int) := by
    -- Nat 等式を Int に持ち上げ
    have := congrArg (fun n : Nat => (n : Int)) hCard
    simp_all only [Nat.cast_pow, Nat.cast_ofNat, sub_self, zero_mul, add_zero, tsub_le_iff_right]

  have hdiff0 :
      (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
        - (fiber V R Q B).card) = 0 := by
    -- 右の |fiber| も Int として扱う
    change (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
              - ((fiber V R Q B).card : Int)) = 0
    -- 右項を (2^F) に置換して sub_self
    rw [hCardCast]
    simp
  -- RHS の debt 項を 0 に潰して完成
  have hrw :
    (2 : Int) ^ ( (Free (Q := Q)).card )
        * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
      + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
        * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
    =
    (2 : Int) ^ ( (Free (Q := Q)).card )
        * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := by
    -- debt = 0 を代入
    have : (( (2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card)
              * ((V.card : Int) - (2 : Int) * (B.card : Int)) = 0 := by
      -- 左因子が 0
      rw [hdiff0, zero_mul]
    -- 和に 0 を足しただけ
    have := this
    -- 右辺を整理
    -- （`simp` で `+ 0` を消す）
    -- 直接等式として返す
    --  `simp` を使って記述を簡潔に
    --  （「simpa using」は使っていません）
    --  上の `this` を用いて一行で仕上げます
    --  置換 → 簡約
    --  （calc でも OK ですが短く）
    simpa [this]
  -- 連鎖：LHS ≤ base（with_debt） = 目的 RHS
  calc
    (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        - (V.card : Int) * (fiber V R Q B).card
      ≤ (2 : Int) ^ ( (Free (Q := Q)).card )
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := base
    _ = (2 : Int) ^ ( (Free (Q := Q)).card )
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := hrw


/-- ★ 符号条件（2·|B| ≥ |V|）から debt ≤ 0 を落として仕上げ -/
lemma fiber_nds2_le_rep_term_of_nonneg
  {V : Finset α} {R : Finset (Rule α)} {Q : SCCQuot α V R}
  (B : Finset α) (hB : B ⊆ Rep (Q := Q)) (nonemp : (Free (Q := Q)).Nonempty)
  (hSign : (2 : Int) * (B.card : Int) - (V.card : Int) ≥ 0) :
  (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
      - (V.card : Int) * (fiber V R Q B).card
    ≤
  (2 : Int) ^ ( (Free (Q := Q)).card )
      * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := by
  classical
  -- with_debt
  have base :=
    fiber_nds2_le_rep_term_with_debt (Q := Q) (V := V) (R := R)
      (B := B) hB nonemp
  -- (2^F − |fiber|) ≥ 0 を作る（|fiber| ≤ 2^F）
  have hcard_le_nat :
      (fiber V R Q B).card ≤ (2 : Nat) ^ (Free (Q := Q)).card :=
    fiber_card_le_two_pow (Q := Q) (V := V) (R := R) (B := B) hB
  have hA :
      0 ≤ (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
            - ((fiber V R Q B).card : Int)) :=
    sub_nonneg.mpr (by
      -- Nat の ≤ を Int にキャスト
      exact_mod_cast hcard_le_nat)
  -- (V − 2B) ≤ 0 を作る（仮定 2|B| − |V| ≥ 0）
  have hVle : (V.card : Int) ≤ (2 : Int) * (B.card : Int) :=
    (sub_nonneg.mp hSign)
  have hB' : ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ≤ 0 :=
    sub_nonpos.mpr hVle
  -- debt ≤ 0
  have hDebt_nonpos :
      ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
      * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by
        -- 右の式は (… : Int) と (… : Int) の差に合わせる
        change 0 ≤ (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
                      - ((fiber V R Q B).card : Int))
        exact hA)
      hB'
  -- 「RHS = base + debt ≤ base + 0 = base」で落とす
  have hdrop :
    (2 : Int) ^ ( (Free (Q := Q)).card )
        * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
      + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
        * ( (V.card : Int) - (2 : Int) * (B.card : Int) )
    ≤
    (2 : Int) ^ ( (Free (Q := Q)).card )
        * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := by
    -- debt ≤ 0 を左右に加えてから 0 で消す
    have := add_le_add_left hDebt_nonpos
      ((2 : Int) ^ ( (Free (Q := Q)).card )
          * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ))
    -- いま `… + debt ≤ … + 0`
    -- 右辺を簡約して目標へ
    -- `simp` で `+ 0` を消去
    -- 注意：ここでも「simpa using」は使わない
    -- 直接 `have` を `simp` 付きで整形
    -- 返すべきのは「… ≤ base」
    -- `simp` だけで右辺が base になります
    simpa
      [zero_mul, add_comm, add_left_comm, add_assoc] using this
  -- 連鎖
  calc
    (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        - (V.card : Int) * (fiber V R Q B).card
      ≤ (2 : Int) ^ ( (Free (Q := Q)).card )
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := base
    _ ≤ (2 : Int) ^ ( (Free (Q := Q)).card )
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) := hdrop

lemma fiber_subset_family  (B : Finset α) :
  fiber V R Q B ⊆ family V R := by
  intro I hI
  exact (Finset.mem_filter.mp hI).1

/-- `⋃₍B⊆Rep₎ fiber B = family` -/
lemma biUnion_fibers_eq_family (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R):
  (Rep (Q := Q)).powerset.biUnion (fun B => fiber V R Q B) = family V R := by
  classical
  ext I; constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨B, hB, hIf⟩
    exact (Finset.mem_filter.mp hIf).1
  · intro hI
    -- 取るべき B は B := I ∩ Rep
    have hBsub : I ∩ Rep (Q := Q) ⊆ Rep (Q := Q) := by
      intro x hx; exact (Finset.mem_inter.mp hx).2
    have hBin : I ∩ Rep (Q := Q) ∈ (Rep (Q := Q)).powerset :=
      Finset.mem_powerset.mpr hBsub
    have hIf : I ∈ fiber V R Q (I ∩ Rep (Q := Q)) :=
      Finset.mem_filter.mpr ⟨hI, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨_, hBin, hIf⟩

/-- 異なる `B` の fiber は素に交わる -/
lemma fibers_disjoint   (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B₁ B₂ : Finset α} (h₁ : B₁ ∈ (Rep (Q := Q)).powerset) (h₂ : B₂ ∈ (Rep (Q := Q)).powerset)
  (hNe : B₁ ≠ B₂) :
  Disjoint (fiber V R Q B₁) (fiber V R Q B₂) := by
  classical
  -- 同じ I が両方に入ると，`I ∩ Rep = B₁ = B₂` になってしまう
  refine Finset.disjoint_left.mpr ?_
  intro I hI₁ hI₂
  have htr₁ : I ∩ Rep (Q := Q) = B₁ := (Finset.mem_filter.mp hI₁).2
  have htr₂ : I ∩ Rep (Q := Q) = B₂ := (Finset.mem_filter.mp hI₂).2
  subst htr₁ htr₂
  simp_all only [mem_powerset, inter_subset_right, ne_eq, not_true_eq_false]

/-- `∑_{B⊆Rep} ∑_{I∈fiber B} F I = ∑_{I∈family} F I` -/
lemma sum_over_fibers_eq_sum_family (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (F : Finset α → Int) :
  ∑ B ∈ (Rep (Q := Q)).powerset, ∑ I ∈ fiber V R Q B, F I
    = ∑ I ∈ family V R, F I := by
  classical
  -- `sum_biUnion` は pairwise-disjoint のみを要求
  have hpair :
    (↑((Rep (Q := Q)).powerset) : Set (Finset α)).Pairwise
      (fun B₁ B₂ => Disjoint (fiber V R Q B₁) (fiber V R Q B₂)) := by
    intro B₁ h₁ B₂ h₂ hNe
    -- Set の所属を Finset の所属に戻す
    have h₁' : B₁ ∈ (Rep (Q := Q)).powerset := by simpa using h₁
    have h₂' : B₂ ∈ (Rep (Q := Q)).powerset := by simpa using h₂
    exact fibers_disjoint V R Q h₁' h₂' hNe

  -- biUnion 側の和と「B で和→fiber内で和」の同値
  have h :=
    Finset.sum_biUnion
      (s := (Rep (Q := Q)).powerset)
      (t := fun B => fiber V R Q B)
      (f := fun I => F I)
      hpair
  -- biUnion = family に置換
  have hcov := biUnion_fibers_eq_family (Q := Q) (V := V) (R := R)

  calc
    ∑ B ∈ (Rep (Q := Q)).powerset, ∑ I ∈ fiber V R Q B, F I
        = ∑ I ∈ ((Rep (Q := Q)).powerset.biUnion (fun B => fiber V R Q B)), F I := by
          exact h.symm
    _ = ∑ I ∈ family V R, F I := by
          rw [hcov]


--以下もbindなし版でも使う。
/-- 「個数」版（Int）：`∑_{B⊆Rep} ∑_{I∈fiber B} 1 = |family|` -/
lemma sum_ones_over_fibers_eq_card_family (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R):
  ∑ B ∈ (Rep (Q := Q)).powerset, ∑ _ ∈ fiber V R Q B, (1 : Int)
    = (family V R).card := by
  classical

  -- まず biUnion で family の和に変換
  have h := sum_over_fibers_eq_sum_family
              (Q := Q) (V := V) (R := R) (F := fun (_ : Finset α) => (1 : Int))
  -- 右辺 `∑ I∈family 1 = |family|`
  -- 左辺の形に揃えて返す
  calc
    ∑ B ∈ (Rep (Q := Q)).powerset, ∑ I ∈ fiber V R Q B, (1 : Int)
        = ∑ I ∈ family V R, (1 : Int) := by exact h
    _ = (family V R).card := by
          -- `sum_const_int` を使う
          have := ThreadC_Fiber.sum_const_int (s := family V R) (c := (1 : Int))
          -- `∑ I∈family 1 = (family.card:Int) * 1 = family.card`
          -- `simp` で最後の `* 1` を消去
          -- 「simpa using」は使わず二段で
          have : ∑ I ∈ family V R, (1 : Int) = ((family V R).card : Int) * (1 : Int) := this
          -- さらに `* 1` を消す
          -- 右辺は Int，目標は Nat。等式そのものを展開して返す
          -- まず Int での等式を得てから型の目標に合わせます
          -- ここは `simp` 一行
          -- ただし目標は Int ではなく Nat なので，上の等式を直接使うように statement を Int にしてあります
          -- よって `simp` だけ
          simp_all only [sum_const, Int.nsmul_eq_mul, mul_one]

/-! ## 3) 二項恒等式（既知として使用可）：powerset の大きさ・「大きさの総和」 -/

/- powerset のカード：既知 -/
omit [DecidableEq α] in
lemma card_powerset_pow (S : Finset α) :
  S.powerset.card = (2 : Nat) ^ S.card := by
  classical
  exact Finset.card_powerset _

/-! ## 4) 主要項の総和は 0 -/

--bindなし版でも使う。
lemma sum_main_over_powerset_eq_zero (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)  :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) = 0 := by
  classical
  -- 線形化
  have hlin: ∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        =
        (2 : Int) * (∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int))
        - ∑ _B ∈ (Rep (Q := Q)).powerset, (Rep (Q := Q)).card := by
    -- `sum_sub_distrib` を使わず，両辺を展開して作る
    -- 左辺の和を「和の差」に分ける
    -- 2行で：
    --   ∑ (2*|B| - |Rep|) = ∑ (2*|B|) - ∑ |Rep|
    --   さらに ∑ (2*|B|) = 2 * ∑ |B|
    -- 今はまず差の形へ
    -- （`by`で `simp` を使っても可）
    -- ここでは `by` で `simp` を用いる
    -- 1 行：
    simp [Finset.sum_sub_distrib, two_mul, mul_comm]
    simp [mul_two]
    rw [← sum_add_distrib]

  have hconst :
      ∑ _B ∈ (Rep (Q := Q)).powerset, (Rep (Q := Q)).card
        = ((Rep (Q := Q)).powerset.card : Int) * (Rep (Q := Q)).card := by
    simp_all only [sum_sub_distrib, sum_const, card_powerset, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul,
    Nat.cast_mul, sub_left_inj]

  have hsumcard :
      ∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int)
        = (2 : Int) ^ ((Rep (Q := Q)).card - 1) * (Rep (Q := Q)).card := by

    exact sum_card_powerset_int (S := Rep (Q := Q))

  have hpowN :
      ((Rep (Q := Q)).powerset.card : Int)
        = ((2 : Nat) ^ (Rep (Q := Q)).card : Int) := by
    have := card_powerset_pow (S := Rep (Q := Q))
    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul, Nat.cast_mul,
    sub_left_inj, card_powerset]

  -- r := |Rep|
  set r := (Rep (Q := Q)).card
  -- 2*(2^{r-1} r) − (2^r) r = 0 を r で場合分け
  have hcalc :
    (2 : Int) * ( (2 : Int) ^ (r - 1) * (r : Int) )
      - (( (2 : Nat) ^ r : Int)) * (r : Int) = 0 := by
    cases' hr:r with r0
    · -- r = 0 : どちらも 0
      simp
    · -- r = r0+1
      have hr1 : r - 1 = r0 := by exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm hr)))
      have hx : (( (2 : Nat) ^ r : Int)) = (2 : Int) ^ r := by exact rfl--two_pow_nat_cast_eq_int_pow r
      -- 2*(2^{r-1}) = (2^r)
      -- 両項を (2^r0 * 2) * (r0+1) にそろえて相殺
      have h1 :
        (2 : Int) * ((2 : Int) ^ (r - 1) * ((Nat.succ r0 : Nat) : Int))
          = ((2 : Int) ^ r0 * (2 : Int)) * ((Nat.succ r0 : Nat) : Int) := by
        simp [hr1, mul_comm, mul_left_comm]
      have h2 :
        (( (2 : Nat) ^ r : Int)) * ((Nat.succ r0 : Nat) : Int)
          = ((2 : Int) ^ r0 * (2 : Int)) * ((Nat.succ r0 : Nat) : Int) := by
        -- Nat→Int の冪キャストと pow_succ
        have : (2 : Int) ^ r = (2 : Int) ^ r0 * (2 : Int) := by
          ring_nf
          rw [hr]
          have : r > 0:= by exact Nat.lt_of_sub_eq_succ hr
          exact rfl

        simp
        rw [this]
        simp
      rw [hr] at h1
      rw [hr] at h2
      dsimp [Nat.succ] at h1 h2
      have : r0 + 1 - 1 = r0 := by
        exact rfl
      rw [this]
      norm_cast at h1
      norm_cast
      rw [h1]
      norm_cast at h2
      rw [h2]
      simp

  calc
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
      = (2 : Int) * ( (2 : Int) ^ ((Rep (Q := Q)).card - 1) * (Rep (Q := Q)).card )
        - (((Rep (Q := Q)).powerset.card : Int) * (Rep (Q := Q)).card) := by
          rw [hlin, hsumcard, hconst]
    _ = 0 := by
          -- r と 2^r に置換して hcalc を適用
          simpa [r, hpowN] using hcalc

/-! ## 5) NDS₂ の family 版に総和して集約（主項は 0 に落ち，debt だけ残る） -/

--これもbindなし版で使うが未整備
/-- debt の定義（書きやすさのため関数に） -/
noncomputable def Debt  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (B : Finset α) : Int :=
  ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
    * ( (V.card : Int) - (2 : Int) * (B.card : Int) )

/-- ★ `NDS2 V (family V R) ≤ ∑_{B⊆Rep} Debt(B)` -/
lemma nds2_family_le_sum_debt  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)  (nonemp : (Free (Q := Q)).Nonempty) :
  NDS2 V (family V R)
    ≤ ∑ B ∈ (Rep (Q := Q)).powerset, Debt (Q := Q) (V := V) (R := R) B := by
  classical
  -- fiber with_debt を B で総和
  have base_sum :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (∑ I ∈ fiber V R Q B, (1 : Int)) )
      ≤
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ ((Free (Q := Q)).card)
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + Debt (Q := Q) (V := V) (R := R) B ) := by
    -- with_debt を各 B に適用し，`sum_le_sum`
    apply Finset.sum_le_sum
    intro B hB
    have hBsub : B ⊆ Rep (Q := Q) := (Finset.mem_powerset.mp hB)
    -- with_debt の左側は `-(V.card) * |fiber|` でしたが，
    -- ここでは `-(V.card) * ∑ 1` に同じ形で書いています（等価）
    -- `∑ 1 = card` はこの後まとめて family 側に移すので OK
    have h := fiber_nds2_le_rep_term_with_debt (Q := Q) (V := V) (R := R)
                (B := B) hBsub nonemp
    -- そのまま使える（左も右も一致する形）
    simp_all only [mem_powerset, Nat.cast_ofNat, tsub_le_iff_right, sum_const, Int.nsmul_eq_mul, mul_one, ge_iff_le]
    exact h

  -- 左辺を family の和に置換
  have hSumI :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ∑ I ∈ fiber V R Q B, (I.card : Int)
      = ∑ I ∈ family V R, (I.card : Int) :=
    sum_over_fibers_eq_sum_family (Q := Q) (V := V) (R := R)
      (F := fun I : Finset α => (I.card : Int))
  have hSum1 :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ∑ I ∈ fiber V R Q B, (1 : Int)
      = (family V R).card :=
    sum_ones_over_fibers_eq_card_family (Q := Q) (V := V) (R := R)
  have hL :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (∑ I ∈ fiber V R Q B, (1 : Int)) )
      =
      (2 : Int) * (∑ I ∈ family V R, (I.card : Int))
       - (V.card : Int) * (family V R).card := by
    -- 線形化して `hSumI` と `hSum1` を代入
    calc
      _ = (2 : Int)
              * (∑ B ∈ (Rep (Q := Q)).powerset,
                    ∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int)
              * (∑ B ∈ (Rep (Q := Q)).powerset,
                    ∑ I ∈ fiber V R Q B, (1 : Int)) := by
            simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]
      _ = (2 : Int) * (∑ I ∈ family V R, (I.card : Int))
            - (V.card : Int) * (family V R).card := by
            rw [hSumI, hSum1]
  -- 右辺の主項総和は 0 に落ちる
  have hMainZero :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ ((Free (Q := Q)).card)
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) )
      = 0 := by
    -- 定数因子を外に出して内側の総和 0
    calc
      _ = (2 : Int) ^ ((Free (Q := Q)).card)
            * (∑ B ∈ (Rep (Q := Q)).powerset,
                  ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )) := by
            simp
            simp_all only [sum_const, Int.nsmul_eq_mul, mul_one, sum_sub_distrib, tsub_le_iff_right]
            simp only [← mul_sum]
            simp_all only [sum_sub_distrib, sum_const, card_powerset, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
              mul_eq_mul_left_iff, sub_left_inj, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, false_and, or_false]
            rw [mul_sum]
      _ = (2 : Int) ^ ((Free (Q := Q)).card) * 0 := by
            -- 内側は直前の恒等式
            have h := sum_main_over_powerset_eq_zero (Q := Q) (V := V) (R := R)
            rw [h]
      _ = 0 := by simp
  -- 右辺の和を分離して主項=0 に
  have hR :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ ((Free (Q := Q)).card)
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + Debt (Q := Q) (V := V) (R := R) B )
      =
      ∑ B ∈ (Rep (Q := Q)).powerset, Debt (Q := Q) (V := V) (R := R) B := by
    -- 線形性：sum_add_distrib
    have :
        (∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) ^ ((Free (Q := Q)).card)
                * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) ))
        + (∑ B ∈ (Rep (Q := Q)).powerset, Debt (Q := Q) (V := V) (R := R) B)
      =
        ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ ((Free (Q := Q)).card)
                * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
            + Debt (Q := Q) (V := V) (R := R) B ) := by
      simp [Finset.sum_add_distrib]
    -- 主項の総和 0
    have : ∑ B ∈ (Rep (Q := Q)).powerset,
              ( (2 : Int) ^ ((Free (Q := Q)).card)
                  * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) ) = 0 :=
      hMainZero
    -- 仕上げ
    -- `simp` で 0 を消す
    have := this
    -- 目標の向きに整形
    have :
      ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ ((Free (Q := Q)).card)
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + Debt (Q := Q) (V := V) (R := R) B )
      =
      ∑ B ∈ (Rep (Q := Q)).powerset, Debt (Q := Q) (V := V) (R := R) B := by
      -- 先の等式の左右をひっくり返して 0 を消す
      -- 1 行：
      simp_all only [sum_const, Int.nsmul_eq_mul, mul_one, sum_sub_distrib, tsub_le_iff_right, zero_add]

    exact this
  -- 連鎖：LHS を family に置換，RHS 主項を 0 に
  calc
    NDS2 V (family V R)
        = (2 : Int) * (∑ I ∈ family V R, (I.card : Int))
            - (V.card : Int) * (family V R).card := by
          -- NDS2 の定義を線形化
          simp [NDS2, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]
    _ = ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (∑ I ∈ fiber V R Q B, (1 : Int)) ) := by
          exact hL.symm
    _ ≤ ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) ^ ((Free (Q := Q)).card)
              * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
            + Debt (Q := Q) (V := V) (R := R) B ) := base_sum
    _ = ∑ B ∈ (Rep (Q := Q)).powerset, Debt (Q := Q) (V := V) (R := R) B := hR

lemma nds2_family_nonpos_of_debt_nonpos (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (nonemp : (Free (Q := Q)).Nonempty)
  (hDebtSumNonpos :
    ∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B ≤ 0) :
  NDS2 V (family V R) ≤ 0 := by
  classical
  -- まず C' で得た上界
  have h := nds2_family_le_sum_debt (Q := Q) (V := V) (R := R) nonemp
  -- 連鎖
  exact le_trans h hDebtSumNonpos


end ThreadC_Fiber
