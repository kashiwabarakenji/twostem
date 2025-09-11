import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Int
import Twostem.General
import Twostem.Basic
import Twostem.ProblemCC
import Twostem.ProblemC
import LeanCopilot

open scoped BigOperators
open ThreadC
open ThreadC_Fiber
open Finset
universe u
variable {α : Type u} [DecidableEq α]

lemma fiber_has_bounds
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B I : Finset α} --(hB : B ⊆ Rep (Q := Q))
  (hI : I ∈ fiber V R Q B) :
  B ⊆ I ∧ I ⊆ B ∪ (Free (Q := Q)) := by
  classical
  -- I ∩ Rep = B と I ∈ family を取り出す
  obtain ⟨hIfam, hcap⟩ := (mem_fiber_iff V R Q).1 hI
  -- (1) B ⊆ I
  have hBi : B ⊆ I := by

    have : (I ∩ Rep (Q := Q)) ⊆ I := by
      exact inter_subset_left

    rw [← hcap]
    exact this

  have hIV : I ⊆ V := by
    exact family_subsets V R hIfam

  -- 実際の包含証明
  have hI_sub : I ⊆ B ∪ Free (Q := Q) := by
    intro x hxI
    by_cases hxRep : x ∈ Rep (Q := Q)
    · -- x∈Rep → x∈I∩Rep = B
      have hxIR : x ∈ I ∩ Rep (Q := Q) := by
        exact mem_inter_of_mem hxI hxRep
      have : x ∈ B := by

        have hxIR' := hxIR

        have : x ∈ B := by

          rw [← hcap]
          exact hxIR'
        exact this
      exact mem_union_left (Free Q) this

    · -- x ∉ Rep ⇒ I ⊆ V より x ∈ V，ゆえに x ∈ V \ Rep = Free
      have hxV : x ∈ V := by
        exact hIV hxI
      have : x ∈ Free (Q := Q) := by

        have hx : x ∈ V ∧ x ∉ Rep (Q := Q) := And.intro hxV hxRep

        have : x ∈ V \ Rep (Q := Q) := by

          simpa [Free, Rep] using hx
        -- そのまま返す
        exact this
      exact mem_union_right B this
  exact And.intro hBi hI_sub

lemma fiber_diff_subset_free
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B I : Finset α} --(hB : B ⊆ Rep (Q := Q))
  (hI : I ∈ fiber V R Q B) :
  I \ B ⊆ (Free (Q := Q)) := by
  classical
  -- まず I ⊆ B ∪ Free を得る
  have hbounds := fiber_has_bounds (V := V) (R := R) (Q := Q) (hI := hI)
  have hI_sub : I ⊆ B ∪ Free (Q := Q) := hbounds.2
  -- 既存補題から差集合の包含へ
  exact sdiff_subset_of_subset_union hI_sub

lemma diff_inj_on_fiber
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B I J : Finset α}
  --(hB : B ⊆ Rep (Q := Q))
  (hI : I ∈ fiber V R Q B) (hJ : J ∈ fiber V R Q B)
  (hEq : I \ B = J \ B) :
  I = J := by
  classical
  -- B ⊆ I, B ⊆ J
  have hIB := (fiber_has_bounds (V := V) (R := R) (Q := Q) (hI := hI)).1
  have hJB := (fiber_has_bounds (V := V) (R := R) (Q := Q) (hI := hJ)).1
  -- B ∪ (I \ B) = I, B ∪ (J \ B) = J
  have hIeq : B ∪ (I \ B) = I := union_sdiff_eq_of_subset hIB
  have hJeq : B ∪ (J \ B) = J := union_sdiff_eq_of_subset hJB
  -- 差集合の等式から等号へ
  calc
    I = B ∪ (I \ B) := by
      exact hIeq.symm
    _ = B ∪ (J \ B) := by
      -- ここで hEq を用いて置換
      -- 左右の第二項が等しい
      -- `rw` で十分
      rw [hEq]
    _ = J := by
      exact hJeq

lemma image_diff_maps_to_powerset_free
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α}:-- (hB : B ⊆ Rep (Q := Q)) :
  (fiber V R Q B).image (fun I => I \ B) ⊆ (Free (Q := Q)).powerset := by
  classical
  intro S hS
  rcases mem_image.mp hS with ⟨I, hIf, rfl⟩
  -- `I \ B ⊆ Free` なので powerset へ
  have hsub : I \ B ⊆ Free (Q := Q) :=
    fiber_diff_subset_free (V := V) (R := R) (Q := Q)  (hI := hIf)
  -- `mem_powerset` で終了
  exact mem_powerset.mpr hsub

lemma card_fiber_le_pow_free
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α}:-- (hB : B ⊆ Rep (Q := Q)) :
  (fiber V R Q B).card ≤ (2 : Nat) ^ (Free (Q := Q)).card := by
  classical
  let f : Finset α → Finset α := fun I => I \ B
  -- injOn: `I ↦ I \ B` が fiber 上で単射
  have hinj :
      ∀ {I} (_hI : I ∈ fiber V R Q B) {J} (_hJ : J ∈ fiber V R Q B),
        f I = f J → I = J := by
    intro I hI J hJ hEq
    -- 先の補題を使う
    exact diff_inj_on_fiber (V := V) (R := R) (Q := Q) (hI := hI) (hJ := hJ) (hEq := hEq)
  -- `card (image f) = card (fiber)`
  have hcard_image :
      ((fiber V R Q B).image f).card = (fiber V R Q B).card := by
    -- 提供補題 `card_image_eq_of_injOn`
    refine card_image_eq_of_injOn (s := fiber V R Q B) (f := f) ?_
    intro a ha b hb hfab
    exact hinj ha hb hfab
  -- 像が powerset(Free) に入る
  have himg_subset :
      (fiber V R Q B).image f ⊆ (Free (Q := Q)).powerset :=
    image_diff_maps_to_powerset_free (V := V) (R := R) (Q := Q)
  -- カード数の比較
  have hle :
      ((fiber V R Q B).image f).card ≤ ((Free (Q := Q)).powerset).card := by
    exact card_le_card himg_subset
  -- 連鎖計算
  calc
    (fiber V R Q B).card
        = ((fiber V R Q B).image f).card := by
          exact hcard_image.symm
    _   ≤ ((Free (Q := Q)).powerset).card := hle
    _   = (2 : Nat) ^ (Free (Q := Q)).card := by
          exact card_powerset_pow (Free (Q := Q))

lemma card_diff_le_free_card
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B I : Finset α} --(hB : B ⊆ Rep (Q := Q))
  (hI : I ∈ fiber V R Q B) :
  (I \ B).card ≤ (Free (Q := Q)).card := by
  classical
  have hsub : I \ B ⊆ Free (Q := Q) :=
    fiber_diff_subset_free (V := V) (R := R) (Q := Q)  (hI := hI)
  exact card_le_card hsub

lemma sum_card_diff_le_free_mul_card_fiber_nat
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α}:-- (hB : B ⊆ Rep (Q := Q)) :
  ∑ I ∈ fiber V R Q B, (I \ B).card
    ≤ (Free (Q := Q)).card * (fiber V R Q B).card := by
  classical
  -- 各項の一様上界
  have hbound : ∀ I ∈ fiber V R Q B, (I \ B).card ≤ (Free (Q := Q)).card := by
    intro I hI
    exact card_diff_le_free_card (V := V) (R := R) (Q := Q) (hI := hI)
  -- 和の比較：∑ (I\B).card ≤ ∑ const = card * const
  have hsum_le :
      ∑ I ∈ fiber V R Q B, (I \ B).card
        ≤ ∑ I ∈ fiber V R Q B, (Free (Q := Q)).card := by
    refine sum_le_sum ?_
    intro I hI
    exact hbound I hI
  -- 定数和の評価（Nat）
  have hsum_const :
      ∑ I ∈ fiber V R Q B, (Free (Q := Q)).card
        = (fiber V R Q B).card * (Free (Q := Q)).card := by
    -- Nat 版の定数和：`sum_const_nat`
    -- `∑ x ∈ s, c = s.card * c`
    simp_all only [sum_const, smul_eq_mul]

  apply le_trans hsum_le
  simp_all only [sum_const, smul_eq_mul]
  rw [mul_comm]

/-- Nat の和を Int に持ち上げるための小補題（`simpa using` なし） -/
lemma sum_card_nat_to_int (s : Finset (Finset α)) :
  ∑ A ∈ s, (A.card : Int) = ((∑ A ∈ s, A.card) : Int) := by
  classical
  refine Finset.induction_on s ?base ?step
  · -- s = ∅
    simp
  · intro a s ha_notin hs
    -- ∑ over insert
    -- 左辺
    have L :
        ∑ A ∈ insert a s, (A.card : Int)
          = (a.card : Int) + ∑ A ∈ s, (A.card : Int) := by
      simp [ha_notin]
    -- 右辺
    have R :
        ((∑ A ∈ insert a s, A.card) : Int)
          = (a.card : Int) + ((∑ A ∈ s, A.card) : Int) := by
      have : (∑ A ∈ insert a s, A.card) = a.card + (∑ A ∈ s, A.card) := by
        simp [ha_notin]
      -- cast
      -- (x + y : ℕ :> ℤ) = (x:ℤ) + (y:ℤ)
      -- `Nat.cast_add` を利用
      -- `rw` で移項
      exact L
    -- 仕上げ
    -- 帯同帰納法の仮定 hs を使って両辺の後半を一致させる
    -- L と R を結合
    calc
      ∑ A ∈ insert a s, (A.card : Int)
          = (a.card : Int) + ∑ A ∈ s, (A.card : Int) := L
      _   = (a.card : Int) + ((∑ A ∈ s, A.card) : Int) := by
              -- 帯同帰納法の仮定 hs を使用
              -- hs : ∑ A ∈ s, (A.card : Int) = ((∑ A ∈ s, A.card) : Int)
              -- `rw [hs]`
              rw [hs]
      _   = ((∑ A ∈ insert a s, A.card) : Int) := by
              -- R を対辺へ
              -- 位置合わせのために左右を入れ替える
              -- 直前の等式 R の対称形
              exact R.symm

lemma eq_of_insert_eq_insert_of_not_mem
  {α : Type*} [DecidableEq α] {a : α} {X Y : Finset α}
  (haX : a ∉ X) (haY : a ∉ Y)
  (h : insert a X = insert a Y) : X = Y := by
  -- 片側包含：X ⊆ Y
  have hXY : X ⊆ Y := by
    intro x hxX
    -- x ∈ insert a X
    have hxInsX : x ∈ insert a X := by
      -- `x ∈ insert a X ↔ x = a ∨ x ∈ X`
      exact (mem_insert).mpr (Or.inr hxX)
    -- 等式で運ぶ：x ∈ insert a Y
    have hxInsY : x ∈ insert a Y := by
      -- `congrArg (fun s => x ∈ s)` でメンバーシップの等式へ
      have := congrArg (fun s : Finset α => x ∈ s) h
      simp_all only [mem_insert]
    -- `x = a ∨ x ∈ Y`
    have hxAorY : x = a ∨ x ∈ Y := (mem_insert).mp hxInsY
    -- もし x = a なら a ∈ X（= hxX）と矛盾（haX）
    cases hxAorY with
    | inl hxa =>
        -- `x = a` を代入すると `a ∈ X`
        -- 矛盾から任意の命題が出るので，ここでは `cases` で閉じる
        have : a ∈ X := by
          -- `rw [hxa]` で hxX を書き換え
          -- （`simpa using` は使わない）
          have := hxX

          subst hxa
          exact this
        exact (haX this).elim
    | inr hxY =>
        exact hxY
  -- 逆包含：Y ⊆ X（同様）
  have hYX : Y ⊆ X := by
    intro y hyY
    have hyInsY : y ∈ insert a Y :=
      (mem_insert).mpr (Or.inr hyY)
    have hyInsX : y ∈ insert a X := by
      have := congrArg (fun s : Finset α => y ∈ s) h
      -- 逆向きに使う
      simp_all only [mem_insert, or_true]
    have hyaOrX : y = a ∨ y ∈ X := (mem_insert).mp hyInsX
    cases hyaOrX with
    | inl hya =>
        have : a ∈ Y := by
          subst hya
          exact hyY
        exact (haY this).elim
    | inr hyX =>
        exact hyX
  -- ２つの包含から等号
  exact subset_antisymm hXY hYX

lemma insert_eq_insert_iff_of_not_mem
  {a : α} {X Y : Finset α}
  (haX : a ∉ X) (haY : a ∉ Y) :
  insert a X = insert a Y ↔ X = Y := by
  constructor
  · intro h
    exact eq_of_insert_eq_insert_of_not_mem haX haY h
  · intro hXY
    -- X = Y なら insert a X = insert a Y は自明
    -- `rw [hXY]` か `cases hXY; rfl`
    cases hXY
    rfl

lemma powerset_nat (n : ℕ) :
    2 * (n * 2 ^ (n - 1)) + 2 ^ n = (n + 1) * 2 ^ n := by
  nth_rw 1 [← Nat.mul_assoc]
  nth_rw 1 [Nat.mul_comm 2]
  cases n with
  | zero =>
    -- n = 0 のとき
    simp  -- 0 - 1 = 0, 2^0 = 1
  | succ m =>
    -- n = m + 1 のとき（m : ℕ）
    -- 2 * 2^m = 2^(m+1) を使う
    rw [Nat.succ_sub_succ, Nat.pow_succ]  -- (m+1)-1 = m, 2^m * 2 = 2^(m+1)
    simp_all only [tsub_zero]
    ring_nf

private lemma sum_card_powerset_nat
  (S : Finset α) :
  ∑ T ∈ S.powerset, T.card = S.card * (2 : Nat) ^ (S.card - 1) := by
  classical
  induction  S  using Finset.induction_on with
  | empty =>
    -- LHS = ∑ T∈{∅}, |T| = 0, RHS = 0 * 2^(0-1)=0*1=0
    simp
  | insert a S ha_notMem IH =>
    -- a ∉ S, IH: ∑ T∈S.powerset,
    -- powerset の分割：⊆S と a を含む像
    have hps :
        (insert a S).powerset
          = S.powerset ∪ (S.powerset.image (fun T => insert a T)) := by
      -- 既知：`powerset_insert`（a∉S）
      simp [Finset.powerset_insert] -- `simp` は使用、ただし `simpa using` は不使用
    -- 和の分割（互いに素）
    have hdisj :
        Disjoint S.powerset (S.powerset.image (fun T => insert a T)) := by
      -- 片方は a を含まず，他方は必ず a を含む
      dsimp [Disjoint]
      intro U hU hV V hUV
      --refine disjoint_left.mpr ?_
      exfalso
      have h_img : V ∈ S.powerset.image (fun T => insert a T) := hV hUV
  -- image の定義より、ある T ∈ S.powerset が存在して V = insert a T
      obtain ⟨T, hT⟩ := Finset.mem_image.1 h_img
      -- insert a T は必ず a を含む
      have h_a_in_V : a ∈ V := by
        simp_all only [mem_image, mem_powerset]
        obtain ⟨w, h⟩ := h_img
        obtain ⟨left, right⟩ := hT
        obtain ⟨left_1, right_1⟩ := h
        subst right
        simp_all only [mem_insert, true_or]

      have : a ∉  V:= by --ha_notMemと hUとhUVを使う。
        exact notMem_of_mem_powerset_of_notMem (hU hUV) ha_notMem

      exact this h_a_in_V

    -- sum の分解
    have hsum_split :
        ∑ U ∈ (insert a S).powerset, U.card
          =
        ∑ U ∈ S.powerset, U.card
          + ∑ U ∈ (S.powerset.image (fun T => insert a T)), U.card := by
      -- `sum_union` を使う
      simp_all only
      rw [← IH]
      simp_all only
      rw [Finset.sum_union hdisj, IH]

    have hinj :
        ∀ {X} (_ : X ∈ S.powerset) {Y} (_ : Y ∈ S.powerset),
          insert a X = insert a Y → X = Y := by
      intro X hX Y hY hEq
      -- a ∉ X, a ∉ Y（X,Y ⊆ S）なので `erase` で戻せる
      have haX : a ∉ X := by
        exact fun hx => ha_notMem ((mem_powerset.mp hX) hx)
      have haY : a ∉ Y := by
        exact fun hy => ha_notMem ((mem_powerset.mp hY) hy)
      -- `erase_insert` を使う
      have : X = (insert a X).erase a := by
        simp [erase_insert haX]
      have : Y = (insert a Y).erase a := by
        simp [erase_insert haY]

      exact by
        -- `Finset.insert_inj` : insert x s₁ = insert x s₂ ↔ s₁ = s₂ (x∉s₁, x∉s₂)
        -- を `simp` で使う
        have := hEq

        revert this
        intro h'

        have : X = Y := by

          exact eq_of_insert_eq_insert_of_not_mem haX haY hEq
        exact this
    have hsum_image :
        ∑ U ∈ (S.powerset.image (fun T => insert a T)), U.card
          =
        ∑ T ∈ S.powerset, (insert a T).card := by
      -- `sum_image` を用いる
      -- `sum_image` は： injOn → ∑ (image) g = ∑ g ∘ f
      -- ただし順序は左右逆になることが多いので `symm` で調整
      -- ここは左右そのまま
      refine (Finset.sum_image ?h).trans ?rfl
      · intro X hX Y hY hXY
        exact hinj hX hY hXY
    -- (insert a T).card = T.card + 1 （a∉T）
      exact rfl
    have hcard_ins :
        ∀ {T} (_ : T ∈ S.powerset), (insert a T).card = T.card + 1 := by
      intro T hT
      have haT : a ∉ T := by
        exact fun hmem => ha_notMem ((mem_powerset.mp hT) hmem)
      exact card_insert_of_notMem haT
    -- 以上を使って計算：
    calc
      ∑ T ∈ (insert a S).powerset, T.card
          = ∑ U ∈ S.powerset, U.card
            + ∑ U ∈ (S.powerset.image (fun T => insert a T)), U.card := by
              exact hsum_split
      _   = ∑ U ∈ S.powerset, U.card
            + ∑ T ∈ S.powerset, (insert a T).card := by
              exact congrArg (HAdd.hAdd (∑ U ∈ S.powerset, #U)) hsum_image
      _   = ∑ U ∈ S.powerset, U.card
            + (∑ T ∈ S.powerset, (T.card + 1)) := by
              refine congrArg (fun x => (∑ U ∈ S.powerset, U.card) + x) ?eq2
              -- 右側の「和の integrand」を書き換え
              refine Finset.sum_congr rfl ?stepRew
              intro T hT
              exact hcard_ins hT
      _   = (∑ U ∈ S.powerset, U.card)
            + (∑ T ∈ S.powerset, T.card) + (S.powerset.card) := by
              -- ∑(T.card+1) = ∑T.card + ∑1 = ∑T.card + card
              -- `sum_add_distrib` と `sum_const_nat`
              have := Finset.sum_add_distrib (s := S.powerset)
                        (f := fun T => T.card) (g := fun _ => 1)
              -- using を避け、`calc` で丁寧に
              -- まず和の分配
              have h1 :
                  ∑ T ∈ S.powerset, (T.card + 1)
                    = (∑ T ∈ S.powerset, T.card) + (∑ T ∈ S.powerset, (1 : Nat)) := by

                exact this
              -- 次に ∑ 1 = card
              have h2 :
                  ∑ T ∈ S.powerset, (1 : Nat) = S.powerset.card := by
                exact Eq.symm (card_eq_sum_ones S.powerset)

              simp_all only [mem_powerset, subset_refl, card_powerset, sum_const, smul_eq_mul,
                mul_one]
              ring
      _   = (2 : Nat) * (∑ U ∈ S.powerset, U.card) + (S.powerset.card) := by
              -- 上の行で同じ和が2つ出るので2倍
              simp_all only [mem_powerset, subset_refl, card_powerset, Nat.add_right_cancel_iff]
              ring
      _   = (2 : Nat) * (S.card * (2 : Nat) ^ (S.card - 1))
            + ((2 : Nat) ^ S.card) := by

              simp_all only [mem_powerset, subset_refl, card_powerset]
      _   = ((S.card + 1) * (2 : Nat) ^ S.card) := by

              exact powerset_nat #S
      _   = (insert a S).card * (2 : Nat) ^ ((insert a S).card - 1) := by
              -- (insert a S).card = S.card + 1 かつ
              -- (S.card + 1) - 1 = S.card（truncated subtraction でも成立）
              -- よって RHS の形に合致
              simp_all only [mem_powerset, subset_refl, add_tsub_cancel_right]

--Basicに移動の可能性あり。
noncomputable def Excess (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (B : Finset α) : Int := ((Free (Q := Q)).card : Int) * ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (2 : Int) * (∑ I ∈ fiber V R Q B, ((I \ B).card : Int))

lemma Excess_nonneg_pointwise
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α} (F_nonempty : (Free (Q := Q)).Nonempty) :
  0 ≤ Excess V R Q B := by
  classical
  -- 記号短縮
  let F := Free (Q := Q)
  let s := fiber V R Q B
  let f : Finset α → Finset α := fun I => I \ B
  -- `sum_image` のための単射性
  have hinj :
      ∀ {I} (_hI : I ∈ s) {J} (_hJ : J ∈ s), f I = f J → I = J := by
    intro I hI J hJ hEq
    exact diff_inj_on_fiber (V := V) (R := R) (Q := Q) (hI := hI) (hJ := hJ) (hEq := hEq)
  -- 画像は `F.powerset` に入る
  have himg_subset : s.image f ⊆ F.powerset :=
    image_diff_maps_to_powerset_free (V := V) (R := R) (Q := Q) (B := B)
  -- `∑ I∈s (I\B).card = ∑ U∈(s.image f) U.card`（Int 版）
  have hsum_image_int :
      ∑ U ∈ (s.image f), (U.card : Int) = ∑ I ∈ s, ((I \ B).card : Int) := by
    -- sum_image（Int 版）
    -- `sum_image` は `∑_{y ∈ s.image f} g y = ∑_{x ∈ s} g (f x)`。
    -- 右辺と左辺の向きを合わせるため `symm` を付ける。
    simp_all only [s, f, F]
    rw [sum_image]
    dsimp [Set.InjOn]
    exact fun ⦃x₁⦄ a ⦃x₂⦄ a_1 a_2 => hinj a a_1 a_2

  -- 包含からの単調性： `∑_{image} ≤ ∑_{powerset}`
  have hsubset_sum_le :
      ∑ U ∈ (s.image f), (U.card : Int) ≤ ∑ U ∈ F.powerset, (U.card : Int) := by
    -- 分解：S = A ∪ (S \ A) と `sum_union`、右項は非負
    have hdisj : Disjoint (s.image f) (F.powerset \ (s.image f)) := by
      exact disjoint_sdiff
    have hcover :
        (s.image f) ∪ (F.powerset \ (s.image f)) = F.powerset := by
      exact union_sdiff_of_subset himg_subset
    have hS :
        ∑ U ∈ F.powerset, (U.card : Int)
          = ∑ U ∈ (s.image f), (U.card : Int)
            + ∑ U ∈ (F.powerset \ (s.image f)), (U.card : Int) := by
      -- `sum_union` と全体被覆
      calc
        ∑ U ∈ F.powerset, (U.card : Int)
            = ∑ U ∈ (s.image f) ∪ (F.powerset \ (s.image f)), (U.card : Int) := by
                rw [hcover]
        _   = ∑ U ∈ (s.image f), (U.card : Int)
              + ∑ U ∈ (F.powerset \ (s.image f)), (U.card : Int) := by
                exact Finset.sum_union (by exact hdisj)
    -- 右項の非負
    have hnonneg :
        0 ≤ ∑ U ∈ (F.powerset \ (s.image f)), (U.card : Int) := by
      apply sum_nonneg_int
      intro U hU
      -- `U.card : Int ≥ 0`
      exact Int.natCast_nonneg U.card
    -- よって `∑_A ≤ ∑_S`
    have : ∑ U ∈ (s.image f), (U.card : Int)
              ≤ ∑ U ∈ (s.image f), (U.card : Int)
                + ∑ U ∈ (F.powerset \ (s.image f)), (U.card : Int) := by
      -- `a ≤ a + b`（b≥0）
      exact le_add_of_nonneg_right hnonneg
    -- 右辺を全体和に置換
    exact this.trans (by

      --
      have h' := hS
      -- 右辺へ適用
      -- `calc ... ≤ _ := this; _ = _ := hS`
      -- に書き換え直してもよいですが、
      -- ここでは `exact` で返します。
      --
      exact by

        exact Int.le_of_eq (id (Eq.symm hS))
    )
  -- ここまでで `∑_s (I\B).card ≤ ∑_{F.powerset} |U|`
  -- `sum_image` で左辺を戻す
  have hsum_core :
      ∑ I ∈ s, ((I \ B).card : Int)
        ≤ ∑ U ∈ F.powerset, (U.card : Int) := by

    have := hsubset_sum_le

    calc
      ∑ I ∈ s, ((I \ B).card : Int)
          = ∑ U ∈ (s.image f), (U.card : Int) := by
                exact hsum_image_int.symm
      _   ≤ ∑ U ∈ F.powerset, (U.card : Int) := by
                exact hsubset_sum_le
  -- パワーセットの恒等式
  have hPowSum :
      ∑ U ∈ F.powerset, (U.card : Int)
        = (F.card : Int) * (2 : Int) ^ (F.card - 1) := by
    let scp := sum_card_powerset_int F
    rw [mul_comm] at scp
    exact scp

  -- 整理：`2 * ∑_s ≤ |F| * 2^|F|`
  have hfinal :
      (2 : Int) * (∑ I ∈ s, ((I \ B).card : Int))
        ≤ (F.card : Int) * (2 : Int) ^ (F.card) := by
    -- 左辺 ≤ 2 * ∑_{F.powerset} |U|
    have hL :
        (2 : Int) * (∑ I ∈ s, ((I \ B).card : Int))
          ≤ (2 : Int) * (∑ U ∈ F.powerset, (U.card : Int)) :=
      Int.mul_le_mul_of_nonneg_left hsum_core (by decide)
    -- 右辺の指数を合わせる： 2 * (|F| * 2^(|F|-1)) = |F| * 2^|F|
    -- `hPowSum` を使って書き換え
    -- まず右辺へ適用
    have : (2 : Int) * (∑ U ∈ F.powerset, (U.card : Int))
            = (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1)) := by
      rw [hPowSum]
    -- 整式変形：`2 * (a * 2^(n-1)) = a * 2^n`
    -- `pow_succ` を使って安全に
    have : (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1))
            = (F.card : Int) * (2 : Int) ^ (F.card) := by

      calc
        (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1))
            = ((F.card : Int) * ((2 : Int) * (2 : Int) ^ (F.card - 1))) := by

                ac_rfl
        _   = (F.card : Int) * ((2 : Int) ^ (F.card)) := by

                have : (2 : Int) * (2 : Int) ^ (F.card - 1)
                          = (2 : Int) ^ (F.card - 1) * (2 : Int) := by
                  exact mul_comm _ _


                simp
                rw [this]
                by_cases h : F.card = 0
                case pos =>
                  simp_all only [card_empty, Nat.cast_zero, Nat.ofNat_pos, Int.mul_le_mul_left,
                    card_eq_zero, zero_tsub, pow_zero, one_mul, OfNat.ofNat_ne_one, or_true, s, f,
                    F]

                case neg =>
                  left
                  exact pow_sub_one_mul h 2

    -- 連鎖
    exact hL.trans (by

      have h1 : (2 : Int) * (∑ U ∈ F.powerset, (U.card : Int))
                  = (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1)) := by
        rw [hPowSum]
      have h2 : (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1))
                  = (F.card : Int) * (2 : Int) ^ (F.card) := by
        -- 上で示した等式を使う
        -- 直接 `exact` で
        exact
          calc
            (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1))
                = ((F.card : Int) * ((2 : Int) * (2 : Int) ^ (F.card - 1))) := by ac_rfl
            _   = (F.card : Int) * ((2 : Int) ^ (F.card)) := by

                  have : (2 * 2 ^ (#F - 1)) = 2 ^ #F := by
                    rw [mul_comm]
                    rw [pow_sub_one_mul]
                    exact card_ne_zero.mpr F_nonempty
                  simp_all [s, f, F]
                  apply Or.inl
                  exact mod_cast this


      -- 2段の書換で終了
      exact le_of_eq (by

        calc
          (2 : Int) * (∑ U ∈ F.powerset, (U.card : Int))
              = (2 : Int) * ((F.card : Int) * (2 : Int) ^ (F.card - 1)) := by exact h1
          _   = (F.card : Int) * (2 : Int) ^ (F.card) := by exact h2 ))

  have : 0 ≤ (F.card : Int) * (2 : Int) ^ (F.card)
                 - (2 : Int) * (∑ I ∈ s, ((I \ B).card : Int)) := by
    -- `a ≤ b` から `0 ≤ b - a`
    exact sub_nonneg.mpr hfinal

  change 0 ≤ ((Free (Q := Q)).card : Int) * ((2 : Nat) ^ (Free (Q := Q)).card : Int)
            - (2 : Int) * (∑ I ∈ fiber V R Q B, ((I \ B).card : Int))
  -- 右辺は今作った `this`
  exact this

lemma Excess_sum_nonneg
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (F_nonempty : (Free (Q := Q)).Nonempty):
  0 ≤ ∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B := by
  classical
  -- 各項が非負（8 を適用）
  apply sum_nonneg_int ((Rep (Q := Q)).powerset) (fun B => Excess V R Q B)
  intro B hB
  -- 8) は B の条件無しで成立するように修正済み

  exact Excess_nonneg_pointwise (V := V) (R := R) (Q := Q) (B := B) (F_nonempty := F_nonempty)

lemma sum_card_fiber_decompose
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  ∑ I ∈ fiber V R Q B, (I.card : Int)
    =
  (B.card : Int) * (fiber V R Q B).card
  + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int) := by
  classical
  -- 各 I に対し |I| = |B| + |I\B| を示して総和
  have h_each :
      ∀ {I} (_hI : I ∈ fiber V R Q B),
        (I.card : Int) = (B.card : Int) + ((I \ B).card : Int) := by
    intro I hI
    -- (1) I = B ∪ (I \ B)
    have hBI : B ⊆ I := (fiber_has_bounds (V := V) (R := R) (Q := Q) (hI := hI)).1
    have hIeq : B ∪ (I \ B) = I := union_sdiff_eq_of_subset hBI
    -- (2) B ⊆ Rep, (I\B) ⊆ Free, Rep ⟂ Free → B ⟂ (I\B)
    --    B ⊆ Rep は I ∩ Rep = B から従う
    have hcap : I ∩ Rep (Q := Q) = B :=
      (mem_fiber_iff (V := V) (R := R) (Q := Q)).1 hI |>.2
    have hBsubRep : B ⊆ Rep (Q := Q) := by
      -- `B = I ∩ Rep` なので自明
      -- `rw [← hcap]; exact inter_subset_right`
      -- （`simpa using` は使わない）
      have : I ∩ Rep (Q := Q) ⊆ Rep (Q := Q) := inter_subset_right

      have hb : B ⊆ Rep (Q := Q) := by
        -- 書換
        -- （Lean により `rw` が嫌う場合は `calc` で）
        --
        -- ここでは `calc` を使います
          subst hcap
          simp_all only [inter_subset_right, inter_subset_left, sdiff_inter_self_left]

      exact hb
    have hIminusB_subFree : I \ B ⊆ Free (Q := Q) :=
      fiber_diff_subset_free (V := V) (R := R) (Q := Q) (hI := hI)
    have hdisj : Disjoint B (I \ B) := by
      -- B ⊆ Rep, (I\B) ⊆ Free, Rep ⟂ Free
      have hRepFree := disjoint_Rep_Free (V := V) (R := R) (Q := Q)
      exact hRepFree.mono_left hBsubRep |>.mono_right hIminusB_subFree
    -- (3) card の加法
    -- `card_union` は Disjoint があれば加法
    -- `I = B ∪ (I\B)` に差し替えてからカードを足し算へ
    have : (I.card : Int) = ((B ∪ (I \ B)).card : Int) := by

      have hNat : I.card = (B ∪ (I \ B)).card := by
        -- `hIeq : B ∪ (I \ B) = I`
        exact congrArg Finset.card hIeq.symm
      -- Int へ
      exact congrArg (fun n : Nat => (n : Int)) hNat
    -- 加法（disjoint）
    have hCardAdd :
        ((B ∪ (I \ B)).card : Int)
          = (B.card : Int) + ((I \ B).card : Int) := by
      -- Nat 版 `card_disjoint_union` 相当：
      -- `card (s ∪ t) + card (s ∩ t) = card s + card t`
      -- かつ `s ∩ t = ∅`（disjoint）→ 左の第2項 0
      -- まず Nat で示し、その後 Int へ
      have hNat :
          (B ∪ (I \ B)).card + (B ∩ (I \ B)).card
            = B.card + (I \ B).card :=
        card_union_add_card_inter _ _
      -- `B ∩ (I \ B)` は空
      have hcap0 : (B ∩ (I \ B)).card = 0 := by
        -- `Disjoint.card_inter_eq_zero` があれば一発
        -- なければ要素なしを示してから `card_eq_zero.mpr`
        subst hcap
        simp_all only [inter_subset_left, sdiff_inter_self_left, inter_subset_right, inter_assoc, inter_sdiff_self,
          inter_empty, card_empty, add_zero, card_inter_add_card_sdiff]

      -- 以上から
      have : (B ∪ (I \ B)).card = B.card + (I \ B).card := by

        have := hNat

        have h' : (B ∪ (I \ B)).card = B.card + (I \ B).card := by

          have := hNat

          rw [hcap0] at this

          exact this
        -- 完成
        exact h'
      -- Int へキャスト
      exact congrArg (fun n : Nat => (n : Int)) this
    -- まとめ
    calc
      (I.card : Int)
          = ((B ∪ (I \ B)).card : Int) := by exact this
      _   = (B.card : Int) + ((I \ B).card : Int) := by exact hCardAdd
  -- 上の等式を ∑ に積み上げる
  have :
      ∑ I ∈ fiber V R Q B, (I.card : Int)
        = ∑ I ∈ fiber V R Q B, ((B.card : Int) + ((I \ B).card : Int)) := by
    refine sum_congr rfl ?h
    intro I hI
    exact (h_each hI)
  -- 右辺を分配して、定数和をまとめる
  -- ∑ ((B.card) + t_I) = (B.card)*|fiber| + ∑ t_I
  -- `sum_add_distrib` と `sum_const` 系を使う
  -- まず分配
  have :
      ∑ I ∈ fiber V R Q B, ((B.card : Int) + ((I \ B).card : Int))
        = (∑ I ∈ fiber V R Q B, (B.card : Int))
          + (∑ I ∈ fiber V R Q B, ((I \ B).card : Int)) := by
    exact sum_add_distrib
  -- 定数和の評価
  have hconst :
      ∑ I ∈ fiber V R Q B, (B.card : Int)
        = (B.card : Int) * (fiber V R Q B).card := by

    have := sum_const (B.card : Int) (s := fiber V R Q B)

    have hsc := this

    simp
    exact Int.mul_comm ↑(#(fiber V R Q B)) ↑(#B)
  -- 仕上げ
  -- 最初の等式で左辺を書き換え，次に定数和を評価
  calc
    ∑ I ∈ fiber V R Q B, (I.card : Int)
        = (∑ I ∈ fiber V R Q B, (B.card : Int))
          + (∑ I ∈ fiber V R Q B, ((I \ B).card : Int)) := by

            have h1 :
              ∑ I ∈ fiber V R Q B, (I.card : Int)
                = ∑ I ∈ fiber V R Q B, ((B.card : Int) + ((I \ B).card : Int)) := by

                  exact
                    (by
                      simp_all only [sum_const, Int.nsmul_eq_mul])


            exact
              by
                -- 2段の置換を順番に当てる版
                -- まず h1
                have h1' :
                  ∑ I ∈ fiber V R Q B, (I.card : Int)
                    = ∑ I ∈ fiber V R Q B, ((B.card : Int) + ((I \ B).card : Int)) := by
                      simp_all only [sum_const, Int.nsmul_eq_mul]
                -- 次に分配
                have h2' :
                  ∑ I ∈ fiber V R Q B, ((B.card : Int) + ((I \ B).card : Int))
                    = (∑ I ∈ fiber V R Q B, (B.card : Int))
                      + (∑ I ∈ fiber V R Q B, ((I \ B).card : Int)) := by
                    exact sum_add_distrib
                -- 連鎖
                exact (Eq.trans h1' h2')
    _   = (B.card : Int) * (fiber V R Q B).card
          + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int) := by
            -- 定数和の評価を左側に適用
            -- `hconst`
            --
            -- `rw [hconst]` で OK
            --
            -- 実行：
            simp_all only [sum_const, Int.nsmul_eq_mul]

lemma sum_linearize_card_sub_const_on_fiber
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
    =
  (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
    - (V.card : Int) * (fiber V R Q B).card := by
  -- 既存の一般形を S = fiber V R Q B に適用
  exact sum_linearize_card_sub_const (V := V) (S := fiber V R Q B)

lemma fiber_block_linearized
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
  =
  (2 : Int) * (B.card : Int) * (fiber V R Q B).card
  + (2 : Int) * (∑ I ∈ fiber V R Q B, ((I \ B).card : Int))
  - (V.card : Int) * (fiber V R Q B).card := by
  classical
  -- A2’ で線形化
  have hlin :
      ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
        =
      (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        - (V.card : Int) * (fiber V R Q B).card :=
    sum_linearize_card_sub_const_on_fiber (V := V) (R := R) (Q := Q) (B := B)
  -- A1 で Σ|I| を分解
  have hsumI :
      ∑ I ∈ fiber V R Q B, (I.card : Int)
        =
      (B.card : Int) * (fiber V R Q B).card
      + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int) :=
    sum_card_fiber_decompose (V := V) (R := R) (Q := Q) (B := B)
  -- 代入して整理
  -- 2 * ((|B|)*|fiber| + Σ|I\B|) - |V|*|fiber|
  -- = (2*|B|)*|fiber| + 2*Σ|I\B| - |V|*|fiber|
  have :
      (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
        - (V.card : Int) * (fiber V R Q B).card
        =
      (2 : Int) * (B.card : Int) * (fiber V R Q B).card
      + (2 : Int) * (∑ I ∈ fiber V R Q B, ((I \ B).card : Int))
      - (V.card : Int) * (fiber V R Q B).card := by

    rw [hsumI]
    -- 2) 分配
    -- 2 * (A + B) = 2*A + 2*B
    have : (2 : Int) * ((B.card : Int) * (fiber V R Q B).card
            + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int))
            =
          (2 : Int) * ((B.card : Int) * (fiber V R Q B).card)
          + (2 : Int) * (∑ I ∈ fiber V R Q B, ((I \ B).card : Int)) := by
      exact mul_add (2 : Int)
            ((B.card : Int) * (fiber V R Q B).card)
            (∑ I ∈ fiber V R Q B, ((I \ B).card : Int))
    -- この `this` を適用
    -- ただし `rw` で置換
    --
    rw [this]
    -- 3) (2 : Int) * ((B.card : Int) * s) = (2*|B|) * s
    -- `mul_assoc` を 1 回使えばよい
    --
    -- 最終形はゴールと一致するため、ここは `ac_rfl` でも可
    --
    -- ここでは `ac_rfl` を使用
    --
    ac_rfl
  -- 以上を合成
  exact hlin.trans this

  lemma NDS2_family_partition_by_fiber
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  NDS2 V (family V R)
    =
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int)) := by
  classical
  -- 定義に戻し，既存の分割補題を適用
  change
    ∑ I ∈ family V R, ((2 : Int) * (I.card : Int) - (V.card : Int))
      =
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
  -- φ を指定して分割
  exact
    (sum_family_partition_as_fibers (V := V) (R := R) (Q := Q)
      (φ := fun I => (2 : Int) * (I.card : Int) - (V.card : Int)))

lemma rewrite_block_with_V_free
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  (2 : Int) ^ (Free (Q := Q)).card
    * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
  =
  (2 : Int) ^ (Free (Q := Q)).card
    * ((2 : Int) * (B.card : Int) - (V.card : Int))
  + ((Free (Q := Q)).card : Int) * (2 : Int) ^ (Free (Q := Q)).card := by
  classical
  -- `V.card = Rep.card + Free.card` を使い，右の第2項を“差分”として抽出
  -- まず `-(Rep.card) = -(V.card) + Free.card`
  have hcard :
      - ((Rep (Q := Q)).card : Int)
        = - (V.card : Int) + ((Free (Q := Q)).card : Int) := by
    -- `card_Rep_add_card_Free : Rep.card + Free.card = V.card`
    -- を Int へ上げて並べ替え
    have hNat := card_Rep_add_card_Free (V := V) (R := R) (Q := Q)
    -- Int へキャスト
    have hInt : ((Rep (Q := Q)).card : Int) + ((Free (Q := Q)).card : Int)
                  = (V.card : Int) :=
      congrArg (fun n : Nat => (n : Int)) hNat

    have : ((Free (Q := Q)).card : Int)
              = -((Rep (Q := Q)).card : Int) + (V.card : Int) := by
      -- `hInt : Rep + Free = V`
      -- `add_left_neg_self` を使う
      -- `by` で書きます
      calc
        ((Free (Q := Q)).card : Int)
            = (0 : Int) + ((Free (Q := Q)).card : Int) := by
                exact (zero_add _).symm
        _   = (- ((Rep (Q := Q)).card : Int) + ((Rep (Q := Q)).card : Int))
              + ((Free (Q := Q)).card : Int) := by
                -- -a + a = 0 を左に挿入
                -- `add_left_neg_self` は `a + (-a) = 0` の形なので，
                -- ここは `add_comm` を適宜使って整えます。
                -- 直接は `by` で：
                have : (- ((Rep (Q := Q)).card : Int) + ((Rep (Q := Q)).card : Int))
                        = (0 : Int) := by
                  exact Int.add_left_neg ↑(#(Rep Q))
                -- 置換
                -- 0 + Free への書換えに使うため，この形で残します
                -- ここは一旦そのまま置く
                simp_all only [neg_add_cancel, zero_add]
        _   = - ((Rep (Q := Q)).card : Int)
              + (((Rep (Q := Q)).card : Int) + ((Free (Q := Q)).card : Int)) := by
                exact add_assoc _ _ _
        _   = - ((Rep (Q := Q)).card : Int) + (V.card : Int) := by

                exact congrArg (fun t : Int => - ((Rep (Q := Q)).card : Int) + t) hInt

    have htmp :
        - ((Rep (Q := Q)).card : Int)
          = - (V.card : Int) + ((Free (Q := Q)).card : Int) := by
      -- `this : Free = -Rep + V`
      -- 左右を `Eq.symm` と `add_comm`/`add_left_comm` で並べ替えて取得
      -- `calc` で安全に：
      calc
        - ((Rep (Q := Q)).card : Int)
            = - (V.card : Int) + (V.card : Int)
              - ((Rep (Q := Q)).card : Int) := by

                ring -- （もし `ring` を避けたい場合は加法結合法で展開してください）
        _ = - (V.card : Int) + ((Free (Q := Q)).card : Int) := by

            simp_all only [add_neg_cancel_left, neg_add_cancel, zero_sub, neg_add_cancel_comm_assoc]

 -- これで `hcard` が欲しい形になりました
    exact htmp

  calc
    (2 : Int) ^ (Free (Q := Q)).card
      * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
        = (2 : Int) ^ (Free (Q := Q)).card
          * ((2 : Int) * (B.card : Int) + ( - (V.card : Int) + ((Free (Q := Q)).card : Int))) := by
            -- 括弧内の `-Rep = -V + Free` を置換
            -- `a - Rep = a + (-Rep)`
            -- そこへ `hcard` を代入
            -- ここは `rw` 2発
            --
            -- まず `a - Rep = a + (-Rep)`
            have : ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
                      = ((2 : Int) * (B.card : Int) + ( - ((Rep (Q := Q)).card : Int))) := by
              exact sub_eq_add_neg _ _

            have h1 := this

            exact by

              rw [sub_eq_add_neg]
              rw [hcard]
    _ = (2 : Int) ^ (Free (Q := Q)).card
          * ((2 : Int) * (B.card : Int) - (V.card : Int))
        + ((Free (Q := Q)).card : Int) * (2 : Int) ^ (Free (Q := Q)).card := by
          -- 分配法則
          -- 2^F * (A + Free) = 2^F*A + 2^F*Free
          -- 後者は `((Free.card : Int) * 2^F)` と等しい（可換なので ac_rfl でOK）
          have : (2 : Int) ^ (Free (Q := Q)).card
                    * ((2 : Int) * (B.card : Int) + ( - (V.card : Int)))
                  = (2 : Int) ^ (Free (Q := Q)).card
                      * ((2 : Int) * (B.card : Int) - (V.card : Int)) := by
            -- `a + (-b) = a - b`
            -- ここは `by` 1行
            exact by rfl
          -- 全体を分配
          -- `mul_add` と，末尾の可換で並べ替え
          -- 実装：
          calc
            (2 : Int) ^ (Free (Q := Q)).card
              * ((2 : Int) * (B.card : Int) + ( - (V.card : Int) + ((Free (Q := Q)).card : Int)))
                =
              (2 : Int) ^ (Free (Q := Q)).card
                * ((2 : Int) * (B.card : Int) + ( - (V.card : Int)))
              + (2 : Int) ^ (Free (Q := Q)).card
                * (((Free (Q := Q)).card : Int)) := by
                    simp_all only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, false_and, or_false]
                    ring
            _ =
                (2 : Int) ^ (Free (Q := Q)).card
                  * ((2 : Int) * (B.card : Int) - (V.card : Int))
              + ((Free (Q := Q)).card : Int) * (2 : Int) ^ (Free (Q := Q)).card := by
                  -- 前半は上の this で置換、後半は可換で並べ替え
                  -- `mul_comm` を使う
                  -- 実装：
                  --
                  -- まず前半
                  --
                  have hfront :
                      (2 : Int) ^ (Free (Q := Q)).card
                        * ((2 : Int) * (B.card : Int) + ( - (V.card : Int)))
                        =
                      (2 : Int) ^ (Free (Q := Q)).card
                        * ((2 : Int) * (B.card : Int) - (V.card : Int)) := by
                    exact this
                  -- 後半
                  have hback :
                      (2 : Int) ^ (Free (Q := Q)).card
                        * (((Free (Q := Q)).card : Int))
                        =
                      ((Free (Q := Q)).card : Int) * (2 : Int) ^ (Free (Q := Q)).card := by
                    exact mul_comm _ _
                  -- 連結
                  exact by
                    rw [hfront, hback]

/-- 「a を rep+free に展開した」純代数形。
LHS と RHS は同じ多項式なので `ring` で閉じます。 -/
private lemma rearrange_block_core_ring'
  (Fpow s rep free b D : Int) :
  (Fpow * b - s * b) + ((rep + free) * s - Fpow * rep) - (2 : Int) * D
  =
  (s - Fpow) * ((rep + free) - b) + (Fpow * free - (2 : Int) * D) := by
  ring

/-- 上の補題を `a = rep + free` で包み直した版。
`a` を使う側（元ファイル）からはこの形が便利です。 -/
private lemma rearrange_block_core_ring
  (Fpow a b s rep free D : Int) (hVR : a = rep + free) :
  (Fpow * b - s * b) + (a * s - Fpow * rep) - (2 : Int) * D
  =
  (s - Fpow) * (a - b) + (Fpow * free - (2 : Int) * D) := by
  -- 両辺とも `a` を `rep+free` に書き換えて `ring` 補題を使う
  have h := rearrange_block_core_ring' (Fpow := Fpow) (s := s) (rep := rep) (free := free) (b := b) (D := D)

  simp_all only



private lemma sum_card_on_fiber_decompose
  (V : Finset α) (R : Finset (α × α × α)) (Q : SCCQuot α V R) {B : Finset α} :
  ∑ I ∈ fiber V R Q B, (I.card : Int)
    =
  ((fiber V R Q B).card : Int) * (B.card : Int)
  + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int) := by
  classical
  -- 記号の短縮
  let s := fiber V R Q B

  -- 各 I∈s で |I| = |B| + |I\B|
  have h_each :
      ∀ {I} (_hI : I ∈ s),
        (I.card : Int) = (B.card : Int) + ((I \ B).card : Int) := by
    intro I hI
    -- fiber から B ⊆ I
    have hBI : B ⊆ I := (fiber_has_bounds (V := V) (R := R) (Q := Q) (B := B) (I := I) (hI := hI)).1
    -- I = B ∪ (I\B)
    have hIeq : B ∪ (I \ B) = I := union_sdiff_eq_of_subset hBI
    -- B と (I\B) は互いに素
    have hdisj : Disjoint B (I \ B) := by
      -- 一般に `Disjoint s (t \ s)`
      exact disjoint_sdiff
    -- Nat で |I| = |B| + |I\B| を作ってから Int に上げる
    have hNat_union :
        (B ∪ (I \ B)).card + (B ∩ (I \ B)).card
          = B.card + (I \ B).card :=
      card_union_add_card_inter _ _
    have hcap0 : (B ∩ (I \ B)).card = 0 := by
      simp_all only [union_sdiff_self_eq_union, union_eq_right, inter_sdiff_self, card_empty, add_zero, s]
    have hNat : I.card = B.card + (I \ B).card := by
      -- `I.card = (B ∪ (I\B)).card`
      have : I.card = (B ∪ (I \ B)).card := by
        exact congrArg Finset.card hIeq.symm
      -- 左の等式 `card_union_add_card_inter` に `hcap0` を代入して
      -- `(B ∪ (I\B)).card = B.card + (I\B).card`
      have hsum : (B ∪ (I \ B)).card = B.card + (I \ B).card := by

        have := hNat_union
        -- 代入
        -- `rw` を嫌う場合は `simp [hcap0] at this` でも同じですが、ここは `rw` で。
        have : (B ∪ (I \ B)).card = B.card + (I \ B).card := by
          -- 左辺に `hcap0` を入れて消去
          -- (s∪t).card + 0 = s.card + t.card なので成立
          simpa [hcap0] using this
        exact this
      -- 連結
      exact this.trans hsum
    -- Int に上げる
    exact congrArg (fun n : Nat => (n : Int)) hNat

  -- いま得た各 I の等式を ∑ に積み上げる
  have hsum :
      ∑ I ∈ s, (I.card : Int)
        = ∑ I ∈ s, ((B.card : Int) + ((I \ B).card : Int)) := by
    refine sum_congr rfl ?h
    intro I hI
    exact h_each hI

  -- 和を分配：∑(定数 + 項) = ∑定数 + ∑項
  have hsplit :
      ∑ I ∈ s, ((B.card : Int) + ((I \ B).card : Int))
        = (∑ I ∈ s, (B.card : Int))
          + (∑ I ∈ s, ((I \ B).card : Int)) := by
    exact sum_add_distrib

  -- 定数和：∑_{I∈s} (B.card) = (|s| : ℤ) * |B|
  have hconst :
      ∑ I ∈ s, (B.card : Int)
        = ((s.card : Int) * (B.card : Int)) := by
    -- `sum_const` → `nsmul` → 掛け算
    have hsc :
        ∑ I ∈ s, (B.card : Int) = s.card • (B.card : Int) := by
      simp_all only [sum_const, Int.nsmul_eq_mul, s]
    have hmul :
        s.card • (B.card : Int) = (s.card : Int) * (B.card : Int) :=
      nsmul_eq_mul _ _
    exact hsc.trans hmul

  -- 仕上げ：式を順に置換
  calc
    ∑ I ∈ s, (I.card : Int)
        = ∑ I ∈ s, ((B.card : Int) + ((I \ B).card : Int)) := by
            exact hsum
    _   = (∑ I ∈ s, (B.card : Int))
          + (∑ I ∈ s, ((I \ B).card : Int)) := by
            exact hsplit
    _   = ((s.card : Int) * (B.card : Int))
          + ∑ I ∈ s, ((I \ B).card : Int) := by
            -- 定数和を評価
            rw [hconst]
    _   = ((fiber V R Q B).card : Int) * (B.card : Int)
          + ∑ I ∈ fiber V R Q B, ((I \ B).card : Int) := by
            -- s = fiber ...
            rfl

/-- ブロックごとの恒等式（正しい版）：先頭の `card` は `Rep` -/
private lemma delta_block_eq_negDebt_plus_Excess_pointwise
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  ((2 : Int) ^ (Free (Q := Q)).card)
      * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
  - ( ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int)) )
  =
  - Debt V R Q B + Excess V R Q B := by
  classical
  -- 省略記法
  set F := Free (Q := Q)
  set s := fiber V R Q B
  set Fpow : Int := ((2 : Nat) ^ F.card : Int)
  set a : Int := (V.card : Int)
  set b : Int := (2 : Int) * (B.card : Int)
  -- D := Σ_{I∈s} |I \ B|
  set D : Int := ∑ I ∈ s, ((I \ B).card : Int)

  -- 和の線形化：  Σ (2|I| - a) = 2 Σ|I| - a * |s|
  have hlin :
      ∑ I ∈ s, ((2 : Int) * (I.card : Int) - a)
        = (2 : Int) * (∑ I ∈ s, (I.card : Int)) - a * s.card :=
    sum_linearize_card_sub_const (V := V) s

  -- 繊維上の分解：  Σ|I| = |s|*|B| + Σ|I\B|
  have hsplit :
      ∑ I ∈ s, (I.card : Int)
        = (s.card : Int) * (B.card : Int) + ∑ I ∈ s, ((I \ B).card : Int) := by
    -- （これは先に証明済みの B 系補題を使ってください。
    --  例えば `sum_card_on_fiber_decompose` のような名前で用意したもの。
    --  未定なら、各 I について |I| = |B| + |I\B| を合計して示せます。）
    exact sum_card_on_fiber_decompose (V := V) (R := R) (Q := Q) (B := B)

  -- 左辺を機械的に変形


  calc
    Fpow * (b - (Rep (Q := Q)).card)
        - (∑ I ∈ s, ((2 : Int) * (I.card : Int) - a))
        =
      Fpow * (b - (Rep (Q := Q)).card)
        - ( (2 : Int) * (∑ I ∈ s, (I.card : Int)) - a * s.card ) := by
          rw [hlin]
    _ = Fpow * (b - (Rep (Q := Q)).card)
          - ( (2 : Int) * ( (s.card : Int) * (B.card : Int)
                            + ∑ I ∈ s, ((I \ B).card : Int) )
              - a * s.card ) := by
          -- hsplit を代入
          rw [hsplit]
    _ =
      -- 展開：2 を分配して整理
      (Fpow * b - Fpow * (Rep (Q := Q)).card)
        - ( (2 : Int) * (s.card : Int) * (B.card : Int)
            + (2 : Int) * (∑ I ∈ s, ((I \ B).card : Int))
            - a * s.card ) := by
          ring
    _ =
      -- カッコを外しつつまとめる
      (Fpow * b - (2 : Int) * (s.card : Int) * (B.card : Int))
        + (a * s.card - Fpow * (Rep (Q := Q)).card)
        - (2 : Int) * (∑ I ∈ s, ((I \ B).card : Int)) := by
          ring
    _ =
      -- -Debt + Excess の形に並べ替える
      ((s.card : Int) - Fpow) * (a - b)
        + (Fpow * (F.card : Int) - (2 : Int) * D) := by

      have hb : (2 : Int) * (s.card : Int) * (B.card : Int) = (s.card : Int) * ((2 : Int) * (B.card : Int)) := by ac_rfl
      rw [hb]
      apply rearrange_block_core_ring (Fpow := Fpow) (a := a) (b := b) (s := (s.card : Int)) (rep := (Rep (Q := Q)).card) (free := (F.card : Int)) (D := D)
      exact cardV_as_Rep_plus_Free

    _ =
      -- `(s.card : Int) - Fpow = -(Fpow - (s.card : Int))` を使って Debt を出す
      - ( (Fpow - (s.card : Int)) * (a - b) )
        + (Fpow * (F.card : Int) - (2 : Int) * D) := by
      ring
    _ =
      - Debt V R Q B + Excess V R Q B := by
      -- 定義そのまま
      simp [Debt, Excess, F, s, Fpow, a, b, D]
      exact Int.mul_comm (2 ^ #(Free Q)) ↑(#(Free Q))

/-- `∑_{B⊆Rep} (2|B| - |Rep|) = 0`（Int 版）。 -/
private lemma sum_over_powerset_block_coeff_zero
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
  = 0 := by
  classical
  -- 線形化
  have hlin :=
    sum_linearize_card_sub_const (V := (Rep (Q := Q)))
      ((Rep (Q := Q)).powerset)
  -- ここで V := Rep を入れた形に直す
  have hlin' :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ((2 : Int) * (B.card : Int) - ((Rep (Q := Q)).card : Int))
        =
      (2 : Int) * (∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int))
        - ((Rep (Q := Q)).card : Int) * (Rep (Q := Q)).powerset.card := by
    -- hlin は「任意の V, S」対応なのでそのまま使える
    -- （上の `hlin` は V := Rep, S := Rep.powerset）
    exact hlin
  -- `∑ (|B|)` の評価（Int 版）：|Rep| * 2^{|Rep|-1}
  have hsum_card_int :
      ∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int)
        = ((Rep (Q := Q)).card : Int)
          * ((2 : Nat) ^ ((Rep (Q := Q)).card - 1) : Int) := by
    classical
    -- Nat 版 `sum_card_powerset` を Int へ持ち上げる
    -- まず Nat 版
    have h_nat : ∑ B ∈ (Rep (Q := Q)).powerset, B.card
                  = (Rep (Q := Q)).card * (2 : Nat) ^ ((Rep (Q := Q)).card - 1) := by
      let scp := sum_card_powerset_nat (Rep (Q := Q))
      exact scp

    -- ring_hom で和を写像： `ℕ → ℤ`
    have h_cast :
        ((∑ B ∈ (Rep (Q := Q)).powerset, B.card : Nat) : Int)
          = ∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int) := by
      -- `map_sum` を使う

      let ms := (map_sum (Nat.castRingHom Int) (fun B : Finset α => (B.card : Nat))
          ((Rep (Q := Q)).powerset))
      exact ms
    -- 右辺も Int へ
    have h_rhs :
        (( (Rep (Q := Q)).card * (2 : Nat) ^ ((Rep (Q := Q)).card - 1) ) : Int)
          =
        ((Rep (Q := Q)).card : Int) * ((2 : Nat) ^ ((Rep (Q := Q)).card - 1) : Int) := by

      ring

    have := congrArg (fun n : Nat => (n : Int)) h_nat
    -- `((∑ B card) : Int) = ((|Rep|*2^{|Rep|-1}) : Int)`
    -- 左を h_cast で，右を h_rhs で置換
    -- 仕上げ
    exact (by

      have := this

      exact
        (by
          -- 左
          have h1 := this

          simp_all only [card_powerset, Nat.cast_pow, Nat.cast_ofNat, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, Nat.cast_mul]
          )
    )
  -- `|powerset| = 2^{|Rep|}`（Int 版）
  have hcardPow :
      (((Rep (Q := Q)).powerset.card : Nat) : Int)
        = ((2 : Nat) ^ (Rep (Q := Q)).card : Int) := by
    exact card_powerset_pow_int (S := (Rep (Q := Q)))
  -- まとめ：線形化に `hsum_card_int` と `hcardPow` を代入して 0
  calc
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
      =
    (2 : Int) * (∑ B ∈ (Rep (Q := Q)).powerset, (B.card : Int))
      - ((Rep (Q := Q)).card : Int) * (Rep (Q := Q)).powerset.card := by
        exact hlin'
  _ = (2 : Int) * ( ((Rep (Q := Q)).card : Int)
                  * ((2 : Nat) ^ ((Rep (Q := Q)).card - 1) : Int))
      - ((Rep (Q := Q)).card : Int)
          * (( (Rep (Q := Q)).powerset.card : Nat) : Int) := by

        rw [hsum_card_int]
  _ = (2 : Int) * ( ((Rep (Q := Q)).card : Int)
                  * ((2 : Nat) ^ ((Rep (Q := Q)).card - 1) : Int))
      - ((Rep (Q := Q)).card : Int)
          * ((2 : Nat) ^ (Rep (Q := Q)).card : Int) := by
        -- powerset.card を 2^{|Rep|} に
        -- `rw [hcardPow]`
        rw [hcardPow]
  _ = 0 := by
        -- 2 * (x * 2^{n-1})  -  x * 2^n  = 0
        -- 整式計算
        ring_nf
        by_cases h : (Rep (Q := Q)).card ≥ 1
        case pos =>
          rw [mul_comm]
          rw [←mul_assoc]
          rw [mul_comm]
          rw [←mul_assoc]
          --rw [mul_comm ((@Nat.cast ℤ instNatCastInt) (#(Rep Q))) (2 ^ (#(Rep Q) - 1))]
          let ps := pow_succ (2 : Nat) ((Rep (Q := Q)).card - 1)
          have :#(Rep Q) - 1 + 1 = #(Rep Q) := by
            exact Nat.sub_add_cancel h
          rw [this] at ps

          rw [mul_comm ((@Nat.cast ℤ instNatCastInt) (#(Rep Q))) (2 ^ #(Rep Q))]
          simp_all only [Nat.cast_ofNat, card_powerset, Nat.cast_mul, Nat.cast_pow, sum_sub_distrib, sum_const, Int.nsmul_eq_mul,
            ge_iff_le, one_le_card, card_pos, Nat.pow_pred_mul, Nat.sub_add_cancel, sub_self]

        case neg =>
          simp_all only [Nat.cast_ofNat, card_powerset, Nat.cast_pow, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, ge_iff_le,
            one_le_card, not_nonempty_iff_eq_empty, card_empty, Nat.cast_zero, zero_tsub, pow_zero, mul_one, zero_mul, sub_self]

/-- powerset×fiber での差の総和分配 -/
private lemma sum_sub_distrib_over_powerset_fiber
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (α × α × α)) (Q : SCCQuot α V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ( ((2 : Int) ^ (Free (Q := Q)).card)
          * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
        - ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int)) )
  =
    (∑ B ∈ (Rep (Q := Q)).powerset,
        ((2 : Int) ^ (Free (Q := Q)).card)
          * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
    -
    (∑ B ∈ (Rep (Q := Q)).powerset,
        ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
  classical
  -- 記号短縮
  let S := (Rep (Q := Q)).powerset
  set f :=
    (fun B : Finset α =>
      ((2 : Int) ^ (Free (Q := Q)).card)
        * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) with hf
  set g :=
    (fun B : Finset α =>
      ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))) with hg
  -- 形を一般補題に合わせる
  change
    ∑ B ∈ S, (f B - g B)
      =
    (∑ B ∈ S, f B) - (∑ B ∈ S, g B)
  -- 一般事実で終了
  exact sum_sub_distrib f g

private lemma sum_over_powerset_fiber_eq_sum_family
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (φ : Finset α → Int) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ∑ I ∈ fiber V R Q B, φ I
  =
  ∑ I ∈ family V R, φ I := by
  classical
  -- 既存の分割補題を対称向きで使うだけ
  have h := sum_family_partition_as_fibers
              (V := V) (R := R) (Q := Q) (φ := φ)
  exact h.symm

private lemma double_sum_over_fiber_eq_NDS2
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset,
      ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
  =
  NDS2 V (family V R) := by
  classical
  -- 一般 φ 版から、φ := fun I => 2|I| - |V|
  have h := sum_over_powerset_fiber_eq_sum_family
              (V := V) (R := R) (Q := Q)
              (φ := fun I => (2 : Int) * (I.card : Int) - (V.card : Int))
  -- 定義に戻す
  calc
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ∑ I ∈ fiber V R Q B,
            ((2 : Int) * (I.card : Int) - (V.card : Int))
        = ∑ I ∈ family V R,
            ((2 : Int) * (I.card : Int) - (V.card : Int)) := by
              exact h
    _ = NDS2 V (family V R) := by
          rfl


private lemma NDS2_eq_sumDebt_minus_sumExcess
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  NDS2 V (family V R)
    =
  (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
  - (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) := by
  classical
  -- L3’ を各 B に適用して総和
  have hδ :
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( ((2 : Int) ^ (Free (Q := Q)).card)
            * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
          - ∑ I ∈ fiber V R Q B,
              ((2 : Int) * (I.card : Int) - (V.card : Int)) )
      =
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( - Debt V R Q B + Excess V R Q B ) := by
    -- 項ごとに一致
    refine sum_congr rfl ?h
    intro B hB
    -- まさに pointwise 等式
    exact
      (delta_block_eq_negDebt_plus_Excess_pointwise
        (V := V) (R := R) (Q := Q) (B := B))
  -- 左辺を「ブロック係数の総和 − R 側 NDS2」に整理
  have hS :
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( ((2 : Int) ^ (Free (Q := Q)).card)
            * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
          - ∑ I ∈ fiber V R Q B,
              ((2 : Int) * (I.card : Int) - (V.card : Int)) )
      =
    ( (2 : Int) ^ (Free (Q := Q)).card
        * ∑ B ∈ (Rep (Q := Q)).powerset,
            ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) )
      - NDS2 V (family V R) := by
    -- `sum_sub_distrib` と B1 の分割を使用
    -- まず「差の総和 = 総和の差」
    have hsplit :
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ( ((2 : Int) ^ (Free (Q := Q)).card)
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
            - ∑ I ∈ fiber V R Q B,
                ((2 : Int) * (I.card : Int) - (V.card : Int)) )
        =
      (∑ B ∈ (Rep (Q := Q)).powerset,
          ((2 : Int) ^ (Free (Q := Q)).card)
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        -
      (∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ fiber V R Q B,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) := by

      exact sum_sub_distrib_over_powerset_fiber (V := V) (R := R) (Q := Q)

    -- 右辺第2項は B1 で `NDS2 V (family V R)` に
    -- 右辺第1項は定数 `2^{|Free|}` を外へ
    calc
      ∑ B ∈ (Rep (Q := Q)).powerset,
          ( ((2 : Int) ^ (Free (Q := Q)).card)
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
            - ∑ I ∈ fiber V R Q B,
                ((2 : Int) * (I.card : Int) - (V.card : Int)) )
        =
      (∑ B ∈ (Rep (Q := Q)).powerset,
          ((2 : Int) ^ (Free (Q := Q)).card)
              * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        -
      (∑ B ∈ (Rep (Q := Q)).powerset,
          ∑ I ∈ fiber V R Q B,
              ((2 : Int) * (I.card : Int) - (V.card : Int))) := by
        exact hsplit
    _ =
      ( (2 : Int) ^ (Free (Q := Q)).card
          * ∑ B ∈ (Rep (Q := Q)).powerset,
              ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) )
      - NDS2 V (family V R) := by

        have hB1' :
          ∑ B ∈ (Rep (Q := Q)).powerset,
              ∑ I ∈ fiber V R Q B, ((2 : Int) * (I.card : Int) - (V.card : Int))
          = NDS2 V (family V R) := by
          let dso := double_sum_over_fiber_eq_NDS2 (V := V) (R := R) (Q := Q)
          exact dso
        rw [hB1']
        simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat,
          sub_left_inj]
        rw [← mul_sum, ← mul_sum]
        simp_all only [sum_sub_distrib, sum_const, card_powerset, Int.nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          mul_eq_mul_left_iff, sub_left_inj, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, false_and, or_false]
        rw [mul_sum]

  -- これで、hδ と hS より
  --   2^|F| * Σ_B (...)  -  NDS2(V,R) = - Σ Debt + Σ Excess
  -- さらに前段の「係数和 0」補題で左の第1項が 0
  have hcoeff0 :=
    sum_over_powerset_block_coeff_zero (V := V) (R := R) (Q := Q)
  -- 合成して結論へ
  calc
    NDS2 V (family V R)
        =
      ( (2 : Int) ^ (Free (Q := Q)).card
          * ∑ B ∈ (Rep (Q := Q)).powerset,
              ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) )
        - ( ∑ B ∈ (Rep (Q := Q)).powerset,
              ( ((2 : Int) ^ (Free (Q := Q)).card)
                  * ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)
                - ∑ I ∈ fiber V R Q B,
                    ((2 : Int) * (I.card : Int) - (V.card : Int)) ) ) := by
      -- これは単に hS を両辺移項した形
      -- すぐ上の hS を反転向きで使う
      have := hS

      simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_zero, zero_sub, card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, sub_neg_eq_add, zero_add]
  _ =
      ( (2 : Int) ^ (Free (Q := Q)).card
          * ∑ B ∈ (Rep (Q := Q)).powerset,
              ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) )
        - ( ∑ B ∈ (Rep (Q := Q)).powerset,
              ( - Debt V R Q B + Excess V R Q B ) ) := by
      -- hδ を適用（中括弧の総和を置換）
      -- `rw` 1 行相当
      exact congrArg (fun t => ( (2 : Int) ^ (Free (Q := Q)).card
                                  * ∑ B ∈ (Rep (Q := Q)).powerset,
                                      ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) )
                                - t) hδ
  _ =
      ( (2 : Int) ^ (Free (Q := Q)).card
          * 0 )
        - ( ∑ B ∈ (Rep (Q := Q)).powerset,
              ( - Debt V R Q B + Excess V R Q B ) ) := by
      -- 係数和 0 補題
      -- `rw [hcoeff0]`
      -- 実装：
      -- 置換
      have := hcoeff0
      -- 右辺第1項を 0 に
      -- 結果を採用
      -- （`rw` を避けるなら `change`+`exact` にしてもよい）
      exact
        congrFun (congrArg HSub.hSub (congrArg (HMul.hMul (2 ^ #(Free Q))) hcoeff0))
          (∑ B ∈ (Rep Q).powerset, (-Debt V R Q B + Excess V R Q B))
  _ =
      (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
        - (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) := by
      -- 左の第1項は 0，右のカッコは総和の線形性で
      -- `-∑(-Debt+Excess) = ∑Debt - ∑Excess`
      -- 整式計算
      ring_nf
      let S := (Rep Q).powerset
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_zero, zero_sub, card_powerset, Nat.cast_pow,
        Nat.cast_ofNat, neg_add_rev, neg_neg]
      ring_nf

--このファイルのメイン定理
/-- （条件付き仕上げ版）`NDS2 V (family V R1) = 0` が分かれば、
    ご希望の L4 がそのまま成立する。 -/
theorem NDS2_diff_eq_negDebt_plus_Excess_of_R1_zero
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  --(hV : supportedOn V R)
  (hR1zero : NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) = 0) :
  (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
   - NDS2 V (family V R))
  =
  - (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
  + (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) := by
  classical
  -- 右辺は `-(∑Debt) + (∑Excess)`，左辺は `0 - NDS2(V,R)`（仮定から）
  -- 一方，上で示した無条件恒等式：`NDS2(V,R) = ∑Debt - ∑Excess`
  -- これらを連結して終了
  have hR : NDS2 V (family V R)
              = (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
                - (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) :=
    NDS2_eq_sumDebt_minus_sumExcess (V := V) (R := R) (Q := Q)
  calc
    (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
       - NDS2 V (family V R))
        = 0 - NDS2 V (family V R) := by
            -- `hR1zero` を代入
            -- `rw [hR1zero]`
            exact by
              -- 置換一発
              -- 実運用では `rw [hR1zero]`
              simp_all only [R1, zero_sub, neg_sub]
    _ = - (NDS2 V (family V R)) := by
            ring
    _ = - ( (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
            - (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) ) := by
            -- `hR` を代入
            -- `rw [hR]`
            exact congrArg Neg.neg hR
    _ = - (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
          + (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) := by
            ring
/-
--この補題は条件が足りずにうまく証明できない。成り立たないと思われる。
theorem NDS2_diff_eq_negDebt_plus_Excess (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (hV : supportedOn V R) :
   (NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) - NDS2 V (family V R))
    = - (∑ B ∈ (Rep (Q := Q)).powerset, Debt V R Q B)
      + (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B) := by
  classical
  have hR1zero : NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) = 0 := by
    sorry
    --let sop := sum_over_powerset_block_coeff_zero (V := V) (R := R) (Q := Q)

  exact NDS2_diff_eq_negDebt_plus_Excess_of_R1_zero V R Q  hR1zero
-/
