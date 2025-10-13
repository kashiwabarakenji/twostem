import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Int
import Charging.Core.Basic
import Charging.Core.Chains

/- Mathlib.Algebra.Order.Group.Intでいらなくなった。
instance int_AddCommMonoid : AddCommMonoid ℤ :=
{ add := Int.add,
  add_comm := Int.add_comm,
  add_assoc := Int.add_assoc,
  zero := 0,
  zero_add := Int.zero_add,
  add_zero := Int.add_zero,
  nsmul := fun n z => n * z,
  nsmul_zero := by exact fun x => mul_eq_zero_of_left rfl x,
  nsmul_succ := by
    intro n x
    simp_all only [Nat.cast_add, Nat.cast_one]
    exact add_one_mul (↑n) x
}

instance int_PartialOrder : PartialOrder ℤ :=
{ le := (· ≤ ·),
  lt := (· < ·),
  le_refl := @le_refl ℤ _,
  le_trans := @le_trans ℤ _,
  le_antisymm := @le_antisymm ℤ _,
  lt_iff_le_not_ge := fun a b => by exact Int.lt_iff_le_not_le }

instance int_IsOrderedAddMonoid  : IsOrderedAddMonoid ℤ :=
{ add_le_add_left := by
   intro a b hab c
   exact_mod_cast Int.add_le_add_left hab c
}
-/


/-!
# Core.Fiber
ファイバーと仮定 (F) の定義。
-/

namespace Charging

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

open scoped BigOperators

namespace RuleSystem

variable (R : RuleSystem V) (D : ChainDecomp V)

/-- 鎖 `j` と外側部分 `τ` に対するファイバー：
  `C` は閉集合で、かつ `C \ P(j) = τ`。 -/
noncomputable def Fiber (j : D.ι) (τ : Finset V) : Finset (Finset V) :=
  (R.closedFamily).filter (fun C => C \ (D.P j) = τ)

@[simp] lemma mem_Fiber {j : D.ι} {τ C : Finset V} :
  C ∈ R.Fiber D j τ ↔ (R.Closed C ∧ C \ (D.P j) = τ) := by
  unfold RuleSystem.Fiber
  simp [RuleSystem.closedFamily]

/-- ファイバーが非空（存在性）であることの述語。 -/
def FiberNonempty (j : D.ι) (τ : Finset V) : Prop :=
  (R.Fiber D j τ).Nonempty

/-- (F)：各ファイバーで P(j) との交差サイズが 0..K の完全初期区間になり、
  かつ各サイズに対し一意に閉集合が存在（多重度 1）。 -/
def F_condition : Prop :=
  ∀ (j : D.ι) (τ : Finset V),
    FiberNonempty (R := R) (D := D) j τ →
    ∃ K : Nat, K ≤ D.ℓ j ∧
      ((∀ k : Nat, k ≤ K →
         ∃! (C : Finset V), C ∈ R.Fiber D j τ ∧ (C ∩ D.P j).card = k) ∧
       (∀ k : Nat, K < k → k ≤ D.ℓ j →
         ¬ ∃ C : Finset V, C ∈ R.Fiber D j τ ∧ (C ∩ D.P j).card = k))

/-- `C ∈ Fiber j τ` なら `C` は閉。 -/
lemma Closed_of_memFiber {j : D.ι} {τ C : Finset V}
  (hC : C ∈ R.Fiber D j τ) : R.Closed C :=
  (R.mem_Fiber (D := D)).1 hC |>.1

/-- `C ∈ Fiber j τ` なら `C \ P j = τ`。 -/
lemma sdiff_eq_of_memFiber {j : D.ι} {τ C : Finset V}
  (hC : C ∈ R.Fiber D j τ) : C \ D.P j = τ :=
  (R.mem_Fiber (D := D)).1 hC |>.2

--Fiber 側で同名補題を再定義している箇所は削除して、Chains 側のものを使ってください。
/-
omit [Fintype V] in
lemma asFinset_card_eq_length (P : Chain V) :
    P.asFinset.card = P.length := by
  -- 展開して Mathlib の補題を使う
  simp [Chain.asFinset, Chain.length]
  exact List.toFinset_card_of_nodup P.nodup
-/

/-- `C ∈ Fiber j τ` から、`(C ∩ P j).card ≤ ℓ j`。 -/
lemma card_inter_P_le_length {j : D.ι} {τ C : Finset V}
  (hC : C ∈ R.Fiber D j τ) :
  (C ∩ D.P j).card ≤ D.ℓ j := by
  -- `card_inter_le` : (C ∩ S).card ≤ S.card
  have hle : (C ∩ D.P j).card ≤ (D.P j).card := by
    simp_all only [mem_Fiber]
    obtain ⟨left, right⟩ := hC
    subst right
    apply Finset.card_le_card
    simp_all only [Finset.inter_subset_right]

  -- `card (P j) = ℓ j`
  have hP : (D.P j).card = D.ℓ j := by
    -- ChainDecomp.P は asFinset、ℓ は length。
    -- List.toFinset のカードは NoDup の長さに等しい。
    -- 既に Chains.lean に `Pref_top` 等があり、以下の補題が証明しやすいです。
    -- 補題が未定なら、Chains.lean に次を用意：
    -- lemma Chain.asFinset_card_eq_length : (P.asFinset).card = P.length
    -- ここではそれを用いる形にします：
    simp [ChainDecomp.P, ChainDecomp.ℓ]
    exact Chain.asFinset_card_eq_length (D.chains j)

  simpa [hP] using hle

/-! ### `closedFamily` のファイバー分割（cover & pairwise_disjoint） -/

/-- `closedFamily` は `τ = C \ P(j)` ごとのファイバーで被覆される。 -/
lemma closedFamily_subset_biUnion_Fiber (j : D.ι) :
  R.closedFamily ⊆
    (Finset.powerset (Finset.univ \ D.P j)).biUnion (fun τ => R.Fiber D j τ) := by
  intro C hC
  -- 置換：この C に固有の τ := C \ P(j)
  set τ : Finset V := C \ D.P j
  have hτ_subset : τ ⊆ Finset.univ \ D.P j := by
    intro x hx
    have hxC : x ∈ C := by
      have : x ∈ C ∧ x ∉ D.P j := by
        simpa [τ, Finset.mem_sdiff] using hx
      exact this.1
    have hx_notP : x ∉ D.P j := by
      have : x ∈ C ∧ x ∉ D.P j := by
        simpa [τ, Finset.mem_sdiff] using hx
      exact this.2
    simp [Finset.mem_sdiff, hx_notP]
  have hτ_mem : τ ∈ Finset.powerset (Finset.univ \ D.P j) :=
    Finset.mem_powerset.mpr hτ_subset
  -- 目標：C は biUnion のその τ の成分に入る
  simp_all only [mem_closedFamily, Finset.mem_powerset, Finset.mem_biUnion, mem_Fiber, true_and, exists_eq_right', τ]


/-- 逆包含：各ファイバーは `closedFamily` の部分。 -/
lemma biUnion_Fiber_subset_closedFamily (j : D.ι) :
  (Finset.powerset (Finset.univ \ D.P j)).biUnion (fun τ => R.Fiber D j τ)
    ⊆ R.closedFamily := by
  intro C hC
  rcases Finset.mem_biUnion.mp hC with ⟨τ, hτ, hCτ⟩
  -- `C ∈ Fiber j τ` なら `C` は閉
  have hClosed : R.Closed C := R.Closed_of_memFiber (D := D) hCτ
  -- `closedFamily` は `Closed` で filter
  have hU : C ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hPow : C ∈ Finset.powerset (Finset.univ : Finset V) := Finset.mem_powerset.mpr hU
  simpa [RuleSystem.closedFamily] using Finset.mem_filter.mpr ⟨hPow, hClosed⟩

/-- 等号：`closedFamily = ⋃_{τ ⊆ (univ \ P j)} Fiber j τ`。 -/
lemma closedFamily_biUnion_Fiber (j : D.ι) :
  R.closedFamily =
    (Finset.powerset (Finset.univ \ D.P j)).biUnion (fun τ => R.Fiber D j τ) := by
  apply Finset.Subset.antisymm
  · exact R.closedFamily_subset_biUnion_Fiber (D := D) j
  · exact R.biUnion_Fiber_subset_closedFamily (D := D) j

/-- 異なる τ でファイバーは相互素。 -/
lemma disjoint_Fiber {j : D.ι} {τ₁ τ₂ : Finset V} (hτ : τ₁ ≠ τ₂) :
  Disjoint (R.Fiber D j τ₁) (R.Fiber D j τ₂) := by
  refine Finset.disjoint_left.mpr ?_
  intro C hC1 hC2
  -- 同じ C が両方に入ると `C \ P j` が等しいはず
  have h1 := R.sdiff_eq_of_memFiber (D := D) hC1
  have h2 := R.sdiff_eq_of_memFiber (D := D) hC2
  exact hτ (by simpa [h1] using h2)

/-! ### ファイバー寄与の記号化（後の主定理用） -/

/-- 鎖 `j`・外側 `τ` に対する「ファイバー寄与」。
    （主定理で `NDS = ∑_{j,τ} T_{j,τ}` として使う） -/
noncomputable def fiberContribution (j : D.ι) (τ : Finset V) : ℤ :=
  ∑ C ∈ R.Fiber D j τ, (2 * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))

@[simp] lemma fiberContribution_empty (j : D.ι) :
  R.fiberContribution D j ∅ =
    ∑ C ∈ R.Fiber D j ∅, (2 * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)) := rfl

lemma fiberContribution_le_from_sum_bound
  (R : RuleSystem V) (D : ChainDecomp V) (j : D.ι) (τ : Finset V)
  (hsum :
    ∑ C ∈ R.Fiber D j τ, ((2 : ℤ) * ((C ∩ D.P j).card : ℤ))
      ≤ ((R.Fiber D j τ).card : ℤ) * ((2 : ℤ) * (D.ℓ j : ℤ))) :
  ∑ C ∈ R.Fiber D j τ, ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))
    ≤ ((R.Fiber D j τ).card : ℤ) * (((2 : ℤ) * (D.ℓ j : ℤ)) - (D.ℓ j : ℤ)) := by
  classical
  -- 左辺を「差の和 = 和の差」に展開
  have hsplit :
      ∑ C ∈ R.Fiber D j τ,
          ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))
        =
      (∑ C ∈ R.Fiber D j τ, ((2 : ℤ) * ((C ∩ D.P j).card : ℤ)))
      - (∑ C ∈ R.Fiber D j τ, (D.ℓ j : ℤ)) := by
    -- sum_sub_distrib：∑(f - g) = ∑f - ∑g
    simp [Finset.sum_sub_distrib]
  -- 定数 (ℓ_j) の和を card * ℓ_j に簡約
  have hconst :
      ∑ C ∈ R.Fiber D j τ, (D.ℓ j : ℤ)
        = ((R.Fiber D j τ).card : ℤ) * (D.ℓ j : ℤ) := by
    simp [Finset.sum_const]
  -- hsum から、両辺に同じものを引いて不等式を保つ
  --   (∑ 2|⋯|) - (∑ ℓ) ≤ card * (2ℓ) - card * ℓ
  have hmain :
      (∑ C ∈ R.Fiber D j τ, ((2 : ℤ) * ((C ∩ D.P j).card : ℤ)))
      - (∑ C ∈ R.Fiber D j τ, (D.ℓ j : ℤ))
        ≤
      ((R.Fiber D j τ).card : ℤ) * ((2 : ℤ) * (D.ℓ j : ℤ))
      - (((R.Fiber D j τ).card : ℤ) * (D.ℓ j : ℤ)) := by
      simp_all only [Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul, Int.sub_le_sub_right_iff]

  -- 右辺を factor： a*b - a*c = a*(b-c)
  simpa [hsplit, mul_sub] using hmain


/-- `fiberContribution` の単調な上界（粗い評価）：
    各項 `((C ∩ P j).card)` は `≤ ℓ j`。 -/
lemma fiberContribution_le_trivial (j : D.ι) (τ : Finset V) :
  R.fiberContribution D j τ ≤
    ((R.Fiber D j τ).card : ℤ) * (2 * (D.ℓ j : ℤ) - (D.ℓ j : ℤ)) := by
  -- ただの粗い評価：各 C ごとに `(C ∩ P j).card ≤ ℓ j` を使って項を押さえる。
  classical
  dsimp [fiberContribution]
  dsimp [ChainDecomp.ℓ]
  have hP : (D.P j).card = D.ℓ j := by
    simp [ChainDecomp.P, ChainDecomp.ℓ]
    exact Chain.asFinset_card_eq_length (D.chains j)
  -- 各項の上界： 2*|C∩P_j| - ℓ ≤ 2*ℓ - ℓ
  have hbound :
    ∀ C ∈ R.Fiber D j τ,
      ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))
        ≤ ((2 : ℤ) * (D.ℓ j : ℤ) - (D.ℓ j : ℤ)) := by
    intro C hC
    -- 自明な上界 |C∩P_j| ≤ |P_j|
    have hsubset : C ∩ D.P j ⊆ D.P j := by
      intro x hx
      exact (Finset.mem_inter.mp hx).2
    have hk_nat : (C ∩ D.P j).card ≤ (D.P j).card := by
      exact Finset.card_le_card hsubset

    -- 整数へ持ち上げて 2倍し、両辺に同じものを引く
    have hkZ : ((C ∩ D.P j).card : ℤ) ≤ (D.ℓ j : ℤ) := by
      simpa [hP] using (by exact_mod_cast hk_nat : ((C ∩ D.P j).card : ℤ) ≤ (D.P j).card)
    have hkZ2 : (2 : ℤ) * ((C ∩ D.P j).card : ℤ) ≤ (2 : ℤ) * (D.ℓ j : ℤ) := by
      simp_all only [mem_Fiber, Finset.inter_subset_right, Int.ofNat_le, Int.reduceLT, Int.mul_le_mul_left]
    exact Int.sub_le_sub_right hkZ2 ↑(D.ℓ j)

  -- 定数関数への比較和： sum f ≤ sum (const a) = card * a

  have hsum := Finset.sum_le_sum hbound
  -- 右辺を card * const に簡約
  simp [Finset.sum_const] at hsum

    -- これは定義そのもの
  simp
  -- 上の一般補題を適用するため、両辺を ℓ で書き直す
  have := fiberContribution_le_from_sum_bound (R := R) (D := D) j τ (by
    -- hsum は既に ℓ で書かれているのでそのまま使える
    simpa using hsum)
  -- 仕上げに length へ戻す
  simp
  simp_all only [mem_Fiber, tsub_le_iff_right, sub_add_cancel, and_imp,
    Finset.sum_sub_distrib, Finset.sum_const, Int.nsmul_eq_mul]
  exact this

lemma Fiber_nonempty_iff
  (R : RuleSystem V) (D : ChainDecomp V) :
  ∀ {j : D.ι} {τ : Finset V},
    R.FiberNonempty (D := D) j τ ↔ ∃ C, R.Closed C ∧ C \ D.P j = τ := by
  classical
  intro j τ; constructor
  · intro h
    rcases h with ⟨C, hC⟩
    -- C ∈ Fiber ⇒ (Closed C ∧ C \ P j = τ)
    have h' : R.Closed C ∧ C \ D.P j = τ :=
      (R.mem_Fiber (D := D) (j := j) (τ := τ) (C := C)).1 hC
    exact ⟨C, h'.1, h'.2⟩
  · rintro ⟨C, hClosed, hτ⟩
    -- まず C ∈ closedFamily
    have hPow : C ∈ Finset.powerset (Finset.univ : Finset V) :=
      Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hLC : C ∈ R.closedFamily := by
      simpa [RuleSystem.closedFamily] using
        Finset.mem_filter.mpr ⟨hPow, hClosed⟩
    -- そこから Fiber へ
    exact ⟨C, by simpa [RuleSystem.Fiber, hτ] using hLC⟩

-- 2) （補助）Fiber の相互素性を powerset 指標上で束ねた形に
lemma pairwiseDisjoint_Fiber (j : D.ι) :
  ∀ τ₁ τ₂, τ₁ ≠ τ₂ → Disjoint (R.Fiber D j τ₁) (R.Fiber D j τ₂) := by
  intro τ₁ τ₂ hneq
  apply R.disjoint_Fiber (D := D) (j := j)
  exact hneq

-- 3) closedFamily の総和 = ファイバー分割の二重和
lemma sum_closedFamily_as_sum_overFibers
  {α : Type*} [AddCommMonoid α]
  (j : D.ι) (f : Finset V → α) :
  ∑ C ∈ R.closedFamily, f C
    = ∑ τ ∈ Finset.powerset (Finset.univ \ D.P j),
        ∑ C ∈ R.Fiber D j τ, f C := by
  classical
  -- 既に示した等号： closedFamily = ⋃ τ Fiber j τ
  have hdecomp := R.closedFamily_biUnion_Fiber (D := D) j
  -- 右辺で biUnion の和に切り替え
  -- Finset.sum_biUnion の条件：ペアワイズ相互素が必要
  have hpair := R.pairwiseDisjoint_Fiber (D := D) j
  -- sum_biUnion を使うため、等式を書き換える
  simp [hdecomp]
  exact Finset.sum_biUnion fun ⦃x⦄ a ⦃y⦄ a => hpair x y

-- 4) fiberContribution の粗い上界（簡潔版）
lemma fiberContribution_le_trivial'
  (j : D.ι) (τ : Finset V) :
  R.fiberContribution D j τ
    ≤ ((R.Fiber D j τ).card : ℤ) * (2 * (D.ℓ j : ℤ) - (D.ℓ j : ℤ)) := by
  classical
  -- まず、項別に 2 * |C ∩ P_j| ≤ 2 * ℓ_j を示す
  have hP : (D.P j).card = D.ℓ j := by
    simpa [ChainDecomp.P, ChainDecomp.ℓ]
      using Chain.asFinset_card_eq_length (D.chains j)

  have hpoint' :
    ∀ C ∈ R.Fiber D j τ,
      (2 : ℤ) * ((C ∩ D.P j).card : ℤ) ≤ (2 : ℤ) * (D.ℓ j : ℤ) := by
    intro C hC
    -- |C ∩ P_j| ≤ |P_j| = ℓ_j
    have hsubset : C ∩ D.P j ⊆ D.P j := by
      intro x hx; exact (Finset.mem_inter.mp hx).2
    have hcard_le : (C ∩ D.P j).card ≤ (D.P j).card :=
      Finset.card_le_card hsubset
    have hkZ : ((C ∩ D.P j).card : ℤ) ≤ (D.ℓ j : ℤ) := by
      simpa [hP] using
        (by exact_mod_cast hcard_le : ((C ∩ D.P j).card : ℤ) ≤ (D.P j).card)
    -- 2 ≥ 0 なので左から掛けて不等式保存
    simp_all only [mem_Fiber, Finset.inter_subset_right, Int.ofNat_le, Int.reduceLT, Int.mul_le_mul_left]

  -- 項別の評価を総和に上げる：∑ 2|⋯| ≤ card * (2ℓ)
  have hsum :
    ∑ C ∈ R.Fiber D j τ, ((2 : ℤ) * ((C ∩ D.P j).card : ℤ))
      ≤ ((R.Fiber D j τ).card : ℤ) * ((2 : ℤ) * (D.ℓ j : ℤ)) := by
    -- sum_le_sum で項別評価を合算し、右辺は定数の和＝card * const
    have := Finset.sum_le_sum hpoint'
    simpa [Finset.sum_const] using this

  -- 一般補題で「差の和」に変換： (∑ 2|⋯|) から fiberContribution の形へ
  -- （ここで “- ℓ” を両辺に同数だけ引く操作を一括で処理）
  have := fiberContribution_le_from_sum_bound (R := R) (D := D) j τ hsum

  -- ちょうど目標の形
  simpa [RuleSystem.fiberContribution] using this

end RuleSystem

end Charging
