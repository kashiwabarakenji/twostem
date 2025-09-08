import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Twostem.General
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

omit [DecidableEq α] in
lemma NDS2_sum_formula
  (V : Finset α) (F : Finset (Finset α)) :
  NDS2 V F = ∑ I ∈ F, ((2 : Int) * (I.card : Int) - (V.card : Int)) := by
  exact rfl

omit [DecidableEq α] in
lemma NDS2_family_empty_zero (V : Finset α) :
  NDS2 V (family V (∅ : Finset (Rule α))) = 0 := by
  simp_all only [family]
  dsimp [NDS2]
  dsimp [isClosed]
  simp
  let scp := sum_card_powerset_int V
  have :∑ x ∈ V.powerset, 2 * @Nat.cast ℤ instNatCastInt x.card = 2 * ∑ x ∈ V.powerset, ↑x.card := by
    simp [two_mul]
    rw [Finset.sum_add_distrib]
  rw [this, scp]
  rw [←mul_assoc]
  by_cases hV : V.card = 0
  case pos =>
    simp_all only [Finset.card_eq_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.cast_zero,
      zero_tsub, pow_zero, mul_zero]
    exact rfl
  case neg =>
    rw [mul_pow_sub_one hV 2]
    exact Int.sub_self (2 ^ V.card * ↑V.card)

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

/- `family` のメンバ判定を素直に展開した形。 -/
omit [DecidableEq α] in
lemma mem_family_iff
  (V : Finset α) (R : Finset (Rule α)) {I : Finset α} :
  I ∈ family V R ↔ I ⊆ V ∧ isClosed R I := by
  unfold family
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hsubset : I ⊆ V := Finset.mem_powerset.mp h'.1
    exact And.intro hsubset h'.2
  · intro h
    have hsubset : I ⊆ V := h.1
    have hclosed : isClosed R I := h.2
    have hpow : I ∈ V.powerset := Finset.mem_powerset.mpr hsubset
    exact Finset.mem_filter.mpr (And.intro hpow hclosed)

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
noncomputable def Core
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) : Finset α := by
  classical
  exact V.filter (fun x => ∀ I ∈ ViolSet V R t0, x ∈ I)

structure SCCQuot (α : Type u) (V : Finset α) (R : Finset (Rule α)) where
  (β : Type u) [βdec : DecidableEq β]
  (π : α → β)
  (σ : β → α)
  (σ_in_V : ∀ b, σ b ∈ V)
attribute [instance] SCCQuot.βdec

/-- 代表化写像 -/
def rep {β : Type u} (π : α → β) (σ : β → α) : α → α := fun x => σ (π x)

/-- 代表集合 -/ --大文字の方に統一する？
def Rep {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) : Finset α :=
  V.image (rep (π := Q.π) (σ := Q.σ))

/-- 自由成分 -/
def Free {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) : Finset α :=
  V \ Rep (Q := Q)

/-- 繊維：`I ∩ Rep = B` を満たす family の部分 -/
noncomputable def fiber (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (B : Finset α) : Finset (Finset α) :=
  (family V R).filter (fun I => I ∩ Rep (Q := Q) = B)


/-- R が V の元だけから成る（新頂点なし）。 -/
def supportedOn (V : Finset α) (R : Finset (α × α × α)) : Prop :=
  ∀ {t : α × α × α}, t ∈ R →
    t.1 ∈ V ∧ t.2.1 ∈ V ∧ t.2.2 ∈ V

--def contractRules
--  (p : α → β) [DecidableEq β] (R : Finset (Rule α)) : Finset (β × β × β) :=
--  (R.image (fun t => (p t.1, p t.2.1, p t.2.2)))
def contractRules {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α) (R : Finset (Rule α)) : Finset (Rule α) := R.image (fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2)))

--引用なしだが、メインから使う予定
lemma supportedOn_contractRules (V : Finset α) (R : Finset (Rule α)) {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α)-- (hV : supportedOn V R)
 (hσ : ∀ b, σ b ∈ V) :
 supportedOn V (contractRules (π := π) (σ := σ) R) := by

  intro t ht
  -- t は像：∃ s∈R, t = (σ (π s.1), σ (π s.2.1), σ (π s.2.2))
  rcases Finset.mem_image.mp ht with ⟨s, hsR, hmap⟩
  -- s の各成分は V にある
  subst hmap
  simp_all only [and_self]

--引用なし
lemma card_contractRules_le
  (R : Finset (Rule α))
  {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α) :
  (contractRules (π := π) (σ := σ) R).card ≤ R.card := by
  -- 画像の濃度は元の濃度以下（基本事実）
  exact Finset.card_image_le
    (s := R) (f := fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2)))

--参照なしだがメインから使う予定
lemma card_contractRules_lt_of_nonninj
  (R : Finset (Rule α))
  {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α)
  (noninj :
    ∃ t₁ ∈ R, ∃ t₂ ∈ R, t₁ ≠ t₂ ∧
      (σ (π t₁.1), σ (π t₁.2.1), σ (π t₁.2.2))
        = (σ (π t₂.1), σ (π t₂.2.1), σ (π t₂.2.2))) :
  (contractRules (π := π) (σ := σ) R).card < R.card := by
  classical
  -- 記号短縮
  let f : Rule α → Rule α :=
    fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2))
  rcases noninj with ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩
  -- 像は t₂ を消しても変わらない：image R f = image (R.erase t₂) f
  have hsub₁ :
      (R.image f) ⊆ ((R.erase t₂).image f) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨s, hsR, hys⟩
    by_cases hs : s = t₂
    · -- s = t₂ の像は t₁ の像でも表せるので、erase側の像に入る
      -- f t₂ = f t₁
      have hft₂ : f s = f t₁ := by
        -- hs で置換してから heq を使う
        have : f t₂ = f t₁ := by
          -- `heq : f t₁ = f t₂` なので対称にする
          exact Eq.symm heq
        -- s = t₂ を反映
        exact Eq.trans (by cases hs; rfl) this
      -- t₁ は erase t₂ に居る
      have ht₁erase : t₁ ∈ R.erase t₂ :=
        by
          subst hys hs
          simp_all only [Finset.mem_image, Prod.mk.injEq, Prod.exists, ne_eq, Finset.mem_erase, not_false_eq_true, and_self, f]

      -- y = f s = f t₁ で、t₁∈erase だから像に入る
      have : y = f t₁ := by
        apply Eq.trans
        exact id (Eq.symm hys)--hys hft₂
        exact hft₂
      apply Finset.mem_image.mpr
      show ∃ a ∈ R.erase t₂, f a = y
      use t₁
      subst hys hs
      simp_all only [Finset.mem_image, Prod.mk.injEq, Prod.exists, ne_eq, Finset.mem_erase, not_false_eq_true, and_self, f]

    · -- s ≠ t₂ のときは、そのまま erase 側の像に入る
      have hsErase : s ∈ R.erase t₂ :=
        Finset.mem_erase.mpr ⟨hs, hsR⟩
      exact Finset.mem_image.mpr ⟨s, hsErase, hys⟩
  have hsub₂ :
      ((R.erase t₂).image f) ⊆ (R.image f) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨s, hsErase, hys⟩
    -- erase の要素は元集合の要素
    have hsR : s ∈ R := (Finset.mem_erase.mp hsErase).2
    exact Finset.mem_image.mpr ⟨s, hsR, hys⟩
  -- 以上より両包含で像が一致
  have himage_eq : (R.image f) = ((R.erase t₂).image f) :=
    by
      apply Finset.Subset.antisymm
      · exact hsub₁
      · exact hsub₂
  -- 濃度の比較：画像の濃度 ≤ 台集合の濃度（erase側）
  have hcard_le_erase :
      ((R.erase t₂).image f).card ≤ (R.erase t₂).card :=
    Finset.card_image_le (s := R.erase t₂) (f := f)
  -- 左辺を書き換えて、(R.image f).card ≤ (R.erase t₂).card
  have hle : (R.image f).card ≤ (R.erase t₂).card := by
    -- `congrArg Finset.card` で等式からカード等式へ
    have hc : (R.image f).card = ((R.erase t₂).image f).card :=
      congrArg Finset.card himage_eq
    -- `hc ▸ hcard_le_erase`
    exact le_trans (le_of_eq hc) hcard_le_erase
  -- `erase` は真に小さい（t₂∈R）
  have hlt_erase : (R.erase t₂).card < R.card := by
    exact Finset.card_erase_lt_of_mem ht₂
  -- 連鎖して結論
  exact lt_of_le_of_lt hle hlt_erase

/-- （証明済として利用可）1本消去での非減（A/B/D/E のいずれかで供給） -/
structure PeelWitness (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) : Prop where
  mem    : t0 ∈ R
  nondec : NDS2 V (family V R) ≤ NDS2 V (family V (R.erase t0))

/-- （証明済：C）無害縮約 -/
structure SafeShrink (V : Finset α) (R R1 : Finset (Rule α)) : Prop where
  smaller    : R1.card < R.card
  supported  : supportedOn V R1
  nds_nondec : NDS2 V (family V R) ≤ NDS2 V (family V R1)

/-- Peel or Shrink の存在（非空 R でどちらかが見つかる） -/
def PeelOrShrink (V : Finset α) (R : Finset (Rule α)) : Prop :=
  (∃ t0, PeelWitness V R t0) ∨ (∃ R1, SafeShrink V R R1)

/-- `supportedOn` は消去で保存 -/
lemma supportedOn_erase
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hV : supportedOn V R) :
  supportedOn V (R.erase t0) := by
  intro t ht
  rcases Finset.mem_erase.mp ht with ⟨_, htR⟩
  exact hV htR
