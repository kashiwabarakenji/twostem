import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Twostem.General
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]


--いろいろなところから使われる共通定義

abbrev Rule (α) := α × α × α

/-- `I` が `R`-閉：すべての `(a,b,r) ∈ R` で `a ∈ I ∧ b ∈ I → r ∈ I` -/
def isClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ t ∈ R, (t.1 ∈ I ∧ t.2.1 ∈ I) → t.2.2 ∈ I

/-- Provide decidable instance for isClosed using classical reasoning -/
noncomputable instance isClosedDecidable (R : Finset (Rule α)) (I : Finset α) : Decidable (isClosed R I) := by
  classical infer_instance


---共通定義。faminyに関するもの。

/-- 閉包族：`V` の冪集合を `isClosed R` でフィルタ -/
noncomputable def family (V : Finset α) (R : Finset (Rule α)) : Finset (Finset α) := by
  classical
  exact V.powerset.filter (fun I => isClosed R I)

/- （既知として使う前提）`family V R` の要素は `V` の部分集合。 -/
omit [DecidableEq α] in
lemma family_subsets (V : Finset α) (R : Finset (Rule α)) :
  ∀ {I : Finset α}, I ∈ family V R → I ⊆ V := by
  classical
  intro I hI
  dsimp [family] at hI ⊢
  rw [Finset.subset_iff]
  intro x a
  simp_all only [Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨left, right⟩ := hI
  exact left a

--現状使われてないが、実は使えばいいのかも。
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

omit [DecidableEq α] in
lemma empty_mem_family
  (V : Finset α) (R : Finset (Rule α)) :
 (∅ : Finset α) ∈ family V R := by
  -- ∅ ⊆ V は自明
  -- isClosed R ∅ は自明（前提が偽になるので）
  dsimp [family]
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · intro t ht hparents
    exfalso
    simp_all only [Finset.notMem_empty, and_self]

--共通定義NDSに関するもの。

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

--Peelのほうに使うもの。

--ProblemAだけでなく、ProblemBでも使う。
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

---Coreに関して Problem AとB-----
/-- 交わり核（違反集合群の共通部分）。空なら便宜上 `V` とする。 -/
noncomputable def Core
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) : Finset α := by
  classical
  exact V.filter (fun x => ∀ I ∈ ViolSet V R t0, x ∈ I)

--使われている
/-- x が Core に入る ↔ x∈V かつ「全ての違反集合 I に x が入る」 -/
lemma mem_Core_iff
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) (x : α) :
  x ∈ Core V R t0
  ↔ x ∈ V ∧ (∀ I ∈ ViolSet V R t0, x ∈ I) := by
  classical
  -- Core は `V.filter P` なので、`mem_filter` の同値。
  apply Iff.intro
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    exact And.intro hx'.1 hx'.2
  · intro hx
    have : x ∈ V := hx.1
    have : (x ∈ V ∧ ∀ I ∈ ViolSet V R t0, x ∈ I) := And.intro hx.1 hx.2
    exact Finset.mem_filter.mpr this

--使われてない。
/-- Core は V の部分集合 -/
lemma Core_subset_V
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α) :
  Core V R t0 ⊆ V := by
  classical
  intro x hx
  have hx' := (mem_Core_iff (V := V) (R := R) (t0 := t0) x).1 hx
  exact hx'.1

--使われてない。
/-- I が違反族に属するとき、Core ⊆ I （「共通部分」の定義から即） -/
lemma Core_subset_of_mem_ViolSet
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  {I : Finset α} (hI : I ∈ ViolSet V R t0) :
  Core V R t0 ⊆ I := by
  classical
  intro x hx
  have hx' := (mem_Core_iff (V := V) (R := R) (t0 := t0) x).1 hx
  exact hx'.2 I hI

--使われてない。
/-- 違反族が空なら Core = V （外側の全称が空域なので真） -/
lemma Core_eq_V_of_ViolSet_empty
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hEmpty : ViolSet V R t0 = ∅) :
  Core V R t0 = V := by
  classical
  -- `∀ I ∈ ∅, …` は真なので、Core は `V.filter (fun _ => True)` に等しい
  -- → これは `V`。
  ext x
  apply Iff.intro
  · intro hx
    have hx' := (mem_Core_iff (V := V) (R := R) (t0 := t0) x).1 hx
    exact hx'.1
  · intro hxV
    have hall : ∀ I ∈ ViolSet V R t0, x ∈ I := by
      -- 空集合上の全称は自明に成立
      intro I hI
      have : False := by
        -- hI : I ∈ ∅ に矛盾
        have : I ∈ (∅ : Finset (Finset α)) := by
          simp_all only [Finset.notMem_empty]

        exact Finset.notMem_empty I this
      exact this.elim
    have : x ∈ V ∧ (∀ I ∈ ViolSet V R t0, x ∈ I) := And.intro hxV hall
    exact Finset.mem_filter.mpr this

-----
---SCC関係 (Problem C系で広く使われるもの)

structure SCCQuot (α : Type u) (V : Finset α) (R : Finset (Rule α)) where
  (β : Type u) [βdec : DecidableEq β]
  (π : α → β)
  (σ : β → α)
  (σ_in_V : ∀ b, σ b ∈ V)
attribute [instance] SCCQuot.βdec

/-- 代表化写像 -/
def rep {β : Type u} (π : α → β) (σ : β → α) : α → α := fun x => σ (π x)

/-- 代表集合 -/ --小文字のrepを使って定義される。familyRepというのもある。
def Rep {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) : Finset α :=
  V.image (rep (π := Q.π) (σ := Q.σ))

/-- 自由成分 -/
def Free {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) : Finset α :=
  V \ Rep (Q := Q)

/-- 繊維：`I ∩ Rep = B` を満たす family の部分 -/
noncomputable def fiber (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (B : Finset α) : Finset (Finset α) :=
  (family V R).filter (fun I => I ∩ Rep (Q := Q) = B)

/-- 代表化は常に `V` に落ちる。 -/
lemma rep_mem_V {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) (x : α):-- (hx : x ∈ V) :
  rep (π := Q.π) (σ := Q.σ) x ∈ V := by
  -- rep x = σ (π x) で、σ は常に V に入る
  exact Q.σ_in_V (Q.π x)

/-- `Rep Q = V.image (rep)` は `V ⊆` で、したがって `Rep Q ⊆ V`。 -/
lemma Rep_subset_V
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) :
  Rep (Q := Q) ⊆ V := by
  intro y hy
  -- y = rep x かつ x∈V を取り出す
  rcases Finset.mem_image.mp hy with ⟨x, hxV, hrep⟩
  have : rep (π := Q.π) (σ := Q.σ) x ∈ V := by
    exact rep_mem_V V R Q x
  -- 置換して結論
  exact Eq.ndrec this hrep

/-- `fiber` のメンバ判定を素直に展開した形。 -/
lemma mem_fiber_iff
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B I : Finset α} :
  I ∈ fiber V R Q B ↔ I ∈ family V R ∧ I ∩ Rep (Q := Q) = B := by
  unfold fiber
  constructor
  · intro h; exact Finset.mem_filter.mp h
  · intro h; exact Finset.mem_filter.mpr h

/-- `Free Q = V \ Rep Q` と定義したので、`Rep` と `Free` は交わらない。 -/
lemma disjoint_Rep_Free
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) :
  Disjoint (Rep (Q := Q)) (Free (Q := Q)) := by
  -- Free := V \ Rep
  -- 標準事実：s と (t := s \ u) は交わらない
  refine Finset.disjoint_left.mpr ?_
  intro a haRep haFree
  -- haFree : a ∈ V ∧ a ∉ Rep
  have hVand := Finset.mem_sdiff.mp haFree
  -- Rep と (V \ Rep) は排反
  exact hVand.2 haRep

/-- `Rep Q ⊆ V` より、`Rep ∪ Free = V`。 -/
lemma union_Rep_Free_eq_V
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) :
  Rep (Q := Q) ∪ Free (Q := Q) = V := by
  -- Free = V \ Rep、かつ Rep ⊆ V なので union_sdiff_of_subset
  have hsub : Rep (Q := Q) ⊆ V := Rep_subset_V (V := V) (R := R) (Q := Q)
  -- `Finset.union_sdiff_of_subset` を使う
  -- (この補題名が環境で `by` 補う必要がある場合は手で両包含を示してもOK)
  exact Finset.union_sdiff_of_subset hsub

/-- 上の等式から直ちに得られる分割のカード等式。 -/
lemma card_Rep_add_card_Free
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R) :
  (Rep (Q := Q)).card + (Free (Q := Q)).card = V.card := by
  -- `Rep ⊆ V` だから `card (V \ Rep) + card Rep = card V`
  have hsub : Rep (Q := Q) ⊆ V := Rep_subset_V (V := V) (R := R) (Q := Q)
  -- `Finset.card_sdiff_add_card` を使うと一発。
  -- `card (V \ Rep) + card Rep = card V`。
  have h :=
    Finset.card_sdiff_add_card (s := V) (t := Rep (Q := Q))
  -- 形を合わせるために加法の交換。
  -- h : (V \ Rep).card + (Rep).card = V.card
  -- しかし `Free = V \ Rep` なので書き換える。
  have hfree : (V \ Rep (Q := Q)) = Free (Q := Q) := rfl
  -- 等式を書き換える。
  -- （`rw` を段階的に使う。）
  have := h
  -- まず左辺の `(V \ Rep)` を `Free` に置換
  have h1 : (V \ Rep (Q := Q)).card + (Rep (Q := Q)).card = V.card := by
    exact Finset.card_sdiff_add_card_eq_card hsub
  -- 置換して結論
  -- `h1` をそのまま返す（`rfl` で `Free` を認識）
  -- ここで `rfl` による置換が効くように式を並べる
  -- Lean 的には `rfl` 展開不要なら `exact` で良い
  rw [hfree] at h1
  rw [add_comm] at h1
  exact h1

/-- R が V の元だけから成る（新頂点なし）。 -/
def supportedOn (V : Finset α) (R : Finset (α × α × α)) : Prop :=
  ∀ {t : α × α × α}, t ∈ R →
    t.1 ∈ V ∧ t.2.1 ∈ V ∧ t.2.2 ∈ V

omit [DecidableEq α] in
lemma V_nonempty_of_supported
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hne : R ≠ ∅) :
  V.Nonempty := by
  classical
  -- R の要素 t を 1 本取り、親 t.1 ∈ V から証人を得る
  rcases Finset.Nonempty.exists_mem
      (Finset.nonempty_iff_ne_empty.mpr hne) with ⟨t, ht⟩
  have h := hV (t := t) ht
  exact ⟨t.1, h.1⟩

/-- `supportedOn` は消去で保存 -/
lemma supportedOn_erase
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (hV : supportedOn V R) :
  supportedOn V (R.erase t0) := by
  intro t ht
  rcases Finset.mem_erase.mp ht with ⟨_, htR⟩
  exact hV htR

--- contractRules関連

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

-- R1を使っているもの。

/-- 記号短縮：R₁ := contractRules Q.π Q.σ R -/
@[simp] def R1 (Q : SCCQuot α V R) : Finset (Rule α) :=
  contractRules (π := Q.π) (σ := Q.σ) R

/-- R₁ の閉性は `Rep` 成分だけで決まり、`I` と `I ∩ Rep` で同値。
    ここでは `supportedOn V R` を仮定して、R₁ の子（σ(π r)）が確かに `Rep` に属することを使う。 -/
lemma isClosed_contractRules_iff_onRep
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) :
  ∀ I : Finset α,
    isClosed (R1 (V := V) (R := R) (Q := Q)) I
      ↔
    isClosed (R1 (V := V) (R := R) (Q := Q)) (I ∩ Rep (Q := Q)) := by
  classical
  intro I
  -- 記号短縮
  set R₁ := R1 (V := V) (R := R) (Q := Q)
  constructor
  · -- → 方向：I が閉なら I∩Rep も閉
    intro hClosed t ht hparents
    -- t ∈ R₁ は像なので、元の s∈R を取れる
    rcases Finset.mem_image.mp ht with ⟨s, hsR, hmap⟩
    -- 親が I∩Rep に入っていれば I にも入っている
    have hpa : t.1 ∈ I := by
      -- t = (σ(π s.1), …) なので、親は Rep の元
      -- hparents : t.1 ∈ I ∩ Rep ∧ t.2.1 ∈ I ∩ Rep
      exact (Finset.mem_inter.mp (And.left hparents)).1
    have hpb : t.2.1 ∈ I := by
      exact (Finset.mem_inter.mp (And.right hparents)).1
    -- I の閉性から子も I に入る
    have hchild_in_I : t.2.2 ∈ I := by
      -- hClosed : isClosed R₁ I
      -- 使うには t の形を合わせる必要はない（R₁・t のままでよい）
      exact hClosed t ht (And.intro hpa hpb)
    -- 子は Rep の元（R₁ の子は σ(π r) 形）。I∩Rep にも入る。
    have hchild_in_Rep : t.2.2 ∈ Rep (Q := Q) := by
      have : t.2.2 = (Q.σ (Q.π s.2.2)) := by
        have := congrArg (fun (x : α × α × α) => x.2.2) hmap
        -- 左辺の第3成分は σ(π s.2.2)
        exact id (Eq.symm this)
      have hrep_mem : (rep (π := Q.π) (σ := Q.σ) s.2.2) ∈ Rep (Q := Q) := by
        -- s.2.2 ∈ V は hsV
        refine Finset.mem_image.mpr ⟨s.2.2, ?_, rfl⟩
        dsimp [supportedOn] at hV
        exact (hV hsR).2.2
      -- 置換
      subst hmap
      simp_all only [R1, Finset.mem_inter, true_and, R₁]
      exact hrep_mem

    -- まとめ：子は I と Rep の両方に入るので I∩Rep に入る
    exact (Finset.mem_inter.mpr (And.intro hchild_in_I hchild_in_Rep))
  · -- ← 方向：I∩Rep が閉なら I も閉
    intro hClosedRep t ht hparents
    -- 親が I に入っていれば I∩Rep にも入っている（親は Rep の元）
    -- t ∈ R₁ は像なので、親は Rep の元（σ(π _ ) 形）
    have hparents_in_Rep :
        t.1 ∈ Rep (Q := Q) ∧ t.2.1 ∈ Rep (Q := Q) := by
      rcases Finset.mem_image.mp ht with ⟨s, hsR, hmap⟩
      -- 第1成分
      have h1 : t.1 = (Q.σ (Q.π s.1)) := by
        have := congrArg (fun (x : α × α × α) => x.1) hmap
        subst hmap
        simp_all only [R1, R₁]

      have h1mem : (rep (π := Q.π) (σ := Q.σ) s.1) ∈ Rep (Q := Q) := by
        have hsV := (hV hsR).1
        exact Finset.mem_image.mpr ⟨s.1, hsV, rfl⟩
      -- 第2成分（親2）
      have h2 : t.2.1 = (Q.σ (Q.π s.2.1)) := by
        have := congrArg (fun (x : α × α × α) => x.2.1) hmap
        subst hmap
        simp_all only [R1, R₁]

      have h2mem : (rep (π := Q.π) (σ := Q.σ) s.2.1) ∈ Rep (Q := Q) := by
        have hsV := (hV hsR).2.1
        exact Finset.mem_image.mpr ⟨s.2.1, hsV, rfl⟩
      constructor
      simp_all only [R1, R₁]
      exact h1mem

      simp_all only [R1, R₁]
      exact h2mem

    -- したがって親は I∩Rep に入る
    have hpa : t.1 ∈ I ∩ Rep (Q := Q) :=
      Finset.mem_inter.mpr (And.intro (And.left hparents) hparents_in_Rep.1)
    have hpb : t.2.1 ∈ I ∩ Rep (Q := Q) :=
      Finset.mem_inter.mpr (And.intro (And.right hparents) hparents_in_Rep.2)
    -- I∩Rep の閉性から子は I∩Rep に入る
    have hchild_in_Irep : t.2.2 ∈ I ∩ Rep (Q := Q) :=
      hClosedRep t ht (And.intro hpa hpb)
    -- よって I にも入る
    exact (Finset.mem_inter.mp hchild_in_Irep).1

/-- Rep 上の縮約族（R₁ に対する Rep 側の閉集合族） -/
--外部から参照される定理で利用されている。
noncomputable def familyRep
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  Finset (Finset α) :=
  (Rep (Q := Q)).powerset.filter
    (fun B => isClosed (R1 (V := V) (R := R) (Q := Q)) B)

/-- R₁ の family へのメンバ判定を、`I ⊆ V` と `I ∩ Rep ∈ familyRep` に還元。 -/
lemma mem_family_contractRules_iff
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) {I : Finset α} :
  I ∈ family V (R1 (V := V) (R := R) (Q := Q))
    ↔ I ⊆ V ∧ I ∩ Rep (Q := Q) ∈ familyRep (V := V) (R := R) (Q := Q) := by
  classical
  -- family の定義を展開
  have base := (mem_family_iff (V := V) (R := R1 (V := V) (R := R) (Q := Q)) (I := I))
  -- isClosed の同値で書き換える
  have hceq := isClosed_contractRules_iff_onRep (V := V) (R := R) (Q := Q) hV I
  -- `Rep ⊆ V` を使って powerset 側の要件に整える
  have hRep_subV : Rep (Q := Q) ⊆ V := Rep_subset_V (V := V) (R := R) (Q := Q)
  constructor
  · intro hIfam
    have hsub_and_closed := (base.mp hIfam)
    have hsub : I ⊆ V := hsub_and_closed.1
    have hclosedI : isClosed (R1 (V := V) (R := R) (Q := Q)) I := hsub_and_closed.2
    -- isClosed を I∩Rep へ
    have hclosedIrep : isClosed (R1 (V := V) (R := R) (Q := Q)) (I ∩ Rep (Q := Q)) :=
      (hceq.mp hclosedI)
    -- I∩Rep ⊆ Rep は自明
    have hBsubset : I ∩ Rep (Q := Q) ⊆ Rep (Q := Q) := Finset.inter_subset_right
    have hBin : I ∩ Rep (Q := Q) ∈ (Rep (Q := Q)).powerset :=
      Finset.mem_powerset.mpr hBsubset
    -- familyRep に入る
    have hBfamRep :
        I ∩ Rep (Q := Q) ∈ familyRep (V := V) (R := R) (Q := Q) := by
      unfold familyRep
      exact Finset.mem_filter.mpr (And.intro hBin hclosedIrep)
    exact And.intro hsub hBfamRep
  · intro h
    -- 逆向き：I ⊆ V かつ I∩Rep ∈ familyRep から I ∈ family V R₁
    have hsub : I ⊆ V := h.1
    have hBfamRep : I ∩ Rep (Q := Q) ∈ familyRep (V := V) (R := R) (Q := Q) := h.2
    -- family の形に戻す
    have hpow_and_closed :
        I ∩ Rep (Q := Q) ∈ (Rep (Q := Q)).powerset
        ∧ isClosed (R1 (V := V) (R := R) (Q := Q)) (I ∩ Rep (Q := Q)) :=
      Finset.mem_filter.mp hBfamRep
    have hclosedIrep : isClosed (R1 (V := V) (R := R) (Q := Q)) (I ∩ Rep (Q := Q)) :=
      hpow_and_closed.2
    -- I の閉性へ（同値の逆向きを使う）
    have hclosedI : isClosed (R1 (V := V) (R := R) (Q := Q)) I :=
      (hceq.mpr hclosedIrep)
    -- family へ
    have hpow : I ∈ V.powerset := Finset.mem_powerset.mpr hsub
    exact (Finset.mem_filter.mpr (And.intro hpow hclosedI))

-------------excess用

/-- `I ⊆ B ∪ S` なら `I \ B ⊆ S`。 -/
lemma sdiff_subset_of_subset_union
  {I B S : Finset α} (h : I ⊆ B ∪ S) :
  I \ B ⊆ S := by
  intro x hx
  have hxI  : x ∈ I := (Finset.mem_sdiff.mp hx).1
  have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hx).2
  have hxUnion : x ∈ B ∪ S := h hxI
  rcases Finset.mem_union.mp hxUnion with hxB | hxS
  · simp_all only [Finset.mem_sdiff, not_false_eq_true, and_self, not_true_eq_false]
  · exact hxS

/-- `B ⊆ I` なら `B ∪ (I \ B) = I`。 -/
lemma union_sdiff_eq_of_subset
  {I B : Finset α} (h : B ⊆ I) :
  B ∪ (I \ B) = I := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxB | hxDiff
    · exact h hxB
    · exact (Finset.mem_sdiff.mp hxDiff).1
  · intro hxI
    by_cases hxB : x ∈ B
    · exact Finset.mem_union.mpr (Or.inl hxB)
    · -- x∈I かつ x∉B なので x∈I\B
      have hxDiff : x ∈ I \ B := Finset.mem_sdiff.mpr ⟨hxI, hxB⟩
      exact Finset.mem_union.mpr (Or.inr hxDiff)

/- 画像の濃度が単射性で等しい（Finset 版 InjOn wrapper）。 -/
omit [DecidableEq α] in
lemma card_image_eq_of_injOn
  {β : Type u} [DecidableEq β]
  {s : Finset α} {f : α → β}
  (hinj : ∀ {a} (_ : a ∈ s) {b} (_ : b ∈ s), f a = f b → a = b) :
  (s.image f).card = s.card := by
  classical
  -- `card_image_iff` は「↔」形の単射性を要求するので、逆向きは自明で埋める
  have hiff :
      ∀ {a} (ha : a ∈ s) {b} (hb : b ∈ s), (f a = f b ↔ a = b) := by
    intro a ha b hb
    constructor
    · intro h; exact hinj ha hb h
    · intro h; cases h; rfl
  exact Finset.card_image_iff.mpr (by intro a ha b hb; exact fun a_1 => hinj ha hb a_1)

/-- Int 版：非負な各項の和は非負。 -/
lemma sum_nonneg_int
  {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (f : ι → Int)
  (h : ∀ i ∈ s, 0 ≤ f i) :
  0 ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    have h0a : 0 ≤ f a := h a (by exact Finset.mem_insert_self a s)
    have h0s : ∀ i ∈ s, 0 ≤ f i := by

      intro i hi; exact h i (Finset.mem_insert_of_mem hi)
    have : 0 ≤ ∑ i ∈ s, f i := by exact ih h0s
    -- 0 ≤ f a + ∑ … ≤> 0 ≤ ∑ over insert
    have := add_nonneg h0a this
    -- 展開
    simpa [Finset.sum_insert, ha] using this

/-- 各項が `≤ C` なら、和は `≤ C * |s|`（Nat を Int に鋳造して使いやすい形）。 -/
lemma sum_natCast_le_bound_mul_card
  {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (g : ι → Nat) (C : Nat)
  (hbound : ∀ i ∈ s, g i ≤ C) :
  ∑ i ∈ s, (g i : Int) ≤ (C : Int) * s.card := by
  classical
  --refine Finset.induction_on s ?base ?step
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    have ha_le : (g a : Int) ≤ C := by

      have := hbound a (by exact Finset.mem_insert_self a s)
      exact_mod_cast this
    have hs_le :
        ∑ i ∈ s, (g i : Int) ≤ (C : Int) * s.card := by
      simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, Nat.cast_le]
    -- 目標： (g a) + ∑_s ≤ C + C * |s| = C * (|s|+1)
    have : (g a : Int) + ∑ i ∈ s, (g i : Int)
            ≤ (C : Int) + (C : Int) * s.card :=
      add_le_add ha_le hs_le
    -- 整理
    have hcard : ((s.card.succ : Nat) : Int) = (s.card : Int) + 1 := by
      -- これは後で `by` 展開せずとも `Nat.succ_eq_add_one` から移送して可
      -- ただ、右辺で使うのは `(C:Int) * (s.card + 1)`
      rfl
    -- sum_insert 展開と右辺の因数まとめ
    have := this
    -- 左展開
    have hL :
        (∑ i ∈ insert a s, (g i : Int))
          = (g a : Int) + ∑ i ∈ s, (g i : Int) := by
      simp [Finset.sum_insert, ha]
    -- 右展開
    have hR :
        (C : Int) * (insert a s).card
          = (C : Int) + (C : Int) * s.card := by
      -- |insert a s| = s.card + 1
      -- 右辺 = C * (s.card + 1) = C + C*|s|
      have : (insert a s).card = s.card + 1 := by
        simp_all only [Finset.mem_insert, or_true, implies_true, forall_eq_or_imp, Nat.cast_le,
          Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, not_false_eq_true, Finset.sum_insert,
          Finset.card_insert_of_notMem]

      calc
        (C : Int) * (insert a s).card
            = (C : Int) * (s.card + 1) := by
                  exact congrArg (fun n : Nat => (C : Int) * n) this
        _   = (C : Int) * s.card + (C : Int) * 1 := by
                  ring
        _   = (C : Int) * s.card + (C : Int) := by simp
        _   = (C : Int) + (C : Int) * s.card := by
                  ac_rfl
    -- 置換して完了
    have := le_trans (by simpa [hL] using this) (by exact Int.le_refl (↑C + ↑C * ↑s.card))
    simp_all only [Finset.mem_insert, or_true, implies_true, forall_eq_or_imp, Nat.cast_le,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, not_false_eq_true, Finset.sum_insert,
      Finset.card_insert_of_notMem]


/- `|𝒫(S)| = 2^{|S|}` の Int 版。 -/
omit [DecidableEq α] in
lemma card_powerset_pow_int (S : Finset α) :
  ((S.powerset.card : Nat) : Int) = ((2 : Nat) ^ S.card : Int) := by
  have h := Finset.card_powerset S
  simp_all only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]

--Mainから使う予定

--ProblemAでも使う。
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
