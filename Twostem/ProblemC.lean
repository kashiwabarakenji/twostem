import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Twostem.Basic
import LeanCopilot
open scoped Rat
--import Mathlib.Tactic.NormCast

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

namespace ThreadC
open scoped BigOperators

abbrev Rule (α) := α × α × α

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

--def contractRules
--  (p : α → β) [DecidableEq β] (R : Finset (Rule α)) : Finset (β × β × β) :=
--  (R.image (fun t => (p t.1, p t.2.1, p t.2.2)))
def contractRules {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α) (R : Finset (Rule α)) : Finset (Rule α) := R.image (fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2)))

lemma supportedOn_contractRules (V : Finset α) (R : Finset (Rule α)) {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α)-- (hV : supportedOn V R)
 (hσ : ∀ b, σ b ∈ V) :
 supportedOn V (contractRules (π := π) (σ := σ) R) := by

  intro t ht
  -- t は像：∃ s∈R, t = (σ (π s.1), σ (π s.2.1), σ (π s.2.2))
  rcases Finset.mem_image.mp ht with ⟨s, hsR, hmap⟩
  -- s の各成分は V にある
  subst hmap
  simp_all only [and_self]

lemma card_contractRules_le
  (R : Finset (Rule α))
  {β : Type u} [DecidableEq β] (π : α → β) (σ : β → α) :
  (contractRules (π := π) (σ := σ) R).card ≤ R.card := by
  -- 画像の濃度は元の濃度以下（基本事実）
  exact Finset.card_image_le
    (s := R) (f := fun t => (σ (π t.1), σ (π t.2.1), σ (π t.2.2)))

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

end ThreadC
