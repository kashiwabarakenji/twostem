import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import LeanCopilot

open scoped BigOperators

namespace Twostem
open Closure

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Rules and basic predicates (assume your existing `Rule` etc. are imported). -/
-- placeholder: `Rule α` should already be defined in your project
def UC (R : Finset (Rule α)) : Prop :=
  ∀ a : α, (R.filter (fun t => t.head = a)).card ≤ 1

-- Closed family w.r.t. rules R
@[simp] def IsClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ ⦃t : Rule α⦄, t ∈ R → t.prem ⊆ I → t.head ∈ I

/-- Rules applicable to I (prem ⊆ I ∧ head ∉ I). -/
@[simp] def applicable (R : Finset (Rule α)) (I : Finset α) : Finset (Rule α) :=
  R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I)

/-- All heads that can fire in one step. -/
--@[simp] def fires [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
--  (R.filter (fun t => t.prem ⊆ I)).image (fun t => t.head)

@[simp] def fires (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  (applicable R I).image (fun t => t.head)


/-- One-step expansion by firing all currently applicable heads. -/
@[simp] def step [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  I ∪ fires R I

/- Monotonicity of `fires`.
--成り立たないらしい。
lemma fires_mono {α : Type*} [DecidableEq α]
  (R : Finset (Rule α)) : Monotone (fires R) := by
-/

/-- Inflationary: `I ⊆ step R I`. -/
lemma step_infl {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
  ∀ s, s ⊆ step R s := by
  intro s x hx;
  dsimp [step];
  simp_all only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, true_or]

/-- I ⊆ J → fires R I ⊆ step R J -/
lemma fires_subset_step_of_subset
  {R : Finset (Rule α)} {I J : Finset α}
  (hIJ : I ⊆ J) : fires R I ⊆ step R J := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨t, htI, hEq⟩
  -- htI : t ∈ applicable R I
  -- 分解：t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I
  have hsplit : t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I :=
    Finset.mem_filter.mp htI
  have hPremJ : t.prem ⊆ J := Finset.Subset.trans hsplit.2.1 hIJ
  by_cases hHeadJ : t.head ∈ J
  · -- 左側（J）に入る
    have : a ∈ J := by
      -- hEq : t.head = a
      have ht : t.head ∈ J := hHeadJ
      have h' : a ∈ J := by
        -- t.head = a で書き換え
        have tmp := ht
        rw [hEq] at tmp
        exact tmp
      exact h'
    exact Finset.mem_union.mpr (Or.inl this)
  · -- 右側（fires R J）に入る
    have htJ : t ∈ applicable R J := by
      -- 組み立て：t ∈ R ∧ prem ⊆ J ∧ head ∉ J
      exact Finset.mem_filter.mpr ⟨hsplit.1, And.intro hPremJ hHeadJ⟩
    have : a ∈ fires R J := by
      exact Finset.mem_image.mpr ⟨t, htJ, hEq⟩
    exact Finset.mem_union.mpr (Or.inr this)

/-- 並列ステップは単調：I ⊆ J → step R I ⊆ step R J -/
lemma step_mono {α : Type*} [DecidableEq α][Fintype α]
  (R : Finset (Rule α)) : Monotone (step R) := by
  intro I J hIJ x hx
  rcases Finset.mem_union.mp hx with hxI | hxF
  · exact Finset.mem_union.mpr (Or.inl (hIJ hxI))
  · exact (fires_subset_step_of_subset (R:=R) (I:=I) (J:=J) hIJ) hxF

def stepPar (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  I ∪ fires R I

def parIter (R : Finset (Rule α)) (I : Finset α) : Nat → Finset α
  | 0     => I
  | k+1   => stepPar R (parIter R I k)

lemma parIter_mono_in_steps [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) (k : ℕ) :
  parIter R I k ⊆ parIter R I (k + 1) := by
  cases k with
  | zero =>
    simp [parIter, stepPar]
  | succ k =>
    simp only [parIter]
    unfold stepPar
    exact Finset.subset_union_left

lemma parIter_increasing [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) :
  ∀ k₁ k₂, k₁ ≤ k₂ → parIter R I k₁ ⊆ parIter R I k₂ := by
  intro k₁ k₂ h
  induction h with
  | refl => rfl
  | step h ih =>
    exact Finset.Subset.trans ih (parIter_mono_in_steps R I _)

lemma parIter_mono {α : Type*} [DecidableEq α][Fintype α]
  (R : Finset (Rule α)) (k : Nat) :
  Monotone (parIter R · k) := by
  intro I J hIJ
  induction k with
  | zero =>
      -- parIter R I 0 = I
      exact hIJ
  | succ k ih =>
      -- 目標: parIter R I (k+1) ⊆ parIter R J (k+1)
      intro x hx
      -- parIter の定義を「型の変更(change)」で開く
      have hxStep : x ∈ step R (parIter R I k) := by
        -- hx : x ∈ parIter R I (k+1)
        -- parIter R I (k+1) は定義的に step R (parIter R I k)
        have h0 := hx
        change x ∈ step R (parIter R I k) at h0
        exact h0
      -- 帰納法の仮定と step_mono から包含を得る
      have hIncl : step R (parIter R I k) ⊆ step R (parIter R J k) := by
        apply step_mono R
        exact ih
      have hx' : x ∈ step R (parIter R J k) := hIncl hxStep
      -- ゴール側も parIter を定義で「型の変更」
      change x ∈ step R (parIter R J k)
      exact hx'


lemma stepPar_mono (R : Finset (Rule α)) :
  Monotone (stepPar R) := by
  intro I J hIJ
  unfold stepPar
  intro x hx
  cases Finset.mem_union.mp hx with
  | inl hxI => exact Finset.mem_union_left _ (hIJ hxI)
  | inr hxF =>
    -- x ∈ fires R I
    obtain ⟨t, ht_app, ht_head⟩ := Finset.mem_image.mp hxF
    simp [Finset.mem_filter] at ht_app
    subst ht_head
    simp_all only [Finset.le_eq_subset, fires, Finset.mem_union, Finset.mem_image, or_true]
    obtain ⟨left, right⟩ := ht_app
    obtain ⟨w, h⟩ := hxF
    obtain ⟨left_1, right_1⟩ := h
    simp_all only [applicable, Finset.mem_filter, not_false_eq_true, and_true]
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_1, right_2⟩ := left_1
    tauto

/-- 1ステップで生じる新規 head は高々1個（R' 用）。-/
def NoTwoFreshHeads (R' : Finset (Rule α)) : Prop :=
  ∀ I, (fires R' I).card ≤ 1

/-- 交換禁止：1ステップ像が等しければ差は片側にしかない。-/
def NoSwap (R' : Finset (Rule α)) : Prop :=
  ∀ X Y, stepPar R' X = stepPar R' Y → ((X \ Y) = ∅ ∨ (Y \ X) = ∅)

/-! 補助：`stepPar R X = stepPar R Y` のとき、`X \ Y ⊆ fires R Y` / `Y \ X ⊆ fires R X` -/
lemma diff_subset_fires_right
  {R : Finset (Rule α)} {X Y : Finset α}
  (hstep : stepPar R X = stepPar R Y) :
  (X \ Y) ⊆ fires R Y := by
  intro a ha
  have haX  : a ∈ X := (Finset.mem_sdiff.mp ha).1
  have haNY : a ∉ Y := (Finset.mem_sdiff.mp ha).2
  have ha_in_stepX : a ∈ stepPar R X := Finset.mem_union.mpr (Or.inl haX)
  have ha_in_stepY : a ∈ stepPar R Y := by
    have tmp := ha_in_stepX
    -- 書き換え：stepPar R X = stepPar R Y
    rw [hstep] at tmp
    exact tmp
  -- Y にいないので、stepPar R Y の右側（fires）にいる
  have hsplit := Finset.mem_union.mp ha_in_stepY
  cases hsplit with
  | inl hInY  => exact (haNY hInY).elim
  | inr hInFY => exact hInFY

lemma diff_subset_fires_left
  {R : Finset (Rule α)} {X Y : Finset α}
  (hstep : stepPar R X = stepPar R Y) :
  (Y \ X) ⊆ fires R X := by
  -- 対称版：上の補題を対称に使ってもよいが、ここでは直接書く
  intro a ha
  have haY  : a ∈ Y := (Finset.mem_sdiff.mp ha).1
  have haNX : a ∉ X := (Finset.mem_sdiff.mp ha).2
  have ha_in_stepY : a ∈ stepPar R Y := Finset.mem_union.mpr (Or.inl haY)
  have ha_in_stepX : a ∈ stepPar R X := by
    have tmp := ha_in_stepY
    -- 対称に書き換え
    have hsym : stepPar R Y = stepPar R X := Eq.symm hstep
    rw [hsym] at tmp
    exact tmp
  have hsplit := Finset.mem_union.mp ha_in_stepX
  cases hsplit with
  | inl hInX  => exact (haNX hInX).elim
  | inr hInFX => exact hInFX

/-- **last-diff is singleton**：
`k+1` 段で一致する（= 最小一致段を想定）とき、`k` 段の差はちょうど1点。-/
lemma lastDiff_is_singleton
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α} {k : ℕ}
  (hNe :
    ((parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)).Nonempty)
  (hEq : parIter R' U (k+1) = parIter R' V (k+1)) :
  ∃! f,
    f ∈ (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k) := by
  classical
  -- 記号：X,Y
  set X := parIter R' U k
  set Y := parIter R' V k
  -- 次段の一致を step レベルに引き直す
  have hstep : stepPar R' X = stepPar R' Y := by
    -- parIter … (k+1) = stepPar R' X, stepPar R' Y
    have hx : parIter R' U (k+1) = stepPar R' X := rfl
    have hy : parIter R' V (k+1) = stepPar R' Y := rfl
    -- hEq を書き換え
    have tmp := hEq
    rw [hx] at tmp
    rw [hy] at tmp
    exact tmp
  -- NoSwap：差は片側のみ
  have hside : (X \ Y = ∅) ∨ (Y \ X = ∅) := hNS X Y hstep
  -- 片側ずつ場合分け
  cases hside with
  | inl hXYempty =>
    -- union = (X\Y) ∪ (Y\X) = ∅ ∪ (Y\X) = (Y\X)
    have hunion_eq : (X \ Y ∪ Y \ X) = (Y \ X) := by
      -- 左を右へ：X\Y = ∅ を使う
      -- `by_ext` で両包含でもよいが、ここは素直に書き換え
      have : X \ Y = ∅ := hXYempty
      -- union の左を空に
      -- `rw [this, empty_union]` で可
      -- ただし「simpa using」を避けるため、逐次 rw
      -- まず union の左を置換
      -- （Lean では `rw` で十分）
      -- 注意：ここで union の左右の型整合をそのまま利用
      -- 実行：
      -- ここからは簡潔に：
      -- rw [this, empty_union]
      -- 直接書換
      have h1 : (∅ ∪ (Y \ X)) = (Y \ X) := by exact Finset.empty_union (Y \ X)
      -- 以上を一気に反映
      -- いったん goal を `X\Y ∪ Y\X` から `∅ ∪ Y\X` に差し替える
      -- 簡便に：`calc` で書く
      calc
        (X \ Y ∪ Y \ X) = (∅ ∪ Y \ X) := by rw [this]
        _ = (Y \ X) := h1
    -- 非空性を右側へ移す
    have hNeRight : (Y \ X).Nonempty := by
      -- hNe は union の非空
      -- hunion_eq : union = (Y \ X)
      -- これで落とす
      -- `Nonempty` は `Finset.card_pos` でも良いが、ここは `Nonempty` のまま移送
      -- `hNe` の witness をそのまま使う
      rcases hNe with ⟨a, ha⟩
      have : a ∈ (Y \ X) := by
        -- ha : a ∈ (X \ Y ∪ Y \ X)
        -- 書き換え
        -- rw [hunion_eq] at ha; exact ha
        have tmp := ha
        rw [hunion_eq] at tmp
        exact tmp
      exact ⟨a, this⟩
    -- (Y\X) は fires R' X の部分集合 ⇒ card ≤ 1
    have hsub : (Y \ X) ⊆ fires R' X := diff_subset_fires_left (R:=R') (X:=X) (Y:=Y) hstep
    have hcard_le_one : (Y \ X).card ≤ 1 := by
      -- card ≤ card(fires R' X) ≤ 1
      -- まず部分集合から card 上界
      have hle : (Y \ X).card ≤ (fires R' X).card :=
        Finset.card_le_card hsub
      -- NoTwoFreshHeads
      have hfe : (fires R' X).card ≤ 1 := hNTF X
      exact Nat.le_trans hle hfe
    -- 非空 ＆ card ≤ 1 ⇒ card = 1
    have hpos : 0 < (Y \ X).card := Finset.card_pos.mpr hNeRight
    have hone : (Y \ X).card = 1 := by
      -- 1 ≤ card ∧ card ≤ 1 ⇒ card = 1
      have hge1 : 1 ≤ (Y \ X).card := Nat.succ_le_of_lt hpos
      -- 1 = card
      have h1eq : 1 = (Y \ X).card := Nat.le_antisymm hge1 hcard_le_one
      exact Eq.symm h1eq
    -- card = 1 から一意存在へ
    -- `card_eq_one` : s.card = 1 ↔ ∃ a, s = {a}
    rcases Finset.card_eq_one.mp hone with ⟨f, hfset⟩
    -- 目的：∃! f, f ∈ union
    refine ExistsUnique.intro f ?hexists ?huniq
    · -- 存在
      -- f ∈ (Y\X) = union
      have hf_in : f ∈ (Y \ X) := by
        -- f ∈ {f} ↔ ...
        -- `hfset : (Y\X) = {f}` の対称で書き換え
        -- `mem_singleton_self` を使う
        have : f ∈ ({f} : Finset α) := by
          -- `mem_singleton` の自明
          exact Finset.mem_singleton_self f
        -- 書き換え
        -- {f} = (Y\X) の形にしたいので対称に
        have hfset' : {f} = (Y \ X) := Eq.symm hfset
        -- rewrite
        have tmp := this
        -- rw [hfset'] at tmp
        -- exact tmp
        -- 逐次書換
        rw [hfset'] at tmp
        exact tmp
      -- union 側へ移す
      -- union = (Y\X)
      have : f ∈ (X \ Y ∪ Y \ X) := by
        -- 書換
        -- rw [hunion_eq] で右辺へ
        have tmp := hf_in
        -- 逆向きに戻す
        -- rw [← hunion_eq] at tmp; exact tmp
        -- ここでは直接書き換え
        -- `hunion_eq : (X\Y ∪ Y\X) = (Y\X)`
        -- その対称で置換
        have hsym : (Y \ X) = (X \ Y ∪ Y \ X) := Eq.symm hunion_eq
        -- rewrite
        have tmp2 := tmp
        rw [hsym] at tmp2
        exact tmp2
      exact this
    · -- 一意性
      intro g hg
      -- union = (Y\X)
      have hgYX : g ∈ (Y \ X) := by
        -- rw [hunion_eq] at hg; exact hg
        have tmp := hg
        rw [hunion_eq] at tmp
        exact tmp
      -- (Y\X) = {f}
      -- したがって g = f
      -- `hfset : (Y\X) = {f}`
      -- 書き換え
      have : g ∈ ({f} : Finset α) := by
        -- 対称で置換
        have hsym : ({f} : Finset α) = (Y \ X) := Eq.symm hfset
        -- rewrite
        have tmp := hgYX
        -- rw [hsym] at tmp
        -- exact tmp
        rw [←hsym] at tmp
        exact tmp


      -- 1点集合の会員なら要素は f
      -- `mem_singleton` で落とす
      -- `mem_singleton.mp` を直接使わずに等式で示すなら：
      -- ここは簡潔に：
      -- `by` でケース分けでもよいが、`mem_singleton` を使う
      have : g = f := by
        -- `mem_singleton.mp this`
        exact Finset.mem_singleton.mp this
      -- 終了
      exact this
  | inr hYXempty =>
    -- 対称ケース：union = (X\Y)
    have hunion_eq : (X \ Y ∪ Y \ X) = (X \ Y) := by
      -- 対称に空を右に
      -- union_comm を使わずに計算
      have : (Y \ X) = ∅ := hYXempty
      -- (X\Y) ∪ ∅ = (X\Y)
      have h1 : (X \ Y ∪ ∅) = (X \ Y) := by exact Finset.union_empty (X \ Y)
      calc
        (X \ Y ∪ Y \ X) = (X \ Y ∪ ∅) := by rw [this]
        _ = (X \ Y) := h1
    have hNeLeft : (X \ Y).Nonempty := by
      rcases hNe with ⟨a, ha⟩
      have : a ∈ (X \ Y) := by
        have tmp := ha
        rw [hunion_eq] at tmp
        exact tmp
      exact ⟨a, this⟩
    -- (X\Y) ⊆ fires R' Y
    have hsub : (X \ Y) ⊆ fires R' Y := diff_subset_fires_right (R:=R') (X:=X) (Y:=Y) hstep
    have hcard_le_one : (X \ Y).card ≤ 1 := by
      have hle : (X \ Y).card ≤ (fires R' Y).card :=
        Finset.card_le_card hsub
      have hfe : (fires R' Y).card ≤ 1 := hNTF Y
      exact Nat.le_trans hle hfe
    -- 非空 ⇒ card = 1
    have hpos : 0 < (X \ Y).card := Finset.card_pos.mpr hNeLeft
    have hone : (X \ Y).card = 1 := by
      have hge1 : 1 ≤ (X \ Y).card := Nat.succ_le_of_lt hpos
      have h1eq : 1 = (X \ Y).card := Nat.le_antisymm hge1 hcard_le_one
      exact Eq.symm h1eq
    rcases Finset.card_eq_one.mp hone with ⟨f, hfset⟩
    refine ExistsUnique.intro f ?hexist ?huni
    · -- 存在
      have hf_in : f ∈ (X \ Y) := by
        -- f ∈ {f} → 書換
        have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
        have hsym : {f} = (X \ Y) := Eq.symm hfset
        have tmp := this
        rw [hsym] at tmp
        exact tmp
      have : f ∈ (X \ Y ∪ Y \ X) := by
        -- 書換
        have hsym : (X \ Y) = (X \ Y ∪ Y \ X) := Eq.symm hunion_eq
        have tmp := hf_in
        rw [hsym] at tmp
        exact tmp
      exact this
    · -- 一意
      intro g hg
      have hgXL : g ∈ (X \ Y) := by
        have tmp := hg
        rw [hunion_eq] at tmp
        exact tmp
      have : g ∈ ({f} : Finset α) := by
        have hsym : ({f} : Finset α) = (X \ Y) := Eq.symm hfset
        have tmp := hgXL
        rw [←hsym] at tmp
        exact tmp
      exact Finset.mem_singleton.mp this
