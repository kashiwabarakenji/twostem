import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import LeanCopilot

open scoped BigOperators

namespace Twostem
open Closure
open Finset

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


--使われている。
lemma disjoint_union_eq_implies_right_eq
  {α : Type*} [DecidableEq α]
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (h : B ∪ S₁ = B ∪ S₂) : S₁ = S₂ := by
  classical
  apply le_antisymm
  · -- S₁ ⊆ S₂
    intro x hx
    -- x ∈ S₁。互いに素なので x ∉ B。
    have hxNB : x ∉ B := by
      -- `Disjoint` → `x ∈ S₁` かつ `x ∈ B` は両立しない
      -- `disjoint_left.mp hD1` を使う手もあるが、ここは素朴に：
      intro hxB
      -- x ∈ B ∩ S₁ の矛盾を作る
      have : x ∈ B ∩ S₁ := by exact mem_inter.mpr ⟨hxB, hx⟩
      -- `hD1` から `B ∩ S₁ = ∅`
      have hIntEmpty : B ∩ S₁ = (∅ : Finset α) := by
        -- `Disjoint` の定義：`disjoint_left`/`disjoint_right` 等でもOK
        -- ここでは `disjoint_iff` を使っても良いが、簡便に：
        -- Mathlib: `disjoint_left.mp hD1 x hxB hx` で矛盾にできる
        have contra := (disjoint_left.mp hD1) hxB hx
        exact by cases contra
      -- 空集合の要素にする：
      have : x ∈ (∅ : Finset α) := by simp_all only [notMem_empty]
      exact (notMem_empty x) this
    -- 和の等式から x ∈ B ∪ S₂
    have hxInUnion : x ∈ B ∪ S₂ := by
      have : x ∈ B ∪ S₁ := by exact mem_union.mpr (Or.inr hx)
      have := congrArg (fun (s : Finset α) => x ∈ s) h
      -- 書き換え： `x ∈ B ∪ S₁` ≡ `x ∈ B ∪ S₂`
      -- term で直接使うなら：
      -- `rw [h] at this` の代わりに次の2行で：
      -- （ここは戦術的に `have` を使っても良い）
      -- 簡便のため次を採用
      -- 実際の環境では `rw [h]` でOKです
      exact by
        -- tactic が使えるなら：`simpa [h] using this`
        -- ここでは直接：
        -- 既に x∈B∪S₁ を持っており、h : B∪S₁ = B∪S₂ なので差し替え可
        -- いったん rfl 書換に近い扱いをします
        -- ただしチャットでは簡潔に：
        -- （エディタでは `have := this; simpa [h] using this` が楽）
        simp_all only [mem_union, false_or, or_true]
    -- x ∉ B なので、x ∈ S₂
    have : x ∈ S₂ := by
      rcases mem_union.mp hxInUnion with hxB | hxS2
      · exact False.elim (hxNB hxB)
      · exact hxS2
    exact this
  · -- 対称に S₂ ⊆ S₁
    intro x hx
    have hxNB : x ∉ B := by
      intro hxB
      have : x ∈ B ∩ S₂ := by exact mem_inter.mpr ⟨hxB, hx⟩
      -- 同様に `Disjoint B S₂`
      have hIntEmpty : B ∩ S₂ = (∅ : Finset α) := by
        have contra := (disjoint_left.mp hD2) hxB hx
        exact by cases contra
      have : x ∈ (∅ : Finset α) := by
        have hx' : x ∈ B ∩ S₂ := this
        rw [hIntEmpty] at hx'     -- B ∩ S₂ を ∅ に書き換え
        exact hx'
      exact (notMem_empty x) this
    have hxInUnion : x ∈ B ∪ S₁ := by
      have : x ∈ B ∪ S₂ := mem_union.mpr (Or.inr hx)
      -- x ∈ B ∪ S₁ を得るには `h.symm` で書換
      exact by
        -- tactic なら：`simpa [h.symm] using this`
        simp_all only [mem_union, or_true]
    have : x ∈ S₁ := by
      rcases mem_union.mp hxInUnion with hxB | hxS1
      · exact False.elim (hxNB hxB)
      · exact hxS1
    exact this

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

--/***********************
-- * 1. ルール順序(first violationあたり)
-- ***********************/

structure RuleOrder (α) where
  carrier : List (Rule α)
  nodup   : carrier.Nodup

variable {R : Finset (Rule α)}

def RuleOrder.ruleIndex (ρ : RuleOrder α) (t : Rule α) : Nat :=
  ρ.carrier.findIdx (fun s => decide (s = t))

noncomputable def firstRule (ρ : RuleOrder α) (S : Finset (Rule α)) : Option (Rule α) :=
  S.val.toList.argmin (fun t => ρ.ruleIndex t)

--/***********************
-- * 2. 「最初の違反」
-- ***********************/
def violates (R : Finset (Rule α)) (t : Rule α) (I : Finset α) : Prop :=
  t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I

def violatesFirst (ρ : RuleOrder α) (R : Finset (Rule α))
    (t : Rule α) (I : Finset α) : Prop :=
  violates R t I ∧
  (∀ s, violates R s I → ρ.ruleIndex t ≤ ρ.ruleIndex s)

--omit [DecidableEq α][Fintype α] [LinearOrder α] in
lemma violates_not_closed {ρ} {R} {t : Rule α} {I}
  (h : violatesFirst ρ R t I) : ¬ IsClosed R I := by
  intro hcl
  rcases h with ⟨⟨hR, hPrem, hHead⟩, _⟩
  have : t.head ∈ I := hcl (t:=t) hR hPrem
  exact hHead this

--omit [Fintype α] [LinearOrder α] in
lemma exists_first_violation
  (ρ : RuleOrder α) (R : Finset (Rule α)) (I : Finset α) :
  (¬ IsClosed R I) → ∃ t, violatesFirst ρ R t I := by
  classical
  intro hnot
  -- 適用可能で head ∉ I の規則の集合
  let V : Finset (Rule α) :=
    R.filter (fun t => (t.prem ⊆ I) ∧ t.head ∉ I)

  -- V は空でないことを示す（空だと IsClosed になって矛盾）
  have V_nonempty : V.Nonempty := by
    by_contra h'
    -- V = ∅ だと各 t∈R, prem⊆I に対し head∈I が従う
    have hClosed : IsClosed R I := by
      intro t ht hsub
      -- もし head ∉ I なら t ∈ V で V.Nonempty を作れて矛盾
      by_contra hhead
      have htV : t ∈ V := by
        -- t ∈ R ∧ (prem⊆I ∧ head∉I) なので filter に入る
        have : t ∈ R ∧ ((t.prem ⊆ I) ∧ t.head ∉ I) := ⟨ht, ⟨hsub, hhead⟩⟩
        simpa [V, mem_filter] using this
      exact h' ⟨t, htV⟩
    exact hnot hClosed

  -- V の中で ρ.ruleIndex を最小化する元 t を取る
  obtain ⟨t, htV, hmin⟩ :
      ∃ t ∈ V, ∀ t' ∈ V, ρ.ruleIndex t ≤ ρ.ruleIndex t' := by
    classical
    -- `exists_min_image` の型は `∃ a ∈ s, ∀ b ∈ s, f a ≤ f b`
    -- ここでは s = V, f = ρ.ruleIndex
    simpa using
      Finset.exists_min_image (s := V) (f := fun t => ρ.ruleIndex t) V_nonempty

  refine ⟨t, ?hf⟩
  constructor
  · -- t は定義上「違反」している
    have : t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I := by
      have : t ∈ V := htV
      simpa [V, mem_filter] using this
    simpa [violates] using this
  · -- ρ の最小性
    intro s hs
    have hsV : s ∈ V := by
      rcases hs with ⟨hsR, hsp, hsh⟩
      simp_all only [mem_filter, and_imp, not_false_eq_true, and_self, V]
    exact hmin s hsV



--/***********************
-- * 3. 正規極小証人（辞書式一意化）
--- ***********************/
variable (Rep : Finset α)
--def FreeOf (Rep : Finset α) : Finset α := (univ : Finset α) \ Rep
/-- 自由座標（台は univ を想定） -/
def FreeOf (Rep : Finset α) : Finset α :=
  (univ : Finset α) \ Rep

def isWitness [Fintype α] [DecidableEq α] [LinearOrder α] (ρ : RuleOrder α) (R : Finset (Rule α))
    (B S : Finset α) (t : Rule α) : Prop :=
  (S ⊆ FreeOf (α:=α) B) ∧ violatesFirst ρ R t (B ∪ S)

/-- 候補：Free からとった部分集合で、t が first violation になるもの -/
private noncomputable def witnessCandidates
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Finset (Finset α) :=
by
  classical
  -- powerset 上で「t が最小違反 head になるような拡張 S」をフィルタ
  exact (FreeOf (α:=α) B).powerset.filter
    (fun S =>
      violates R t (B ∪ S)
      ∧ ∀ s, violates R s (B ∪ S) → ρ.ruleIndex t ≤ ρ.ruleIndex s)

/-- inclusion 極小元の集合 -/
private def inclusionMinimals (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun S => ∀ S' ∈ F, S' ⊆ S → S = S')

/-- Finset をソートした `List α` に変換（辞書式比較用） -/
private def asLexList [LinearOrder α](S : Finset α) : List α :=
  S.sort (· ≤ ·)

/-- 「辞書式最小」の 1 要素を返す（Nonempty を仮定） -/
private noncomputable def chooseLexMin [LinearOrder α] (F : Finset (Finset α)) : Option (Finset α) :=
  -- `F.val : Multiset (Finset α)` → `toList : List (Finset α)`
  -- `argmin? (asLexList)` でキー最小の要素を `Option` で取得
  (F.val.toList).argmin asLexList

/-
/-- 正規極小証人を返す：候補が空なら none -/
noncomputable def lexMinWitness
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Option (Finset α) := by
  classical
  let cand := witnessCandidates (α:=α) ρ R B t
  let mins := inclusionMinimals cand    -- : Finset (Finset α)
  exact chooseLexMin mins               -- : Option (Finset α)
-/

/-- 返した witness が本当に witness -/
noncomputable def lexMinWitness
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Option (Finset α) := by
  classical
  let cand := witnessCandidates (α:=α) ρ R B t
  let mins := inclusionMinimals cand
  exact if h : mins.Nonempty then some (Classical.choose h) else none

lemma lexMinWitness_isWitness [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α)
  (h : ∃ S, lexMinWitness (α:=α) ρ R B t = some S) :
  ∃ S, isWitness (α:=α) ρ R B S t := by
  classical
  -- 展開
  rcases h with ⟨S, hS⟩
  dsimp [lexMinWitness] at hS
  set cand := witnessCandidates (α:=α) ρ R B t with hcand
  set mins := inclusionMinimals cand with hmins
  by_cases hne : mins.Nonempty
  · -- then 分岐：`some (Classical.choose hne)` と一致
    have hS' : some (Classical.choose hne) = some S := by
    -- 依存 if を評価する等式
      have hreduce :
          (if h : mins.Nonempty then some (Classical.choose h) else none)
            = some (Classical.choose hne) :=
        dif_pos hne
      -- hS は dsimp で展開済み：左辺が今の if 式
      exact hreduce.symm.trans hS
    -- 中身を取り出し
    have S_eq : Classical.choose hne = S := Option.some.inj hS'
    subst S_eq
    -- `S ∈ mins`
    have S_in_mins : Classical.choose hne ∈ mins :=
      Classical.choose_spec hne
    /- inclusionMinimals の定義に依存：
       ここでは `mins = cand.filter P` の形だとし，mem_filter で分解する -/
    have S_in_cand_andP :
        Classical.choose hne ∈ cand ∧
        True := by
      -- P の具体は使わないので `True` に吸収。定義があればそこに合わせて置き換えてください。
      -- `S_in_mins : _ ∈ inclusionMinimals cand` だが、いまは `mins` に畳んでいる
      -- `mins = cand.filter _` を仮定して分解
      -- 具体定義を持っているなら：`have := Finset.mem_filter.mp S_in_mins`
      -- ここでは「cand に属する」ことだけ使う：
      -- とりあえず cand に属すると仮定するヘルパ（定義に合わせて書き換えてください）
      -- （もし `inclusionMinimals` が `cand.filter P` なら次の 1 行で OK）
      simp
      have : mins ⊆ cand := by
        simp [inclusionMinimals, hmins]
      exact this S_in_mins

    have S_in_cand : Classical.choose hne ∈ cand := S_in_cand_andP.left

    -- ここから witnessCandidates の membership をほどいて3条件を抽出
    -- witnessCandidates = powerset (FreeOf B) で filter したもの
    have S_mem_filtered :
        Classical.choose hne ∈
          (Finset.powerset (FreeOf (α:=α) B)).filter
            (fun S =>
              violates R t (B ∪ S) ∧
              ∀ s, violates R s (B ∪ S) → ρ.ruleIndex t ≤ ρ.ruleIndex s) := by
      -- `hcand : cand = witnessCandidates …` を使って書き換え
      -- まず `S_in_cand : _ ∈ cand` を `witnessCandidates` へ
      -- `rw` で書き換える
      have : Classical.choose hne ∈ cand := S_in_cand
      -- `hcand` は `cand = witnessCandidates …`
      -- 右辺へ書き換え
      --   `by cases hcand; exact this` とすれば `simpa` 不要
      cases hcand
      exact this

    -- `mem_filter` で分解
    have hPair := Finset.mem_filter.mp S_mem_filtered
    -- powerset 側
    have hPow : Classical.choose hne ⊆ FreeOf (α:=α) B :=
      (Finset.mem_powerset.mp hPair.left)
    -- 述語側
    have hPred : violates R t (B ∪ Classical.choose hne)
              ∧ ∀ s, violates R s (B ∪ Classical.choose hne) → ρ.ruleIndex t ≤ ρ.ruleIndex s :=
      hPair.right

    -- 3条件をまとめて witness を構成
    refine ⟨Classical.choose hne, ?_⟩
    exact And.intro hPow (And.intro hPred.left hPred.right)

  · -- else 分岐は `none` を返すので `some S` は矛盾
    have : mins = ∅ := by
      exact not_nonempty_iff_eq_empty.mp hne
    exfalso
    rw [this] at hS
    dsimp [chooseLexMin] at hS
    simp at hS

omit [DecidableEq α]  in
/-- 返した witness が inclusion 極小 -/
lemma lexMinWitness_isInclusionMinimal
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α)
  (h : ∃ S, lexMinWitness (α:=α) ρ R B t = some S) :
  ∃ S, (S ∈ witnessCandidates ρ R B t) ∧
       (∀ S' ∈ witnessCandidates ρ R B t, S' ⊆ S → S' = S) := by
  classical
  rcases h with ⟨S, hS⟩
  dsimp [lexMinWitness] at hS
  -- 記号を固定
  set cand := witnessCandidates (α:=α) ρ R B t with hcand
  set mins := inclusionMinimals cand with hmins
  by_cases hne : mins.Nonempty
  · -- then: if を評価し，some の中身を同定
    have hreduce :
        (if h : mins.Nonempty then some (Classical.choose h) else none)
        = some (Classical.choose hne) := by
      exact dif_pos hne
    have hS' : some (Classical.choose hne) = some S :=
      hreduce.symm.trans hS
    have S_eq : Classical.choose hne = S := Option.some.inj hS'
    -- 以降 S = choose hne に統一
    subst S_eq

    -- choose hne は mins に属する
    have S_in_mins : Classical.choose hne ∈ mins :=
      Classical.choose_spec hne

    -- mins = inclusionMinimals cand を展開し，filter のメンバで分解
    -- （simpa は使わずに `cases hmins` で書き換え → `dsimp`/`unfold`）
    cases hmins
    -- ここで mins = inclusionMinimals cand に固定
    -- inclusionMinimals の定義を展開
    --dsimp [inclusionMinimals] at S_in_mins
    -- filter のメンバを分解
    have hpair := Finset.mem_filter.mp S_in_mins
    -- hpair : (choose hne ∈ cand) ∧ (∀ S' ∈ cand, S' ⊆ choose hne → S' = choose hne)
    refine ⟨Classical.choose hne, ?_, ?_⟩
    · -- cand に属する
      -- hcand : cand = witnessCandidates …
      cases hcand
      exact hpair.left
    · -- inclusion 極小性
      cases hcand
      intro S' hS' hsub
      have : mins ⊆ cand := by
        dsimp [mins]
        dsimp [inclusionMinimals]
        exact filter_subset (fun S => ∀ S' ∈ cand, S' ⊆ S → S = S') cand
      simp_all [mins, cand]
      obtain ⟨left, right⟩ := hpair
      symm
      exact right S' hS' hsub

  · -- else: if は none を返すので仮定と矛盾
    have hreduce :
        (if h : mins.Nonempty then some (Classical.choose h) else none) = none :=
      dif_neg hne
    have : none = some S := hreduce.symm.trans hS
    cases this
--------
--Rulesのところで同値な条件であるUCを定めているが微妙に違う。
def UniqueChild (α : Type _) (R : Finset (Rule α)) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ R → t₂ ∈ R → t₁.head = t₂.head → t₁ = t₂

omit [Fintype α]  in
--UCとUniqueChildの同値性の証明
lemma UniqueChild_iff_UC (R : Finset (Rule α)) :
  UniqueChild (α:=α) R ↔ UC (α:=α) R := by
  dsimp [UniqueChild, UC]
  constructor
  · intro h a
    --change (R.filter (fun t => t.head = a)).card ≤ 1
  -- 「任意の2要素が等しい」ことを示せば card ≤ 1
    apply Finset.card_le_one.mpr
    intro t₁ t₂ ht₁ ht₂
    -- filter のメンバを分解
    simp_all only [mem_filter]
    obtain ⟨left, right⟩ := t₂
    obtain ⟨left_1, right_1⟩ := ht₂
    subst right
    apply @h
    · simp_all only
    · simp_all only
    · simp_all only
  · intro h t₁ t₂ ht₁ ht₂ hhead
  -- 集合 s := { t ∈ R | t.head = t₁.head }
    let s : Finset (Rule α) := R.filter (fun t => t.head = t₁.head)

    -- t₁ ∈ s
    have ht₁s : t₁ ∈ s := by
      -- mem_filter ⇔ (mem R ∧ head=…)
      have : t₁ ∈ R ∧ t₁.head = t₁.head := And.intro ht₁ rfl
      exact (Finset.mem_filter.mpr this)

    -- t₂ ∈ s （t₂.head = t₁.head を使用）
    have ht₂s : t₂ ∈ s := by
      have : t₂ ∈ R ∧ t₂.head = t₁.head := And.intro ht₂ hhead.symm
      exact (Finset.mem_filter.mpr this)

    -- もし t₁ ≠ t₂ なら {t₁,t₂} ⊆ s なので 2 ≤ s.card になって矛盾
    by_contra hneq
    -- {t₁,t₂} を `insert t₂ {t₁}` で表す
    have hsubset : insert t₂ ({t₁} : Finset (Rule α)) ⊆ s := by
      intro x hx
      -- x = t₂ ∨ x = t₁
      have hx' := (Finset.mem_insert.mp hx)
      cases hx' with
      | inl hx2 =>
          -- x = t₂
          cases hx2
          exact ht₂s
      | inr hx1 =>
          -- x ∈ {t₁} → x = t₁
          have : x = t₁ := (Finset.mem_singleton.mp hx1)
          cases this
          exact ht₁s

    have hcard_pair : (insert t₂ ({t₁} : Finset (Rule α))).card = 2 := by
      -- card_insert (if a∉s) : (insert a s).card = s.card + 1
      -- ここで s = {t₁} だから 1 + 1 = 2
      have : ({t₁} : Finset (Rule α)).card = 1 := by
        -- 単集合の濃度
        -- again, simp で十分
        simp
      -- まとめて
      -- simp [Finset.card_insert, hnot] は
      --   card (insert t₂ {t₁}) = card {t₁} + 1 = 1 + 1 = 2
      -- を出してくれる
      --simp_all only [mem_filter, and_self, ne_eq, card_singleton, s]
      have h_card_insert : (insert t₂ ({t₁} : Finset (Rule α))).card = ({t₁}:Finset (Rule α)).card + 1 := by
        simp
        exact card_pair fun a => hneq (id (Eq.symm a))
      exact h_card_insert

    -- 部分集合なら濃度は増えない： card {t₁,t₂} ≤ card s
    have two_le_card_s : 2 ≤ s.card := by

      have := Finset.card_le_card (s := insert t₂ ({t₁} : Finset (Rule α)))
         (t := s) hsubset
      simp_all only [mem_filter, and_self, ne_eq, s]

    -- {t₁,t₂} の濃度は 2（t₂ ∉ {t₁} を使って card_insert）
    have hnot : t₂ ∉ ({t₁} : Finset (Rule α)) := by
      -- t₂ ∈ {t₁} ↔ t₂ = t₁
      have : t₂ = t₁ := by
        -- 反証用に仮定すると hneq と矛盾
        have h_s_card_le : s.card ≤ 1 := by
          simp_all only [mem_filter, and_self, ne_eq, s]
        have h_card_pair : #{t₁, t₂} = 2 := by
          simp [hneq]
        have h_s_card_ge : 2 ≤ s.card := by
          simp_all only [mem_filter, and_self, ne_eq, mem_singleton, not_false_eq_true, card_insert_of_notMem, card_singleton,
             Nat.reduceAdd, s]
        linarith

      all_goals
        -- 目的は t₂ ∉ {t₁}
        -- 直接書く：
        -- simp [Finset.mem_singleton, hneq] で済みますが、simpa を避けるなら unfold 的に
        exact by
          -- `simp` で十分（`simpa` は使っていない）
          simp [Finset.mem_singleton]
          exact fun a => hneq (id (Eq.symm this))

    -- 一方、仮定 h から s.card ≤ 1
    have one_ge_card_s : s.card ≤ 1 := by
      -- h を a := t₁.head に適用し，{t∈R | t.head = a} を filter に変換
      have := h (t₁.head)
      -- {t ∈ R | t.head = t₁.head} = R.filter …
      -- `change` で左辺を揃える
      change (R.filter (fun t => t.head = t₁.head)).card ≤ 1 at this
      -- s の定義に一致
      -- s = R.filter …
      -- 置換して終了
      -- `rfl` で一致
      -- （s の定義が `let s := …` なので `rfl`）
      exact (by
        have : s = R.filter (fun t => t.head = t₁.head) := rfl
        simp_all only [mem_filter, and_self, ne_eq, mem_singleton, not_false_eq_true, card_insert_of_notMem, card_singleton,
    Nat.reduceAdd, s])

    -- 2 ≤ s.card ≤ 1 の矛盾
    linarith
    --exact (Nat.le_trans two_le_card_s one_ge_card_s).false
