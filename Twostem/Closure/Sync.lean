import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.Closure.Step

namespace Twostem
open Closure

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]

/- Your existing `nextHead?`, `step2`, `syncClIter`, `syncCl` go here.
    Keep only what is necessary to prove equivalence with `Step.cl`. -/

def nextHead? (R : Finset (Rule α)) (I : Finset α) : Option α :=
  let heads := (applicable R I).image (fun t => t.head)
  if h : heads.Nonempty then
    some (heads.min' h)
  else
    none

omit [Fintype α] in
lemma nextHead?_spec_none
  {R : Finset (Rule α)} {I : Finset α}
  (h : nextHead? R I = none) :
  applicable R I = ∅ := by
  classical
  unfold nextHead? at h
  simp_all only [Finset.image_nonempty, dite_eq_right_iff, reduceCtorEq, imp_false, Finset.not_nonempty_iff_eq_empty]

omit [Fintype α] in
lemma nextHead?_spec_some
  {R : Finset (Rule α)} {I : Finset α} {a : α}
  (h : nextHead? R I = some a) :
  a ∉ I ∧ ∃ t ∈ R, t.prem ⊆ I ∧ t.head = a := by
  classical
  unfold nextHead? at h
  simp_all only [Finset.image_nonempty]
  simp at h
  rcases h with ⟨h_nonempty, hmin⟩
  --dsimp [applicable] at hmin h_nonempty
  -- h_nonempty は heads.Nonempty から ∃ t ∈ applicable, true
  let heads := (applicable R I).image (fun t => t.head)
  let aa := heads.min' ?_
  have ha_in_heads : aa ∈ heads := by
    refine Finset.min'_mem heads (Finset.image_nonempty.mpr h_nonempty)
  obtain ⟨t, ht_app, h_eq⟩ := Finset.mem_image.mp ha_in_heads
  --simp [mem_applicable] at ht_app
  -- a = min' heads h_nonempty
  have ha_le_t : aa ≤ t.head := by
    subst hmin
    apply Finset.min'_le
    simp_all only [applicable, Finset.mem_image, Finset.mem_filter, heads, aa]
  have : t.head ≤ aa := by
    --apply Finset.min'_le
    subst hmin
    simp_all only
  have : t.head = aa := le_antisymm this ha_le_t
  subst hmin
  simp_all only [applicable, Finset.mem_image, Finset.mem_filter, le_refl, not_false_eq_true, true_and, heads, aa]
  obtain ⟨w, h⟩ := ha_in_heads
  obtain ⟨left, right⟩ := ht_app
  obtain ⟨left_1, right_1⟩ := h
  obtain ⟨left_2, right⟩ := right
  obtain ⟨left_1, right_2⟩ := left_1
  obtain ⟨left_3, right_2⟩ := right_2
  simp_all only [not_false_eq_true]
  apply Exists.intro
  · apply And.intro
    · apply left_1
    · simp_all only [and_self]

def step2 (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  match nextHead? R I with
  | none   => I
  | some a => insert a I

def syncClIter (R : Finset (Rule α)) (I : Finset α) : Nat → Finset α
  | 0       => I
  | k + 1   =>
    let J := syncClIter R I k
    match nextHead? R J with
    | none   => J
    | some a => insert a J

def syncCl  [Fintype α] [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  parIter R I (Fintype.card α)

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma syncCl_extensive [Fintype α] [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ syncCl R I := by
  unfold syncCl
  exact parIter_increasing R I 0 (Fintype.card α) (Nat.zero_le _)

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma syncCl_monotone [Fintype α] [DecidableEq α] (R : Finset (Rule α)) :
  Monotone (syncCl R) := by
  intro I J hIJ
  unfold syncCl
  simp_all only [Finset.le_eq_subset]
  apply parIter_mono
  simp_all only [Finset.le_eq_subset]

omit [Fintype α] [LinearOrder α] in
-- fires が非空なら strict に増える： S ⊂ stepPar R S
lemma ssubset_stepPar_of_fires_nonempty
  {R : Finset (Rule α)} {S : Finset α}
  (hne : (fires R S).Nonempty) :
  S ⊂ stepPar R S := by
  refine ⟨?subset, ?ne⟩
  · intro x hx; exact Finset.mem_union.mpr (Or.inl hx)
  · rcases hne with ⟨a, ha⟩
    have ha_in_step : a ∈ stepPar R S := by
      exact Finset.mem_union.mpr (Or.inr ha)
    rcases Finset.mem_image.mp ha with ⟨t, htApp, hEq⟩
    -- t ∈ applicable R S なら head ∉ S
    have hsplit := Finset.mem_filter.mp htApp
    have hhead_not : t.head ∉ S := by exact hsplit.2.2
    have a_not_in_S : a ∉ S := by
      intro haS
      have : t.head ∈ S := by
        -- a = t.head なので書き換え
        have : a = t.head := by exact id (Eq.symm hEq)
        have : t.head = a := this.symm
        -- 置換してから使う
        have haS' : a ∈ S := haS
        subst this
        simp_all only [not_true_eq_false]
      exact hhead_not this

    intro hEqSet
    -- a は step 側に入るが S には入らない ⇒ 等しくない
    have : a ∈ S := by
      -- hEqSet : stepPar R S = S
      -- a ∈ stepPar R S なので a ∈ S に落ちる
      have : a ∈ stepPar R S := ha_in_step
      exact hEqSet ha_in_step
    exact a_not_in_S this

lemma mem_fires_not_mem_base {α} [DecidableEq α]
  {R : Finset (Rule α)} {S : Finset α} {a : α} :
  a ∈ fires R S → a ∉ S := by
  intro ha
  rcases Finset.mem_image.mp ha with ⟨t, htApp, hEq⟩
  -- htApp : t ∈ applicable R S = R.filter (fun t => t.prem ⊆ S ∧ t.head ∉ S)
  have hsplit := Finset.mem_filter.mp htApp
  have hnot : t.head ∉ S := hsplit.2.2
  -- a = t.head なので置換
  intro haS
  have : t.head ∈ S := by
    have tmp := haS
    -- hEq : t.head = a
    -- a∈S を t.head∈S に書き換える
    -- まず a = t.head を作る
    have hEq' : a = t.head := Eq.symm hEq
    -- 書き換え
    -- `rw [hEq']` は `haS : a ∈ S` に使う
    have tmp' : t.head ∈ S := by
      -- 置換して得る
      -- (Lean の補助として一旦 `have` を作って `rw` する)
      have htmp := haS
      rw [hEq'] at htmp
      exact htmp
    exact tmp'
  exact hnot this

-- 重要： stepPar R S = S  ↔  fires R S = ∅
lemma step_eq_iff_fires_empty {α} [DecidableEq α]
  {R : Finset (Rule α)} {S : Finset α} :
  stepPar R S = S ↔ fires R S = ∅ := by
  constructor
  · intro hEq
    -- fires = ∅ を示す：要素があれば矛盾
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have : a ∈ S := by
      -- a ∈ step の右側 ⇒ 等式で S に落ちる
      have hstep : a ∈ stepPar R S := Finset.mem_union.mpr (Or.inr ha)
      -- 書き換え
      have htmp := hstep
      rw [hEq] at htmp
      exact htmp
    have : a ∉ S := mem_fires_not_mem_base (R:=R) (S:=S) (a:=a) ha
    exact this ‹a ∈ S›
  · intro hEmpty
    -- fires = ∅ なら S ∪ ∅ = S
    unfold stepPar
    rw [hEmpty, Finset.union_empty]

lemma fires_nonempty_of_parIter_ne_succ {α} [DecidableEq α] [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  let S := parIter R I (Fintype.card α)
  ¬ parIter R I (Fintype.card α) = parIter R I (Fintype.card α + 1) →
  (fires R S).Nonempty := by
  intro S hneq
  -- parIter (n+1) = stepPar R (parIter n)
  -- 等式になってしまうと hneq と矛盾するので、fires は空でない
  by_contra hnone
  -- hnone : ¬ Nonempty → = ∅
  have hEmpty : fires R S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha; exact hnone ⟨a, ha⟩
  -- step = S
  have hStepEq : stepPar R S = S := (step_eq_iff_fires_empty (R:=R) (S:=S)).mpr hEmpty
  -- parIter (n+1) = stepPar R (parIter n) = S
  have hEq : parIter R I (Fintype.card α + 1) = parIter R I (Fintype.card α) := by
    -- まず parIter の定義
    have hDef : parIter R I (Fintype.card α + 1) = stepPar R (parIter R I (Fintype.card α)) := rfl
    -- S = parIter … n の定義で書き換え
    have hS : S = parIter R I (Fintype.card α) := rfl
    -- 連鎖
    -- parIter (n+1) = stepPar R (parIter n) = stepPar R S = S = parIter n
    -- 一歩ずつ：
    -- 書き換え1：parIter (n+1) = stepPar R (parIter n)
    -- 書き換え2：parIter n を S に（hS の対称を使う）
    -- 書き換え3：stepPar R S = S（hStepEq）
    -- 書き換え4：S = parIter n（hS）
    -- まとめて：
    have h1 : parIter R I (Fintype.card α + 1)
              = stepPar R (parIter R I (Fintype.card α)) := hDef
    -- parIter n を S に置換
    have h2 : stepPar R (parIter R I (Fintype.card α)) = stepPar R S := by
      rw [← hS]
    -- stepPar R S = S
    have h3 : stepPar R S = S := hStepEq
    -- S = parIter n
    have h4 : S = parIter R I (Fintype.card α) := hS
    -- 合成
    -- parIter (n+1) = stepPar R S = S = parIter n
    -- transitivity を段階的に
    have h12 : parIter R I (Fintype.card α + 1) = stepPar R S := by
      rw [h1, h2]
    have h123 : parIter R I (Fintype.card α + 1) = S := by
      rw [h12, h3]
    have h1234 : parIter R I (Fintype.card α + 1) = parIter R I (Fintype.card α) := by
      rw [h123, h4]
    exact h1234
  exact hneq (Eq.symm hEq)

omit [Fintype α] [LinearOrder α] in
lemma parIter_fixed_from
  {R : Finset (Rule α)} {I : Finset α} {i : Nat}
  (hfix : parIter R I (i+1) = parIter R I i) :
  ∀ d, parIter R I (i + d) = parIter R I i := by
  intro d
  induction' d with d ih
  · -- d = 0
    have : i + 0 = i := Nat.add_zero _
    -- 書き換え
    exact rfl

  · -- d → d+1
    -- 目標を書き換え：parIter R I (i + (d+1)) = stepPar …
    change stepPar R (parIter R I (i + d)) = parIter R I i
    -- 帰納法で中身を固定点へ
    have ih' : parIter R I (i + d) = parIter R I i := ih
    rw [ih']
    -- `hfix` から step レベルの固定点を取り出す
    -- parIter R I (i+1) は定義で stepPar R (parIter R I i)
    have hdef : parIter R I (i+1) = stepPar R (parIter R I i) := rfl
    -- stepPar R (parIter R I i) = parIter R I i
    have hstep : stepPar R (parIter R I i) = parIter R I i := by
      -- hdef の左を使って hfix と合成
      have h1 : stepPar R (parIter R I i) = parIter R I (i+1) := by rfl
      -- stepPar … = parIter (i+1) = parIter i
      have h2 : stepPar R (parIter R I i) = parIter R I i := by
        -- trans で合成
        exact Eq.trans h1 hfix
      exact h2
    exact hstep

omit [Fintype α] [LinearOrder α] in
lemma exists_fix_le_card [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  ∃ i, i ≤ Fintype.card α ∧ parIter R I (i+1) = parIter R I i := by
  classical
  -- 反対仮定へ：全て非停止なら各段で fires 非空 → strict 増加が |α|+1 回 → card 矛盾
  by_contra h
  -- h : ¬ ∃ i ≤ |α|, parIter (i+1) = parIter i
  have hneq : ∀ i ≤ Fintype.card α, parIter R I (i+1) ≠ parIter R I i := by
    intro i hi
    intro hiEq
    exact h ⟨i, hi, hiEq⟩
  -- 各 i ≤ |α| で strict 増加
  have hstrict :
    ∀ i ≤ Fintype.card α,
      (parIter R I i) ⊂ (parIter R I (i+1)) := by
    intro i hi
    -- 非停止 ⇒ fires 非空 ⇒ strict
    have hNe' : parIter R I (i+1) ≠ parIter R I i := hneq i hi
    -- fires 非空であることを示す（空なら step = id で矛盾）
    have hne_fires : (fires R (parIter R I i)).Nonempty := by
      by_contra hempty
      -- fires = ∅
      have hf : fires R (parIter R I i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha; exact hempty ⟨a, ha⟩
      -- step = id なので直後で等しい
      have hstep : stepPar R (parIter R I i) = parIter R I i := by
        have hbi : stepPar R (parIter R I i) = parIter R I i :=
          (step_eq_iff_fires_empty (R:=R) (S:=parIter R I i)).mpr hf
        exact hbi
      -- parIter (i+1) = stepPar … = parIter i で矛盾
      have hEq : parIter R I (i+1) = parIter R I i := by
        -- parIter R I (i+1) は定義で stepPar …
        have hdef : parIter R I (i+1) = stepPar R (parIter R I i) := rfl
        have htrans : parIter R I (i+1) = parIter R I i := by
          rw [hdef]; exact hstep
        exact htrans
      exact hNe' hEq
    -- 非空なら strict：S ⊂ stepPar R S、かつ parIter (i+1) = stepPar R (parIter i)
    have hss : (parIter R I i) ⊂ (stepPar R (parIter R I i)) :=
      by
        -- 既出補題：fires 非空 → S ⊂ stepPar R S
        -- ここで直接書く
        refine ⟨?subset, ?ne⟩
        · intro x hx; exact Finset.mem_union.mpr (Or.inl hx)
        · rcases hne_fires with ⟨a, ha⟩
          have ha_in_step : a ∈ stepPar R (parIter R I i) :=
            Finset.mem_union.mpr (Or.inr ha)
          -- a は S には入らない
          have a_not_in_S : a ∉ parIter R I i :=
            mem_fires_not_mem_base (R:=R) (S:=parIter R I i) (a:=a) ha
          intro hEqSet
          have : a ∈ parIter R I i := by
            -- 等式で右辺を左辺へ
            have h' := ha_in_step
            exact hEqSet ha_in_step
          exact a_not_in_S this
    -- parIter (i+1) は定義で stepPar …
    have : (parIter R I i) ⊂ (parIter R I (i+1)) := by
      -- 書き換え
      -- parIter R I (i+1) = stepPar R (parIter R I i)
      have hdef : parIter R I (i+1) = stepPar R (parIter R I i) := rfl
      -- `hss` : S ⊂ stepPar R S を右辺に置換
      -- ssubset は置換で保たれる（`rw` で十分）
      -- まず hss をコピーしてから書き換え
      have htmp := hss
      -- hss の右辺 stepPar … を parIter … に置換
      -- 逆向きの等式が必要なので対称を使う
      have hdef' : stepPar R (parIter R I i) = parIter R I (i+1) := by rfl
      -- htmp : S ⊂ stepPar R S
      -- 右辺書き換え
      -- ここは「ssubset の右側を書き換える」ので、直接 `have` を作って返す
      -- 証明としては htmp をそのまま使ってよい（目的の形に等しい）
      -- Lean 的には `exact` で返せる
      exact by
        -- 右辺の名称だけ変えたいが、型は一致しているのでそのまま返す
        -- （parIter R I (i+1) は defeq で stepPar R (parIter R I i)）
        -- ここは `rfl` 展開を避けて、`exact` で通す
        -- 実は hdef' を使って `rewrite` してから `exact` でも可
        cases hdef'
        exact htmp
    exact this
  -- strict が (|α|+1) 回は不可能：card が |α| を超えるため矛盾へ
  -- 具体的に：0..|α| すべて strict なら card(parIter (|α|+1)) ≥ I.card + (|α|+1)
  -- しかし上限は |α|
  let n := Fintype.card α
  have hge : (parIter R I (n + 1)).card ≥ I.card + (n + 1) := by
    -- 逐次に加算していく帰納で示す
    -- 補助：strict ⟹ card 増加
    have hstep : ∀ i ≤ n,
      (parIter R I (i+1)).card ≥ (parIter R I i).card + 1 := by
      intro i hi
      have hss := hstrict i hi
      have hlt : (parIter R I i).card < (parIter R I (i+1)).card :=
        Finset.card_lt_card hss
      exact Nat.succ_le_of_lt hlt
    -- 累積（0..n の和）
    -- 帰納で card (k) ≥ I.card + k
    have : ∀ k ≤ n+1, (parIter R I k).card ≥ I.card + k := by
      intro k hk
      induction' k with k hk ih
      · -- k=0
        -- card(parIter 0)=I.card ≥ I.card+0
        have : (parIter R I 0).card = I.card := rfl
        -- 等号なので ≥ は自明
        have hge0 : (parIter R I 0).card ≥ I.card := by
          exact le_of_eq this
        -- +0 の書き換え
        have hadd : I.card + 0 = I.card := Nat.add_zero _
        have : (parIter R I 0).card ≥ I.card + 0 := by
          exact hge0
        exact this
      · -- k→k+1
        have hk_le_n : k ≤ n := Nat.le_of_lt_succ hk
        have hk_step := hstep k hk_le_n
        -- (parIter (k+1)).card ≥ (parIter k).card + 1 ≥ (I.card + k) + 1
        have htrans : (parIter R I (k+1)).card ≥ (I.card + k) + 1 := by

          --have h2 := Nat.add_le_add_right ih 1
          apply le_trans
          exact Nat.le_refl (I.card + k + 1)
          --rename_i inst inst_1 inst_2 inst_3 hk_1
          simp_all [n]
          apply le_trans
          on_goal 2 => apply hstep
          on_goal 2 => simp_all only
          simp_all only [add_le_add_iff_right]
          omega

        -- 結合則で I.card + (k+1) に整形
        have hadd : (I.card + k) + 1 = I.card + (k+1) := by
          exact Nat.add_assoc _ _ _
        have : (parIter R I (k+1)).card ≥ I.card + (k+1) := by
          exact htrans
        exact this
    -- 目的の k = n+1
    exact this (k:=n+1) (by exact Nat.le_refl _)
  -- 上限：card ≤ |α|
  have hle : (parIter R I (n + 1)).card ≤ Fintype.card α := by
    exact Finset.card_le_univ _
  -- したがって |α|+1 ≤ card ≤ |α| の矛盾
  have : Fintype.card α + 1 ≤ Fintype.card α := by
    -- I.card ≤ |α| を使って I.card + (n+1) ≥ (0) + (n+1) = |α|+1 でもよいが、
    -- 上で得た hge と hle を直接合成
    -- まず I.card ≤ |α|
    have hIle : I.card ≤ Fintype.card α := Finset.card_le_univ I
    -- I.card + (n+1) ≤ |α| + (n+1)
    have hadd_le : I.card + (n+1) ≤ Fintype.card α + (n+1) :=
      Nat.add_le_add_right hIle (n+1)
    -- (parIter (n+1)).card ≥ I.card + (n+1) ≥ |α| + 1
    have hlow : (parIter R I (n + 1)).card ≥ Fintype.card α + 1 := by
      exact Nat.le_of_add_left_le hge

       -- 低い方が高い方を超えることはない
    exact le_trans hlow hle
  exact Nat.not_succ_le_self _ this

omit [Fintype α] [LinearOrder α] in
-- |α| 段目で停止： parIter R I (|α|) = parIter R I (|α|+1)
lemma parIter_stabilizes_at_card [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  parIter R I (Fintype.card α) = parIter R I (Fintype.card α + 1) := by
  classical
  set n := Fintype.card α
  -- 0..n のどこかで停止
  obtain ⟨i, hi, hfix⟩ := exists_fix_le_card (R:=R) (I:=I)
  -- i 以降はずっと一定
  have hconst := parIter_fixed_from (R:=R) (I:=I) (i:=i) hfix
  -- n 段と n+1 段を i へ引き戻して等しいと示す
  have h1 : parIter R I n = parIter R I i := by
    -- i + (n - i) = n
    have hidx : i + (n - i) = n := Nat.add_sub_of_le hi
    have htmp := hconst (n - i)   -- parIter (i + (n-i)) = parIter i
    -- 左辺を書き換え
    have htmp' : parIter R I n = parIter R I i := by
      -- rewrite at htmp
      have htmp2 := htmp
      rw [hidx] at htmp2
      exact htmp2
    exact htmp'
  have h2 : parIter R I (n + 1) = parIter R I i := by
    -- i ≤ n ⇒ i ≤ n+1
    have hi' : i ≤ n + 1 := by exact Nat.le_add_right_of_le hi
    have hidx : i + (n + 1 - i) = n + 1 := Nat.add_sub_of_le hi'
    have htmp := hconst (n + 1 - i)
    have htmp' : parIter R I (n + 1) = parIter R I i := by
      have htmp2 := htmp
      rw [hidx] at htmp2
      exact htmp2
    exact htmp'
  -- 合成：parIter n = parIter i = parIter (n+1)
  have : parIter R I n = parIter R I (n + 1) := by
    -- trans で i を挟む
    -- parIter n = parIter i
    -- parIter i = parIter (n+1)
    have h2' : parIter R I i = parIter R I (n + 1) := Eq.symm h2
    exact Eq.trans h1 h2'
  -- 置換して終了
  -- n = |α| の定義で戻す
  exact this

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
-- 以上を使って「|α| 段目で飽和」
lemma parIter_saturates [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) (I : Finset α) :
  ∀ t ∈ R, t.prem ⊆ parIter R I (Fintype.card α) →
    t.head ∈ parIter R I (Fintype.card α) := by
  classical
  intro t htR hPrem
  set n := Fintype.card α
  have hfix : parIter R I n = parIter R I (n + 1) :=
    parIter_stabilizes_at_card R I
  -- もし head が入っていないなら「適用可能」になり、次段で追加されるはず。
  by_contra hnot
  have htApp : t ∈ applicable R (parIter R I n) := by
    simp [applicable, Finset.mem_filter, htR, hPrem, hnot]
  have : t.head ∈ parIter R I (n + 1) := by
    -- 次段で union の右側に入る
    have : t.head ∈ fires R (parIter R I n) := by
      exact Finset.mem_image.mpr ⟨t, htApp, rfl⟩
    have : t.head ∈ stepPar R (parIter R I n) :=
      Finset.mem_union.mpr (Or.inr this)
    simpa [parIter, stepPar] using this
  -- しかし n 段目で既に固定点なので、n+1 段目と等しい
  have : t.head ∈ parIter R I n := by simpa [hfix] using this
  exact hnot this

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma parIter_eventually_stops [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) (I : Finset α) :
  stepPar R (parIter R I (Fintype.card α)) = parIter R I (Fintype.card α) := by
  ext x
  constructor
  · intro hx
    unfold stepPar at hx
    cases Finset.mem_union.mp hx with
    | inl h => exact h
    | inr hxF =>
      -- x ∈ fires R (parIter R I (Fintype.card α))
      obtain ⟨t, ht_app, ht_head⟩ := Finset.mem_image.mp hxF
      rw [←ht_head]
      simp at ht_app
      have ⟨ht_in, ht_prem⟩ := ht_app
-- parIter_saturates を適用
      apply parIter_saturates R I t ht_in
      subst ht_head
      simp_all only [not_false_eq_true, and_self, fires, applicable, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        false_or]
  · intro hx
    unfold stepPar
    exact Finset.mem_union_left _ hx

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma syncCl_rule_fires [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) (I : Finset α) (r : Rule α)
  (hr : r ∈ R) (hprem : r.prem ⊆ syncCl R I) :
  r.head ∈ syncCl R I := by
  unfold syncCl at *
  -- 背理法
  by_contra hn
  -- r.prem ⊆ parIter R I (card α) かつ r.head ∉ parIter R I (card α)
  -- なら r ∈ applicable
  have : r ∈ applicable R (parIter R I (Fintype.card α)) := by
    simp [applicable, Finset.mem_filter]
    exact ⟨hr, hprem, hn⟩
  -- したがって r.head ∈ fires
  have : r.head ∈ fires R (parIter R I (Fintype.card α)) := by
    simp [fires]
    simp_all only [applicable, Finset.mem_filter, not_false_eq_true, and_self]
    use r

  -- よって r.head ∈ stepPar R (parIter R I (card α))
  have : r.head ∈ stepPar R (parIter R I (Fintype.card α)) := by
    simp [stepPar]
    simp_all only [applicable, Finset.mem_filter, not_false_eq_true, and_self, fires, Finset.mem_image, or_true]

  rw [parIter_eventually_stops] at this
  exact hn this

omit [Fintype α] [LinearOrder α] in
lemma subset_parIter (R : Finset (Rule α)) (I : Finset α) :
  ∀ k, I ⊆ parIter R I k := by
  intro k
  induction' k with k ih
  · -- k=0
    intro x hx; exact hx  -- parIter R I 0 = I
  · -- k→k+1
    intro x hx
    have hx' : x ∈ parIter R I k := ih hx
    -- stepPar は左側に I を含む
    have : x ∈ stepPar R (parIter R I k) := by
      exact Finset.mem_union.mpr (Or.inl hx')
    -- parIter R I (k+1) の定義
    change x ∈ stepPar R (parIter R I k) at this
    exact this

omit [Fintype α][LinearOrder α] in
lemma syncCl_infl [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ syncCl (R:=R) I := by
  -- syncCl = parIter … (|α|)
  intro x hx
  have hsub := subset_parIter (R:=R) (I:=I) (Fintype.card α)
  exact hsub hx

omit [Fintype α] [LinearOrder α] in
lemma syncCl_closed [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  IsClosed R (syncCl (R:=R) I) := by
  intro t htR hPrem
  -- ゴール書換：syncCl = parIter … (|α|)
  change t.head ∈ parIter R I (Fintype.card α)
  -- parIter_saturates : prem ⊆ parIter … (|α|) → head ∈ parIter … (|α|)
  have hsat :=
    parIter_saturates (R:=R) (I:=I)
  have : t.head ∈ parIter R I (Fintype.card α) := hsat t htR hPrem
  exact this

omit [Fintype α] [LinearOrder α] in
lemma syncCl_min [Fintype α]
  (R : Finset (Rule α)) {I J : Finset α}
  (hIJ : I ⊆ J) (hJclosed : IsClosed R J) :
  syncCl (R:=R) I ⊆ J := by
  -- まず「各段で J を保つ」補題を示し、それを |α| に適用
  have step_into_J :
    ∀ k, parIter R I k ⊆ J := by
    intro k
    induction' k with k ih
    · -- 0 段：I ⊆ J
      intro x hx; exact hIJ hx
    · -- k+1 段
      intro x hx
      -- x ∈ stepPar R (parIter R I k) = parIter R I k ∪ fires R (parIter R I k)
      rcases Finset.mem_union.mp hx with hx_in | hx_fire
      · -- 左側は帰納法より J
        exact ih hx_in
      · -- 右側：fires の元なら、ある t で prem ⊆ parIter R I k, head=x
        rcases Finset.mem_image.mp hx_fire with ⟨t, htApp, hEq⟩
        -- applicable の分解
        have hsplit := Finset.mem_filter.mp htApp
        have hPrem : t.prem ⊆ parIter R I k := hsplit.2.1
        -- prem ⊆ parIter … k ⊆ J
        have hPremJ : t.prem ⊆ J := fun a ha => ih (hPrem ha)
        -- J が閉なので head ∈ J
        have hHeadJ : t.head ∈ J := hJclosed (by exact hsplit.1) hPremJ
        -- head = x で置換
        have hEq' : t.head = x := hEq
        have hxJ : x ∈ J := by
          have tmp := hHeadJ
          rw [hEq'] at tmp
          exact tmp
        exact hxJ
  -- 目的へ
  intro x hx
  -- syncCl = parIter … (|α|)
  change x ∈ parIter R I (Fintype.card α) at hx
  have hxJ := step_into_J (Fintype.card α) hx
  exact hxJ

omit [Fintype α][LinearOrder α] in
lemma syncCl_idem [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  syncCl (R:=R) (syncCl (R:=R) I) = syncCl (R:=R) I := by
  -- 片側：最小性（閉＆自明包含）
  have hclosed : IsClosed R (syncCl (R:=R) I) := syncCl_closed (R:=R) (I:=I)
  have hmin :
    syncCl (R:=R) (syncCl (R:=R) I) ⊆ syncCl (R:=R) I :=
    syncCl_min (R:=R) (I:=syncCl (R:=R) I) (J:=syncCl (R:=R) I)
      (by intro x hx; exact hx)  -- subset_refl
      hclosed
  -- 逆側：inflationary
  have hinfl :
    syncCl (R:=R) I ⊆ syncCl (R:=R) (syncCl (R:=R) I) :=
    syncCl_infl (R:=R) (I:=syncCl (R:=R) I)
  -- 反包含で等号
  apply le_antisymm hmin hinfl

omit [Fintype α] [LinearOrder α] in
lemma syncCl_mono [Fintype α]
  (R : Finset (Rule α)) :
  Monotone (syncCl (R:=R)) := by
  intro I J hIJ
  -- syncCl = parIter … (|α|)
  -- parIter_mono（k 固定）を使う
  have h := parIter_mono (R:=R) (k:=Fintype.card α) hIJ
  -- 目標と同型なのでそのまま
  exact h

/-- **閉包が等しいときの“最小一致段直前の 1 点化”**：
`syncCl R' U = syncCl R' V` なら，最小の `k` で `parIter R' U k = parIter R' V k` が成り立つ。
`k = 0` なら `U = V`。`k > 0` なら `k-1` 段の差集合はちょうど 1 点。 -/
lemma exists_singleton_lastDiff_of_syncEq
  {α : Type*} [DecidableEq α] [Fintype α]   -- ★ ここを必ず入れる
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α}
  (hSync : syncCl (R := R') (I := U) = syncCl (R := R') (I := V)) :  -- ★ 名前付きで
  U = V ∨ ∃ (k : ℕ) (f : α),
    k + 1 ≤ Fintype.card α ∧
    (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k) = {f} := by
  classical

  -- 記号
  set N := Fintype.card α
  -- `P m := parIter R' U m = parIter R' V m`
  let P : Nat → Prop := fun m => parIter R' U m = parIter R' V m
  -- N 段では一致（syncCl の定義）
  have hPN : P N := by
    -- syncCl = parIter … N
    -- hSync : parIter R' U N = parIter R' V N
    exact hSync
  -- 「一致する m の集合」は非空
  have hNonempty : ∃ m, P m := ⟨N, hPN⟩
  -- その最小を取る
  classical
  let k₀ := Nat.find hNonempty
  have hk0P : P k₀ := Nat.find_spec hNonempty
  -- もし k₀ = 0 なら U=V で終了
  by_cases hk0_zero : k₀ = 0
  · left
    -- parIter R' U 0 = U, parIter R' V 0 = V
    -- hk0P : parIter R' U k₀ = parIter R' V k₀
    -- 書き換え
    have : parIter R' U 0 = parIter R' V 0 := by
      have hk0P' : parIter R' U k₀ = parIter R' V k₀ := by
        have h := hk0P
        dsimp [P] at h          -- P を定義展開
        exact h

    -- 次に k₀ = 0 を右辺に反映してゴールへ
      have hk0P0 : parIter R' U 0 = parIter R' V 0 := by
        have h := hk0P'         -- h : parIter R' U k₀ = parIter R' V k₀
        rw [hk0_zero] at h      -- k₀ を 0 に書き換え
        exact h

    -- これがまさにゴール
      exact hk0P0


    -- それぞれ 0 段は初期集合
    -- よって U=V
    -- 直接 `rfl` 書換
    exact this
  · -- k₀ > 0 の場合：`k := k₀ - 1` に `lastDiff_is_singleton` を適用
    right
    have hk0_pos : 0 < k₀ := Nat.pos_of_ne_zero hk0_zero
    -- k := k₀ - 1
    set k := k₀ - 1
    have hk_succ : k + 1 = k₀ := Nat.succ_pred_eq_of_pos hk0_pos
    -- `k` 段で差が非空（さもなくば k₀ が最小に反する）
    have hNe : ((parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)).Nonempty := by
      -- もし空なら parIter … k = parIter … k で、k < k₀ に一致があることになり、最小性に反する
      by_contra hEmpty
      -- union 空 → 両 sdiff が空
      have hXYempty : parIter R' U k \ parIter R' V k = ∅ := by
        -- `empty_union` を使っても良いが、ここでは素朴に
        apply Finset.subset_empty.mp
        intro x hx
        have : x ∈ ((parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)) :=
          Finset.mem_union.mpr (Or.inl hx)

          -- `hEmpty : union.Nonempty` の否定なので、成員がいれば矛盾
          -- `Nonempty` の否定は `∀ x, x ∉ …` と同等。ここは単純に使うのが面倒なので別ルート：
          -- `by_cases` で空集合だと置いてもOKだが、簡単には次を使う：

        have : False := by
          have : x ∈ (∅ : Finset α) := by
            simp
            apply (Finset.notMem_empty x)
            have hx' : x ∈ (parIter R' U k \ parIter R' V k) := by
              exact hx
            have :parIter R' U k \ parIter R' V k ∪ parIter R' V k \ parIter R' U k = ∅ := by
              exact Finset.not_nonempty_iff_eq_empty.mp hEmpty
            have :parIter R' U k \ parIter R' V k = ∅ := by
              simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero,
                not_false_eq_true, implies_true, Nat.le_find_iff, Nat.lt_one_iff,
                Nat.sub_add_cancel, Finset.not_nonempty_iff_eq_empty,
                Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, Finset.union_eq_empty, P, N, k₀,
                k]
            rw [this] at hx'
            exact hx'

          exact (Finset.notMem_empty x) this
        exact this.elim
      -- 同様にもう片側も空
      have hYXempty : parIter R' V k \ parIter R' U k = ∅ := by
        apply Finset.subset_empty.mp
        intro x hx
        have : x ∈ ((parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)) :=
          Finset.mem_union.mpr (Or.inr hx)
        simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero,
                not_false_eq_true, implies_true, Nat.le_find_iff, Nat.lt_one_iff,
                Nat.sub_add_cancel, Finset.not_nonempty_iff_eq_empty,
                Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, Finset.union_eq_empty, P, N, k₀,
                k]
        set X := parIter R' U (Nat.find hNonempty - 1)
        set Y := parIter R' V (Nat.find hNonempty - 1)

        -- 与件の整形
        -- hEmpty : True ∧ Y ⊆ X
        have hYX : Y ⊆ X := hEmpty.right
        -- hXYempty : X ⊆ Y
        have hXY : X ⊆ Y := hXYempty

        -- 包含の両向きから X = Y
        have hEqXY : X = Y := le_antisymm hXY hYX

        -- すると差集合は空になる：Y\X = ∅
        have hYdiffEmpty : Y \ X = (∅ : Finset α) := by
          -- Y\X を Y\Y に書き換えてから `sdiff_self`
          -- `sdiff_self : s \ s = ∅`
          -- まず書き換え
          have : Y \ X = Y \ Y := by simp [hEqXY]
          -- その上で ∅ に落とす
          -- `sdiff_self` は `by exact Finset.sdiff_self Y`
          -- ただし等式の左辺を揃えて使いたいので、まとめて `calc` で書く：
          calc
            Y \ X = Y \ Y := by simp [hEqXY]
            _     = (∅ : Finset α) := Finset.sdiff_self Y

        -- 与件 hx : x ∈ Y ∧ x ∉ X から、x ∈ Y\X を作る
        have hxDiff : x ∈ Y \ X := by
          -- `mem_sdiff.mpr` で (∈, ∉) のペアから差集合会員へ
          exact Finset.mem_sdiff.mpr hx

        -- これを hYdiffEmpty で空集合の会員に書き換える
        have hxEmpty : x ∈ (∅ : Finset α) := by
          -- hxDiff : x ∈ Y\X，hYdiffEmpty : Y\X = ∅
          -- 書き換えて終了
          --   rw [hYdiffEmpty] at hxDiff
          --   exact hxDiff
          -- term でそのまま返すなら：
          have hx' : x ∈ Y \ X := hxDiff
          -- 書き換え
          have : x ∈ (∅ : Finset α) := by
            -- tactic 的に：
            -- rw [hYdiffEmpty] at hx'
            -- exact hx'
            -- term で済ませたいなら下の簡潔版参照
            exact by
              -- ここはエディタなら `rw [hYdiffEmpty] at hx'` で一行です
              -- チャットでは最終行だけ提示します
              simp_all only [Finset.mem_union, Finset.mem_sdiff, not_true_eq_false, and_self,
                sdiff_self, Finset.bot_eq_empty, Finset.notMem_empty, Y, P, X]
          exact this

        -- 目的が `⊢ x ∈ ∅` なら
        exact hxEmpty





      -- sdiff が両方空 ⇒ parIter … k が等しい
      have hEqk : parIter R' U k = parIter R' V k := by
        -- `sdiff_eq_empty` から `⊆`、相互に示して `le_antisymm`
        apply le_antisymm
        · -- ⊆
          intro x hx
          by_contra hxV
          -- x ∈ X \ Y となり、sdiff が空に矛盾
          have : x ∈ parIter R' U k \ parIter R' V k := by
            exact Finset.mem_sdiff.mpr ⟨hx, hxV⟩
          have : False := by
            -- hXYempty = ∅
            have : x ∈ (∅ : Finset α) := by
              simp
              apply (Finset.notMem_empty x)
              have hx' : x ∈ parIter R' U k \ parIter R' V k := this
              rw [hXYempty] at hx'
              exact hx'
            exact (Finset.notMem_empty x) this
          exact this.elim
        · -- 逆 ⊆
          intro x hx
          by_contra hxU
          have : x ∈ parIter R' V k \ parIter R' U k := by
            exact Finset.mem_sdiff.mpr ⟨hx, hxU⟩
          have : False := by
            have : x ∈ (∅ : Finset α) := by
              simp
              apply (Finset.notMem_empty x)
              have hx' : x ∈ parIter R' V k \ parIter R' U k := this
              rw [hYXempty] at hx'
              exact hx'
            exact (Finset.notMem_empty x) this
          exact this.elim

      -- すると P k = true。最小性 `Nat.find_min'` に反する（k < k₀）
      have hk_lt_k0 : k < k₀ := Nat.pred_lt (by exact hk0_pos.ne')
      have : P k := hEqk
      -- `Nat.find_min' : P (Nat.find h) ∧ ∀ m < Nat.find h, ¬ P m`
      -- を使いたいが、`Nat.find_min'` は Mathlib にあるヘルパ。
      -- ここでは `Nat.find_spec` の最小性版 `Nat.find_min'` を使う：
      show False
      have hk0_le_k : k₀ ≤ k := Nat.find_min' hNonempty this

      -- k₀ ≤ k と k < k₀ を合成すると k₀ < k₀ の矛盾が出る
      have hk0_lt_self : k₀ < k₀ := Nat.lt_of_le_of_lt hk0_le_k hk_lt_k0

      -- k₀ < k₀ は不可能
      exact (Nat.lt_irrefl _ ) hk0_lt_self

      --refine Nat.find_min' hNonempty ?_ pos.ne' hk_lt_k0 this

    -- `k+1 = k₀` 段で一致
    have hEq_next : parIter R' U (k+1) = parIter R' V (k+1) := by
      -- hk0P : P k₀
      -- 書き換え
      simpa [hk_succ] using hk0P
    -- ここで lastDiff を適用
    have hSingleton := lastDiff_is_singleton (R':=R') hNTF hNS (U:=U) (V:=V) (k:=k) hNe hEq_next
    -- ∃! f, f ∈ Δ_k から、集合として {f} と等しいことを作る
    rcases hSingleton with ⟨f, hf_mem, huniq⟩
    -- S := Δ_k
    set SΔ := (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)
    have hSΔ_eq_singleton : SΔ = {f} := by
      -- ⊆：任意の x∈SΔ は一意性より x=f
      apply le_antisymm_iff.mpr
      constructor
      · intro x hx
        -- huniq : ∀ g, g ∈ SΔ → g = f
        have : x = f := huniq x hx
        -- したがって x∈{f}
        have : x ∈ ({f} : Finset α) := by exact Finset.mem_singleton.mpr (huniq x hx)
        exact this
      · -- ⊇：f ∈ SΔ は hf_mem から
        intro x hx
        -- x ∈ {f} → x=f → x∈SΔ
        have : x = f := by exact Finset.mem_singleton.mp hx
        simpa [this, SΔ] using hf_mem
    -- 仕上げ
    refine ⟨k, f, ?bound, ?eq⟩
    · -- k+1 ≤ N（最小一致段 k₀ ≤ N より）
      have hk0_le_N : k₀ ≤ N := by
        -- `Nat.find` の最小値は N 以下（N が witness）
        -- `Nat.find_spec` と `Nat.find_min'` から
        -- 簡単には `Nat.find_min'` に `m=N` を入れると `k₀ ≤ N`
        apply Nat.find_min' hNonempty
        exact hSync
        -- ↑ 多少ラフなので、環境によっては次で十分：
        -- have : P N := hPN; exact Nat.find_min' hNonempty ?(0<N)
      -- k+1 = k₀
      have : k + 1 = k₀ := hk_succ
      -- したがって k+1 ≤ N
      exact le_trans (by exact Nat.le_of_eq hk_succ) hk0_le_N
    · -- 差集合 = {f}
      -- いまの `SΔ` がまさに差集合
      exact hSΔ_eq_singleton

lemma cause_exists_on_left_of_step_eq
  {R : Finset (Rule α)} {X Y : Finset α}
  (hstep : stepPar R X = stepPar R Y)
  {g : α} (hg : g ∈ Y \ X) :
  ∃ r, r ∈ R ∧ r.prem ⊆ X ∧ r.head = g := by
  classical
  have hgY  : g ∈ Y := (Finset.mem_sdiff.mp hg).1
  have hgNX : g ∉ X := (Finset.mem_sdiff.mp hg).2
  have : g ∈ stepPar R Y := Finset.mem_union.mpr (Or.inl hgY)
  have : g ∈ stepPar R X := by
    have hsym : stepPar R Y = stepPar R X := hstep.symm
    simpa [hsym] using this
  -- g ∈ X ∪ fires R X だが g ∉ X なので g ∈ fires R X
  have hg_in_firesX : g ∈ fires R X := by
    rcases Finset.mem_union.mp this with hX | hFX
    · exact (hgNX hX).elim
    · exact hFX
  rcases Finset.mem_image.mp hg_in_firesX with ⟨r, hrApp, hrHead⟩
  have hrR  : r ∈ R := (Finset.mem_filter.mp hrApp).1
  have hrPr : r.prem ⊆ X := (Finset.mem_filter.mp hrApp).2.1
  exact ⟨r, hrR, hrPr, hrHead⟩

lemma cause_exists_on_right_of_step_eq
  {R : Finset (Rule α)} {X Y : Finset α}
  (hstep : stepPar R X = stepPar R Y)
  {f : α} (hf : f ∈ X \ Y) :
  ∃ r, r ∈ R ∧ r.prem ⊆ Y ∧ r.head = f := by
  classical
  have hfX  : f ∈ X := (Finset.mem_sdiff.mp hf).1
  have hfNY : f ∉ Y := (Finset.mem_sdiff.mp hf).2
  have : f ∈ stepPar R X := Finset.mem_union.mpr (Or.inl hfX)
  have : f ∈ stepPar R Y := by simpa [hstep] using this
  have hf_in_firesY : f ∈ fires R Y := by
    rcases Finset.mem_union.mp this with hY | hFY
    · exact (hfNY hY).elim
    · exact hFY
  rcases Finset.mem_image.mp hf_in_firesY with ⟨r, hrApp, hrHead⟩
  have hrR  : r ∈ R := (Finset.mem_filter.mp hrApp).1
  have hrPr : r.prem ⊆ Y := (Finset.mem_filter.mp hrApp).2.1
  exact ⟨r, hrR, hrPr, hrHead⟩

end Twostem
