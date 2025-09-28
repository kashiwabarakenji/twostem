import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Twostem.Rules
import LeanCopilot

namespace Twostem

open scoped BigOperators

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-!
同期的閉包：
* applicable R I  : 今の I で適用可能な規則（prem ⊆ I ∧ head ∉ I）
* nextHead? R I   : その head の最小元（Option）
* step R I        : one-step 拡張
* syncClIter / syncCl : 反復手続き（上限 |α|）
-/

/-- I に対して今適用可能な規則（prem ⊆ I かつ head ∉ I） -/
def applicable (R : Finset (Rule α)) (I : Finset α) : Finset (Rule α) :=
  R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I)

--omit [Fintype α] [LinearOrder α] in
lemma mem_applicable {R : Finset (Rule α)} {I : Finset α} {t : Rule α} :
  t ∈ applicable R I ↔ t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I := by
  classical
  unfold applicable
  simp [Finset.mem_filter, and_left_comm]

/-- 適用可能な規則の head のうち最小のもの（Option） -/
def nextHead? (R : Finset (Rule α)) (I : Finset α) : Option α :=
  let heads := (applicable R I).image (fun t => t.head)
  if h : heads.Nonempty then
    some (heads.min' h)
  else
    none

lemma nextHead?_spec_none
  {R : Finset (Rule α)} {I : Finset α}
  (h : nextHead? R I = none) :
  applicable R I = ∅ := by
  classical
  unfold nextHead? at h
  simp_all only [Finset.image_nonempty, dite_eq_right_iff, reduceCtorEq, imp_false, Finset.not_nonempty_iff_eq_empty]

lemma nextHead?_spec_some
  {R : Finset (Rule α)} {I : Finset α} {a : α}
  (h : nextHead? R I = some a) :
  a ∉ I ∧ ∃ t ∈ R, t.prem ⊆ I ∧ t.head = a := by
  classical
  unfold nextHead? at h
  simp_all only [Finset.image_nonempty]
  simp at h
  rcases h with ⟨h_nonempty, hmin⟩
  dsimp [applicable] at hmin h_nonempty
  -- h_nonempty は heads.Nonempty から ∃ t ∈ applicable, true
  let heads := (applicable R I).image (fun t => t.head)
  let aa := heads.min' ?_
  have ha_in_heads : aa ∈ heads := by
    refine Finset.min'_mem heads (Finset.image_nonempty.mpr h_nonempty)
  obtain ⟨t, ht_app, h_eq⟩ := Finset.mem_image.mp ha_in_heads
  simp [mem_applicable] at ht_app
  -- a = min' heads h_nonempty
  have ha_le_t : aa ≤ t.head := by
    subst hmin
    apply Finset.min'_le
    obtain ⟨left, right⟩ := ht_app
    obtain ⟨left_1, right⟩ := right
    rw [h_eq]
    exact ha_in_heads
  have : t.head ≤ aa := by
    --apply Finset.min'_le
    subst hmin
    simp_all only
  have : t.head = aa := le_antisymm this ha_le_t
  rw [this] at ht_app
  constructor
  · subst hmin
    simp_all only [Finset.mem_image, le_refl, heads, aa]
    apply Aesop.BuiltinRules.not_intro
    intro a
    exact ht_app.2.2 a
  · use t
    constructor
    · subst hmin
      obtain ⟨left, right⟩ := ht_app
      exact left
    · constructor
      · subst hmin
        obtain ⟨left, right⟩ := ht_app
        obtain ⟨left_1, right⟩ := right
        exact left_1
      · subst hmin
        simp_all only
        simp_all only [Finset.mem_image, le_refl, heads, aa]
        rfl


/-- 1ステップ：最小 head を加える（無ければ同じ I を返す） -/
def step2 (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  match nextHead? R I with
  | none   => I
  | some a => insert a I

lemma step_id_of_none {R : Finset (Rule α)} {I : Finset α}
  (h : nextHead? R I = none) : step2 R I = I := by
  simp [step2, h]

lemma step_card_succ_if_some
  {R : Finset (Rule α)} {I : Finset α} {a : α}
  (h : nextHead? R I = some a) :
  (step2 R I).card = I.card + 1 := by
  classical
  rcases nextHead?_spec_some (R:=R) (I:=I) (a:=a) h with ⟨haI, _⟩
  simp [step2]
  simp_all only [not_false_eq_true, Finset.card_insert_of_notMem]

lemma step_card_le_succ {R : Finset (Rule α)} {I : Finset α} :
  (step2 R I).card ≤ I.card + 1 := by
  classical
  by_cases h : nextHead? R I = none
  · simp [step2, h]
  · simp at h
    dsimp [nextHead?] at h
    simp at h
    dsimp [applicable] at h
    simp at h
    rcases h with _ | _
    dsimp [step2]
    rename_i h
    simp_all only [Multiset.quot_mk_to_coe'', Finset.union_singleton]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split
    next x heq => simp_all only [le_add_iff_nonneg_right, zero_le]
    next x a_1 heq => apply Finset.card_insert_le

def syncClIter (R : Finset (Rule α)) (I : Finset α) : Nat → Finset α
  | 0       => I
  | k + 1   =>
    let J := syncClIter R I k
    match nextHead? R J with
    | none   => J
    | some a => insert a J

/-
/-- 反復版：上限 |α| で十分停止 -/
def syncClIter (R : Finset (Rule α)) : Finset α → Nat → Finset α
  | I, 0     => I
  | I, Nat.succ k =>
      match nextHead? R I with
      | none   => I
      | some a => syncClIter R (I ∪ {a}) k
-/

def syncCl [Fintype α] (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  syncClIter R I (Fintype.card α)

/-- 逐次的に単調増加 -/
lemma step_increasing (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ step R I := by
  classical
  unfold step
  by_cases h : nextHead? R I = none
  · simp_all only [Finset.subset_union_left]
  · simp_all only [Finset.subset_union_left]

-- 任意段数 n に対して「I の元は n ステップ同期閉包にも含まれる」という一般補題
lemma mem_syncClIter_of_mem
  [DecidableEq α]
  (R : Finset (Rule α)) :
  ∀ n (I : Finset α) (a : α), a ∈ I → a ∈ syncClIter R I n := by
  classical
  refine Nat.rec
    (motive := fun n => ∀ (I : Finset α) (a : α), a ∈ I → a ∈ syncClIter R I n)
    ?base
    ?step
  · -- n = 0
    intro I a ha
    -- あなたの定義に合わせて：例) syncClIter R I 0 = I
    simpa [syncClIter] using ha
  · -- n → n+1
    intro n IH I a ha
    -- あなたの定義に合わせて場合分解：例) nextHead? R I
    cases h : nextHead? R I with
    | none =>
        -- 例) none なら syncClIter R I (n+1) = I
        simp [syncClIter]
        split
        next x heq => simp_all only
        next x a_1 heq => simp_all only [Finset.mem_insert, or_true]

    | some r =>
        -- 例) some r なら syncClIter R I (n+1) = syncClIter R (I ∪ {r}) n
        have ha' : a ∈ I ∪ ({r} : Finset α) := by
          -- a ∈ I から a ∈ I ∪ {r}
          exact (Finset.mem_union.mpr (Or.inl ha))
        have : a ∈ syncClIter R (I ∪ ({r} : Finset α)) n := IH (I ∪ {r}) a ha'
        simp [syncClIter]
        simp_all only [Finset.union_singleton, Finset.mem_insert, or_true]
        split
        next x heq => simp_all only
        next x a_1 heq => simp_all only [Finset.mem_insert, or_true]


 lemma syncCl_infl
   [Fintype α] [DecidableEq α]
  {R : Finset (Rule α)} {I : Finset α} :
  I ⊆ syncCl R I := by
  classical
  intro a ha
  -- syncCl の定義が「Fintype.card α ステップの syncClIter」だと仮定
  unfold syncCl
  -- 先ほどの一般補題をカードに適用して使う
  have gen := mem_syncClIter_of_mem (R := R)
  exact gen (Fintype.card α) I a ha

lemma applicable_empty_nextHead_none
  {R : Finset (Rule α)} {I : Finset α}
  (h : applicable R I = ∅) :
  nextHead? R I = none := by
  classical
  unfold nextHead?
  simp_all only [Finset.image_empty, Finset.not_nonempty_empty, ↓reduceDIte]

/-- `IsClosed R I` と `applicable R I = ∅` は同値 -/
lemma closed_iff_applicable_empty
  {R : Finset (Rule α)} {I : Finset α} :
  IsClosed R I ↔ applicable R I = ∅ := by
  classical
  constructor
  · intro hcl
    -- 閉なら「prem ⊆ I かつ head ∉ I」を満たす規則が存在しない
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    rcases (mem_applicable.mp ht) with ⟨htR, hsub, hnot⟩
    have : t.head ∈ I := hcl htR hsub
    exact hnot this
  · intros happ t htR hsub
    by_contra hnot
    -- すると t が applicable に入ってしまい矛盾
    have : t ∈ applicable R I := by
      exact (mem_applicable.mpr ⟨htR, hsub, hnot⟩)
    have : False := by
      have := congrArg (fun (s : Finset (Rule α)) => t ∈ s) happ
      simp_all only [Finset.notMem_empty]

    exact False.elim this

/-- none になったら以後固定点 -/
lemma syncClIter_fix_of_none
  {R : Finset (Rule α)} {I : Finset α} {k : Nat}
  (h : nextHead? R I = none) :
  syncClIter R I k = I := by
  classical
  induction k with
  | zero => simp [syncClIter]
  | succ k IH =>
      simp [syncClIter]
      simp_all only

/-- 反復の各段階でのカード上界（高々 +1） -/
lemma card_syncClIter_le (R : Finset (Rule α)) :
  ∀ (k : Nat) (I : Finset α), (syncClIter R I k).card ≤ I.card + k := by
  classical
  intro k; induction k with
  | zero =>
    intro I
    simp [syncClIter]
  | succ k IH =>
    intro I
    -- nextHead? R I を等式つきで分解
    cases h : nextHead? R I with
    | none =>
      -- ルール発火なし → 次段も I のまま
      -- 目標: I.card ≤ I.card + (k+1)
      have : I.card ≤ I.card + Nat.succ k := Nat.le_add_right _ _
      simp [syncClIter]
      split
      exact Nat.le_succ_of_le (IH I)
      rename_i h aa
      let J := syncClIter R I k
      have h_notin : h ∉ J := (nextHead?_spec_some aa).left
      have card_succ : (insert h J).card = J.card + 1 := Finset.card_insert_of_notMem h_notin
      calc
      (insert h J).card = J.card + 1 := card_succ
      _ ≤ I.card + k + 1 := add_le_add_right (IH I) _

    | some a =>
      -- ルールが 1 個発火 → 次段は insert a I から k ステップ進めたもの
      -- 帰納法の仮定を insert a I に適用
      have hIH : (syncClIter R (insert a I) k).card ≤ (insert a I).card + k := IH (insert a I)
      -- (insert a I).card ≤ I.card + 1
      have hcard : (insert a I).card ≤ I.card + 1 := by
        simpa using (Finset.card_insert_le (s := I) (a := a))
      -- 両辺に + k して
      have hcard' : (insert a I).card + k ≤ I.card + (1 + k) := by
        rw [Nat.add_comm, Nat.add_left_comm]
        simp_all only
        omega
      -- 1 + k = succ k
      have hcard'' : (insert a I).card + k ≤ I.card + Nat.succ k := by
        simp_all only [Nat.succ_eq_add_one]
        omega
      let lth := le_trans hIH (by simpa [syncClIter, h] using hcard'')
      simp [syncClIter]
      revert IH hIH hcard hcard' hcard'' lth
      suffices eq : syncClIter R I (k + 1) = syncClIter R (insert a I) k from by
        intro IH hIH hcard hcard' hcard'' lth
        change (syncClIter R I (k + 1)).card ≤ I.card + (k + 1)
        rw [eq]
        exact lth
      -- Now prove eq without the reverted assumptions (ih will be unconditional)
      induction' k with k ih
      · simp [syncClIter]
        simp_all
      · have left : syncClIter R I (k + 2) = step2 R (syncClIter R I (k + 1)) := rfl
        have right : syncClIter R (insert a I) (k + 1) = step2 R (syncClIter R (insert a I) k) := rfl
        rw [left, right, ih]


/-- 停止したら以後も同じ集合のまま（停止は不変） -/
lemma stops_constant
    (R : Finset (Rule α)) :
  ∀ {I k}, nextHead? R I = none → syncClIter R I k = I := by
  classical
  intro I k h
  induction k with
  | zero =>
      simp [syncClIter]
  | succ k IH =>
      -- 1 ステップ目で止まる
      have : syncClIter R I 1 = I := by
        -- 定義から `none` のときはそのまま
        simp [syncClIter, h]
      -- 2 ステップ目以降も同じ（以後も nextHead? R I = none を再評価する形だが，定義から都度 I のまま）
      exact syncClIter_fix_of_none h

/-- 段 i で `some` なら基数が 1 つ増える -/
lemma step_card_succ_of_some
    (R : Finset (Rule α)) [DecidableEq α]
    {I : Finset α} {a : α}
    (h : nextHead? R I = some a) :
  (syncClIter R I (Nat.succ 0)).card = I.card + 1 := by
  classical
  -- 1 ステップだけ進める形（定義に沿って前段で some a を使う）
  have a_notin : a ∉ I := (nextHead?_spec_some h).1
  -- 1 ステップの `syncClIter` は `insert a I` になるように定義されているはず
  -- （ユーザ定義が `I ∪ {a}` でも `insert` と同値です）
  have : syncClIter R I 1 = insert a I := by
    -- ユーザ定義：`simp [syncClIter, h]` で `insert a I`（または `I ∪ {a}`）に落ちます
    simp [syncClIter, h]
  -- 基数はちょうど +1
  simpa [this, Nat.succ_eq_add_one] using Finset.card_insert_of_notMem a_notin

lemma syncClIter_add
    (R : Finset (Rule α)) (I : Finset α) :
  ∀ i m, syncClIter R I (i + m) = syncClIter R (syncClIter R I i) m := by
  classical
  intro i m
  induction m with
  | zero =>
      simp
      exact rfl
  | succ m IH =>
      -- 1 ステップ進める定義は `nextHead?` で分岐するだけなので，
      -- 分岐点の引数が一致すれば両辺そろいます
      -- 分岐の引数を一致させるために IH で書き換えます
      cases h : nextHead? R (syncClIter R I (i + m)) with
      | none   => simp [syncClIter, IH]
      | some a => simp [syncClIter, IH]

lemma all_prev_some_of_some_at_j
    (R : Finset (Rule α)) [DecidableEq α]
    (I : Finset α) :
  ∀ {j a}, nextHead? R (syncClIter R I j) = some a →
    ∀ i, i < j → ∃ b, nextHead? R (syncClIter R I i) = some b := by
  classical
  intro j a hj i hi
  -- もし i で none なら，以後ずっと同じ集合で none のはずなので j でも none になる矛盾
  by_contra hnone
  push_neg at hnone
  have hstop : syncClIter R I j = syncClIter R I i := by
    -- i で停止 → 以後一定
    let hnone_eq : nextHead? R (syncClIter R I i) = none :=
      by
        simp_all only [ne_eq]
        ext a_1 : 1
        simp_all only [reduceCtorEq]

    have hc := stops_constant (R:=R) (I:=syncClIter R I i) (k:=j-i) hnone_eq
    rw [←hc]
    show syncClIter R I j = syncClIter R (syncClIter R I i) (j - i)
    let ca := syncClIter_add R I i (j - i)
    simp at ca
    have :i + (j - i) = j := by
      omega
    rw [this] at ca
    exact ca
    --have hc := stops_constant (R:=R) (I:=syncClIter R I i) (k:=j-i) hnone
    -- `syncClIter R I (i + (j-i)) = syncClIter R I i`
    --simp [Nat.add_sub_cancel_of_le hi.le, Nat.add_comm, Nat.add_sub_cancel]

  -- ところが j では some と仮定したので矛盾
  have : nextHead? R (syncClIter R I i) = some a := by simpa [hstop] using hj
  exact hnone a this

/-- 「各段で some」なら段 m で基数は少なくとも `I.card + m` -/
lemma card_ge_if_all_some_up_to
    (R : Finset (Rule α)) [DecidableEq α]
    (I : Finset α) :
  ∀ m, (∀ i, i < m → ∃ a, nextHead? R (syncClIter R I i) = some a) →
    (syncClIter R I m).card ≥ I.card + m := by
  classical
  intro m
  induction m with
  | zero =>
      intro _; simp
      exact (Finset.eq_iff_card_ge_of_superset fun ⦃a⦄ a => a).mpr rfl
  | succ m IH =>
      intro hsome
      -- 段 m での some を取り出す
      rcases hsome m (Nat.lt_succ_self m) with ⟨a, ha⟩
      -- 前段 m までの仮定を適用
      have hprev : ∀ i, i < m → ∃ a, nextHead? R (syncClIter R I i) = some a := by
        intro i hi; exact hsome i (Nat.lt_trans hi (Nat.lt_succ_self m))
      -- 帰納法の下界
      have hIH := IH hprev
      -- 段 m → m+1 で +1
      have hstep : (syncClIter R I (m+1)).card = (syncClIter R I m).card + 1 :=
        by
          -- `ha : nextHead? R (syncClIter R I m) = some a`
          -- 1 ステップ分の補題を適用
          -- まず `step_card_succ_of_some` を `I := syncClIter R I m` に流用
          have := step_card_succ_of_some (R:=R) (I:=syncClIter R I m) (a:=a) ha
          simpa [Nat.succ_eq_add_one]
      -- したがって下界は 1 増える
      have := by
        have := Nat.le_of_eq hstep
        exact this
      -- 整理
      -- hstep は = なので，`by` で書き換えてから `linarith` でも OK
      have : (syncClIter R I (Nat.succ m)).card ≥ I.card + (Nat.succ m) := by
        -- hIH : (syncClIter R I m).card ≥ I.card + m
        -- hstep : (=) なので，両辺に +1
        have := calc
          (syncClIter R I (Nat.succ m)).card
              = (syncClIter R I m).card + 1 := hstep
          _ ≥ (I.card + m) + 1 := Nat.add_le_add_right hIH 1
          _ = I.card + Nat.succ m := by simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        exact this
      simpa using this

lemma exists_stop_index
    (R : Finset (Rule α)) (I : Finset α)
    [Fintype α] [DecidableEq α] :
  ∃ j ≤ Fintype.card α, nextHead? R (syncClIter R I j) = none := by
  classical
  -- j を card α - I.card にとる
  let j := Fintype.card α - I.card
  refine ⟨j, Nat.sub_le _ _, ?_⟩
  -- 反証：まだ発火できる
  by_contra hnone
  rcases Option.ne_none_iff_exists.mp hnone with ⟨a, ha⟩
  -- 段 j まで全て `some`（止まったら以後不変の対偶）
  have hall : ∀ i, i < j → ∃ b, nextHead? R (syncClIter R I i) = some b := by
    exact fun i a_1 => all_prev_some_of_some_at_j R I (id (Eq.symm ha)) i a_1
  -- したがって段 j の基数は I.card + j 以上
  have hge : (syncClIter R I j).card ≥ I.card + j :=
    card_ge_if_all_some_up_to (R:=R) (I:=I) j hall
  -- j の定義を展開
  have hj : I.card + j = Fintype.card α := by
    unfold j; exact Nat.add_sub_of_le (Finset.card_le_univ I)
  -- 段 j の直後はさらに +1
  have hstep : (syncClIter R I (j+1)).card = (syncClIter R I j).card + 1 := by
    -- `ha : nextHead? R (syncClIter R I j) = some a`
    have := step_card_succ_of_some (R:=R) (I:=syncClIter R I j) (a:=a)
    exact this (id (Eq.symm ha))
  -- 以上より (j+1) 段で基数 ≥ card α + 1
  have hgt : (syncClIter R I (j+1)).card ≥ Fintype.card α + 1 := by
    have : (syncClIter R I j).card ≥ Fintype.card α := by simpa [hj] using hge
    simpa [hstep, Nat.add_comm] using Nat.add_le_add_right this 1
  -- しかし有限集合の部分集合の基数は card α 以下
  have hle : (syncClIter R I (j+1)).card ≤ Fintype.card α :=
    Finset.card_le_univ _
  exact (Nat.lt_of_le_of_lt hle hgt).false

/-- `syncCl` は R-閉 -/
lemma syncCl_closed {R : Finset (Rule α)} {I : Finset α} [Fintype α] [DecidableEq α] :
  IsClosed R (syncCl R I) := by
  classical
  -- ある j ≤ |α| で nextHead? R (syncClIter R I j) = none
  rcases exists_stop_index R I with ⟨j, hj, hjnone⟩
  -- j 以降は固定点: syncClIter R (syncClIter R I j) k = syncClIter R I j
  have fix : ∀ k, syncClIter R (syncClIter R I j) k = syncClIter R I j := by
    intro k
    apply stops_constant R hjnone
  -- syncCl R I = syncClIter R I j を証明
  have syncCl_eq : syncCl R I = syncClIter R I j := by
    unfold syncCl
    have : Fintype.card α = j + (Fintype.card α - j) := by
      rw [add_comm]
      exact (Nat.sub_eq_iff_eq_add hj).mp rfl
    rw [this, syncClIter_add]
    exact fix (Fintype.card α - j)
  -- IsClosed R (syncCl R I) を証明
  rw [syncCl_eq]

  unfold IsClosed
  -- nextHead? R (syncClIter R I j) = none より、IsClosed の定義が成り立つ
  intro t ht hprem
  have hnone := nextHead?_spec_none hjnone
  dsimp [applicable] at hnone
  simp_all only [Finset.filter_eq_empty_iff, not_and, Decidable.not_not]


lemma syncCl_subset_of_closed
  {R : Finset (Rule α)} {I J : Finset α} [Fintype α] [DecidableEq α]
  (hIJ : I ⊆ J) (hJ : IsClosed R J) :
  syncCl R I ⊆ J := by
  classical
  -- syncCl R I = syncClIter R I (Fintype.card α)
  unfold syncCl
  -- 反復に対する一般形: ∀ k, syncClIter R I k ⊆ J
  have : ∀ k, syncClIter R I k ⊆ J := by
    intro k
    induction k with
    | zero => simpa [syncClIter] using hIJ
    | succ k IH =>
      simp [syncClIter]
      by_cases h : nextHead? R (syncClIter R I k) = none
      · simp [h, IH]
      · have ⟨a, ha⟩ := Option.ne_none_iff_exists.mp h
        obtain ⟨haI, t, htR, hsub, heq⟩ := nextHead?_spec_some ha.symm
        rw [← ha]
        apply Finset.insert_subset
        · -- t.head ∈ J (using heq to replace a with t.head)
          have : t.prem ⊆ J := by exact fun ⦃a⦄ a_1 => IH (hsub a_1)
          have : t.head ∈ J := by exact hJ htR this
          subst heq; exact this
        · exact IH
  -- k = Fintype.card α を適用
  exact this (Fintype.card α)

end Twostem
