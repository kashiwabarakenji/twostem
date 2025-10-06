import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.SymmDiff
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.NDS
import Twostem.MainCore

namespace Twostem

--addedFamilyの定義と、weak_liftingとhead_not_in_closure_of_eraseとisWitness_disjointは使うかもしれないが、そのあとは消しても影響ないかも。

open scoped BigOperators
open scoped symmDiff
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)]

--/***********************
-- * 4. 弱化リフティング
-- ***********************/
noncomputable def addedFamily
  [DecidableEq α] [DecidableEq (Rule α)]
  (R : Finset (Rule α)) (t : Rule α) :
  Finset (Finset α) := by
  classical
  -- Family (R.erase t) で必要になる決定性インスタンスをローカルに用意
  letI : DecidablePred (IsClosed (R.erase t)) :=
    fun I => Classical.dec (IsClosed (R.erase t) I)
  -- R \ {t} で閉じていて、かつ t が「適用可能（prem⊆I かつ head∉I）」な I を集める
  exact (Family (α := α) (R.erase t)).filter
    (fun I => t.prem ⊆ I ∧ t.head ∉ I)

omit [DecidableEq α] [Fintype α] [DecidableEq (Rule α)] in
--補題5.1あたり。今の所直接は参照されてないが、重要な可能性はある。
lemma weak_lifting [Fintype α] [DecidableEq α] [DecidableEq (Rule α)]
  (ρ : RuleOrder α) (R : Finset (Rule α)) [DecidablePred (IsClosed R)]
  (hUC : UC R)
  (B S : Finset α) (t : Rule α)
  (hwit : isWitness (α:=α)  ρ R B S t) :
  let J := syncCl (R.erase t) (B ∪ S)
  t.prem ⊆ J ∧ t.head ∉ J ∧ J ∈ addedFamily  R t := by
  classical
  intro J
  rcases hwit with ⟨hSsub, hfirst⟩
  rcases hfirst with ⟨⟨htR, htPrem, htHead⟩, hmin⟩
  -- (1) prem ⊆ J
  have h1 : t.prem ⊆ J := by
    intro x hx
    have hx' : x ∈ B ∪ S := htPrem hx
    dsimp [J]
    show x ∈ syncCl (R.erase t) (B ∪ S)
    exact syncCl_infl (α:=α) (R:=R.erase t) (I:=B ∪ S) hx'

    --exact subset_closure_of_subset (R:=R.erase t) (X:=B ∪ S) hx'
  -- (2) head ∉ J ：`head_from_Rerase_contra_first` に依存
  have h2 : t.head ∉ J := by
    intro contra
    apply head_from_Rerase_contra_first (α:=α) ρ R hUC B S t ⟨⟨htR, htPrem, htHead⟩, hmin⟩
    dsimp [J] at contra
    simp [syncCl]
    simp [syncCl] at contra
    convert contra

  -- (3) addedFamily メンバ性
  have hJclosed : IsClosed (R.erase t) J := by exact syncCl_closed (R.erase t) (B ∪ S)
  have hJmem : J ∈ Family (α:=α) (R.erase t) := by
    simp_all only [mem_union, not_or, IsClosed, mem_erase, ne_eq, and_imp, J]
    obtain ⟨left, right⟩ := htHead
    rw [Family]
    simp_all only [IsClosed, mem_erase, ne_eq, and_imp, powerset_univ, mem_filter, mem_univ, not_false_eq_true,
      implies_true, and_self]
  have hfilter : (t.prem ⊆ J ∧ t.head ∉ J) := ⟨h1, h2⟩
  have : J ∈ (Family (α:=α) (R.erase t)).filter
            (fun I => t.prem ⊆ I ∧ t.head ∉ I) := by
    simpa [mem_filter] using And.intro hJmem hfilter
  exact And.intro h1 (And.intro h2 (by simpa [addedFamily] using this))

--補題5.1
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- UC から：t を外した閉包から t.head は出てこない。 -/
lemma head_not_in_closure_of_erase
  [Fintype α] [DecidableEq α] [DecidableEq (Rule α)]
  {R : Finset (Rule α)} {t : Rule α} {I : Finset α}
  (hUC : UC R) (ht : t ∈ R) (hnotI : t.head ∉ I) :
  t.head ∉ syncCl (R.erase t) I := by
  classical
  -- “parIter で得られる要素は I か、R のどれかの head”
  have origin :
    ∀ {k a}, a ∈ parIter (R.erase t) I k →
      a ∈ I ∨ ∃ s ∈ R.erase t, s.head = a := by
    intro k a hk; revert a hk
    induction k with
    | zero =>
        intro a hk; left; exact hk
    | succ k ih =>
        intro a hk
        -- hk : a ∈ stepPar (R.erase t) (parIter (R.erase t) I k)
        rcases Finset.mem_union.mp hk with hkL | hkR
        · exact ih hkL
        · rcases Finset.mem_image.mp hkR with ⟨s, hsApp, hEq⟩
          -- applicable の分解から s ∈ R.erase t
          have hsR : s ∈ R.erase t :=
            (Finset.mem_filter.mp hsApp).1
          right; exact ⟨s, hsR, hEq⟩

  -- 反証：閉包に入ると仮定
  intro hIn
  -- syncCl = parIter … (|α|)
  have : t.head ∈ parIter (R.erase t) I (Fintype.card α) := by
    exact hIn
  -- 出自分解
  have hsrc := origin this
  -- 初期にはないので「誰かの head」として入ったはず
  rcases hsrc with hI | ⟨s, hsErase, hEq⟩
  · exact hnotI hI
  -- ここから UC で `s = t` を導く（erase に矛盾）
  have hs_ne_t : s ≠ t := (Finset.mem_erase.mp hsErase).1
  have hs_in_R : s ∈ R := (Finset.mem_erase.mp hsErase).2

  -- UC: 同じ head を持つ規則は一意
  have s_eq_t : s = t := by
    -- S := {u ∈ R | u.head = t.head} は card ≤ 1
    set S := R.filter (fun u => u.head = t.head) with hS
    have hsS : s ∈ S := by
      -- s ∈ R ∧ s.head = t.head
      apply Finset.mem_filter.mpr
      exact And.intro hs_in_R (by
        -- hEq : s.head = t.head
        exact hEq)
    have htS : t ∈ S := by
      apply Finset.mem_filter.mpr
      exact And.intro ht (by rfl)
    -- もし s ≠ t なら、S は少なくとも 2 要素になる（矛盾）
    by_contra hne
    -- t は S.erase s に入る
    have t_in_erase : t ∈ S.erase s := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hne, htS⟩
    -- erase が非空 → (S.erase s).card ≥ 1
    have pos : 0 < (S.erase s).card :=
      Finset.card_pos.mpr ⟨t, t_in_erase⟩
    -- s ∈ S なので、card (S) = card (S.erase s) + 1 ≥ 2
    have step : (S.erase s).card + 1 = S.card :=
      Finset.card_erase_add_one hsS
    have two_le : Nat.succ 1 ≤ S.card := by
      have one_le : 1 ≤ (S.erase s).card := Nat.succ_le_of_lt pos
      have : 1 + 1 ≤ (S.erase s).card + 1 :=
        Nat.add_le_add_right one_le 1
      -- 書き換え
      have : 1 + 1 ≤ S.card := by
        have htmp := this
        rw [step] at htmp
        exact htmp
      -- 1+1 = Nat.succ 1
      -- 以後の定理と相性の良い形に直す
      simpa [Nat.succ_eq_add_one] using this
    -- UC の仮定（S.card ≤ 1）と矛盾
    have hSle1 : S.card ≤ 1 := by
      -- hUC t.head はまさに S のカード制限
      have := hUC t.head
      -- S の定義で書き換え不要（同じ定義）
      exact this
    exact Nat.not_succ_le_self 1 (le_trans two_le hSle1)
  -- しかし s = t なら erase に入れない
  exact hs_ne_t s_eq_t

--/***********************
-- * 5. 多重度 ≤ 1（Two-Stem + UC）
-- ***********************/

omit [DecidableEq (Rule α)] in
private lemma isWitness_disjoint
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B S : Finset α) (t : Rule α)
  (hW : isWitness ρ R B S t) :
  Disjoint B S := by
  have hS_free : S ⊆ FreeOf B := hW.1
  unfold FreeOf at hS_free
  -- S ⊆ (univ \ B) ⇒ Disjoint B S
  --dsimp [Disjoint, Finset.disjoint_iff_inter_eq_empty]

  (expose_names; rw [subset_sdiff] at hS_free)
  simp_all only [subset_univ, true_and]
  rw [disjoint_iff] at hS_free ⊢
  simp_all only [inf_eq_inter, bot_eq_empty]
  rwa [inter_comm]

----ここから後ろはほとんど使われてないものが並んでいる。

--使わないかも。
omit [Fintype α] [DecidableEq (Rule α)] in
lemma syncClIter_mono_in_steps (R : Finset (Rule α)) (I : Finset α) (k : ℕ) :
  syncClIter R I k ⊆ syncClIter R I (k + 1) := by
  unfold syncClIter
  cases h : nextHead? R (syncClIter R I k) with
  | none =>
    -- nextHead? が none なら変化なし
    simp_all only
    split
    next x => rfl
    next x k =>
      simp_all only [Nat.succ_eq_add_one]
      rfl

  | some a =>
    -- nextHead? が some a なら a を追加
    simp_all only
    split
    exact subset_insert a I
    (expose_names;
      exact
        subset_insert a
          (match nextHead? R (syncClIter R I k) with
          | none => syncClIter R I k
          | some a => insert a (syncClIter R I k)))

--使われてない
omit [Fintype α] [DecidableEq (Rule α)] in
lemma syncClIter_increasing (R : Finset (Rule α)) (I : Finset α) :
  ∀ k₁ k₂, k₁ ≤ k₂ → syncClIter R I k₁ ⊆ syncClIter R I k₂ := by
  intro k₁ k₂ h
  induction h with
  | refl =>
    -- k₁ = k₂ の場合
    exact Finset.Subset.refl _
  | step h ih =>
    -- k₁ ≤ k₂ → k₁ ≤ k₂ + 1
    calc syncClIter R I k₁
      ⊆ syncClIter R I _ := ih
      _ ⊆ syncClIter R I (_ + 1) := syncClIter_mono_in_steps R I _

--使われてない
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma unique_S_of_union_eq
  [DecidableEq α]
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hUV : B ∪ S₁ = B ∪ S₂) : S₁ = S₂ :=
disjoint_union_eq_implies_right_eq hD1 hD2 hUV

/- 2つの閉包が異なるなら、最初に食い違う段 `k`（`k ≤ card α`）が取れる。
    その直前では一致している。 -/
--使われている。
omit [LinearOrder α] [DecidableEq (Rule α)] in
private lemma parIter_subset_syncCl
  (R : Finset (Rule α)) (I : Finset α) :
  ∀ k, parIter R I k ⊆ syncCl R I := by
  intro k; induction k with
  | zero =>
      simpa using (syncCl_infl (R:=R) (I:=I))
  | succ k ih =>
      -- parIter (k+1) = stepPar R (parIter k)
      -- stepPar_mono と syncCl の閉性で閉じる
      intro a ha
      have : stepPar R (parIter R I k) ⊆ stepPar R (syncCl R I) :=
        (stepPar_mono R) ih
      have hclosed : IsClosed R (syncCl R I) := by
        simpa using (syncCl_closed (R:=R) (I:=I))
      -- IsClosed R J から stepPar R J ⊆ J が出る定義（※あなたの定義に依存）
      -- REPLACE: もし `IsClosed` の定義が `stepPar R J = J` なら `simp` で同様に閉じます。
      have hstep_sub : stepPar R (syncCl R I) ⊆ (syncCl R I) := by
        -- 多くの環境では `IsClosed` が `stepPar R X ⊆ X` のこと
        dsimp [stepPar, IsClosed] at hclosed
        dsimp [stepPar]
        intro x hx
        simp_all only [mem_union, mem_image, mem_filter]
        cases hx with
        | inl h => simp_all only
        | inr h_1 =>
          obtain ⟨w, h⟩ := h_1
          obtain ⟨left, right⟩ := h
          subst right
          simp_all only

      -- まとめ
      have : stepPar R (parIter R I k) ⊆ syncCl R I :=
        fun x hx => hstep_sub (this hx)
      simpa [parIter] using this ha

--使われている
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)]in
private lemma syncCl_eq_parIter_card
  [DecidableEq α] [Fintype α]
  (R : Finset (Rule α)) (I : Finset α) :
  syncCl R I = parIter R I (Fintype.card α) := by
  -- ⊆ 方向（最小性）
  have hfix : stepPar R (parIter R I (Fintype.card α))
              = parIter R I (Fintype.card α) :=
    parIter_eventually_stops (R:=R) (I:=I)
  -- IsClosed の取り方（定義に合わせて一方を使う）
  have hclosed_sub : IsClosed R (parIter R I (Fintype.card α)) := by
    -- (1) IsClosed R X : stepPar R X ⊆ X なら：
    --     `stepPar R (parIter ...) = parIter ...` から包含が従う
    --     IsClosed の形に合わせて `exact ?_` で埋める
    --     例：`def IsClosed R X := stepPar R X ⊆ X` なら：
    exact
      (by
        -- stepPar R (parIter ...) = parIter ...
        -- ならば stepPar R (parIter ...) ⊆ parIter ...
        -- （等号は包含を与える）
        have : stepPar R (parIter R I (Fintype.card α))
                   ⊆ parIter R I (Fintype.card α) :=
          fun x hx => Eq.mp (by
            apply congrArg (fun S => x ∈ S); exact hfix) hx
        -- IsClosed の定義に合わせて戻す
        -- def IsClosed … なら `exact this` でOK
        dsimp [IsClosed]
        intro t ht h
        exact parIter_saturates R I t ht h
      )
    -- (2) IsClosed R X : stepPar R X = X なら：
    -- exact (by exact hfix)

  -- I ⊆ parIter _ (card α)
  have hInfl : I ⊆ parIter R I (Fintype.card α) :=
    (parIter_increasing (R:=R) (I:=I) 0 (Fintype.card α) (Nat.zero_le _))

  -- 最小閉包性：syncCl ⊆ parIter card
  have h1 : syncCl R I ⊆ parIter R I (Fintype.card α) :=
    syncCl_min (R:=R) (I:=I) (J:=parIter R I (Fintype.card α)) hInfl hclosed_sub

  -- 逆向き：parIter card ⊆ syncCl（Aで示した補題）
  have h2 : parIter R I (Fintype.card α) ⊆ syncCl R I :=
    parIter_subset_syncCl (R:=R) (I:=I) (Fintype.card α)

  -- まとめ
  apply Finset.Subset.antisymm_iff.mpr
  exact And.intro h1 h2

--コメントアウトしたものの中で使われている。
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma exists_min_k_of_syncCl_ne
  [DecidableEq α] [Fintype α]
  {R' : Finset (Rule α)} {U V : Finset α}
  (hne : syncCl (R:=R') U ≠ syncCl (R:=R') V) :
  ∃ k, k ≤ Fintype.card α ∧
    parIter R' U k ≠ parIter R' V k ∧
    (k = 0 ∨ parIter R' U (k-1) = parIter R' V (k-1)) := by
  classical
  -- 有限単調列 `parIter` は `card α` 回以内に安定：`syncCl` に到達
  -- 異なる極限 ⇒ どこかで初めて食い違う段が存在
  -- 実装は既存の安定化補題（あなたの環境なら `parIter_stabilizes_at_card` 相当）
  -- と `by_contra` + 最小性で取れます。
  -- （ここは数行で書ける定型；既存の安定化補題名に合わせて埋めてください）
  have hU : syncCl R' U = parIter R' U (Fintype.card α) :=
    syncCl_eq_parIter_card (R:=R') (I:=U)
  have hV : syncCl R' V = parIter R' V (Fintype.card α) :=
    syncCl_eq_parIter_card (R:=R') (I:=V)

  -- 非空集合 S := {n ≤ card α ∧ parIter U n ≠ parIter V n}
  have hex : ∃ n, n ≤ Fintype.card α ∧ parIter R' U n ≠ parIter R' V n := by
    refine ⟨Fintype.card α, le_rfl, ?_⟩
    intro hEq
    -- `calc` で hne へ反する等式を作る
    have : syncCl R' U = syncCl R' V := by
      calc
        syncCl R' U = parIter R' U (Fintype.card α) := hU
        _           = parIter R' V (Fintype.card α) := hEq
        _           = syncCl R' V := Eq.symm hV
    exact hne this

  -- 最小 n を取る
  let P : ℕ → Prop := fun n =>
    n ≤ Fintype.card α ∧ parIter R' U n ≠ parIter R' V n
  -- ★ ローカルに DecidablePred を与える（グローバル instance は作らない）
  haveI : DecidablePred P := by
    intro n
    -- classical で Prop は非構成的に可判定になる
    classical
    exact inferInstance

  have hexP : ∃ n, P n := by
    rcases hex with ⟨n, hle, hneq⟩
    exact ⟨n, And.intro hle hneq⟩

  -- k を最小の n として取得
  let k := Nat.find hexP
  have hkP : P k := Nat.find_spec hexP

  -- 成分を取り出し
  have hk_le : k ≤ Fintype.card α := hkP.left
  have hk_ne : parIter R' U k ≠ parIter R' V k := hkP.right

  -- ★ 最小性：m < k なら P m は成り立たない
  have hk_min : ∀ m, m < k → ¬ P m := by
    intro m hm
    -- 反証法：P m と仮定
    intro hPm
    -- Nat.find_min' で k ≤ m
    have hk_le_m : k ≤ m := Nat.find_min' hexP hPm
    -- m < k と矛盾
    exact (not_le_of_gt hm) hk_le_m

  -- ここから「前段一致」を作る例
  have hprev : k = 0 ∨ parIter R' U (k-1) = parIter R' V (k-1) := by
    -- ¬(k ≠ 0 ∧ parIter U (k-1) ≠ parIter V (k-1))
    -- の否定を場合分けで示す
    -- 反証法：¬(A ∨ B) → A ∧ B
    -- から ¬A ∧ ¬B を導く
    -- つまり k ≠ 0 かつ parIter U (k-1) ≠ parIter V (k-1) と仮定して矛盾を導く
    -- 1) k ≠ 0 なら k-1 < k なので
    simp_all [P, k]
    obtain ⟨w, h⟩ := hexP
    obtain ⟨left, right⟩ := h
    tauto

  refine ⟨k, hkP.left, hkP.right, ?_⟩
  by_cases h0 : k = 0
  · exact Or.inl h0
  · right
    have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have hkm : k - 1 < k := Nat.sub_lt hkpos (Nat.succ_pos 0)
    have : ¬ P (k-1) := hk_min (k-1) hkm
    -- `¬(A ∧ B)` から場合分け
    have hcase : k - 1 > Fintype.card α ∨
                 parIter R' U (k-1) = parIter R' V (k-1) := by
      by_cases hle : k - 1 ≤ Fintype.card α
      · -- ならば「≠」部分が偽
        have : ¬(parIter R' U (k-1) ≠ parIter R' V (k-1)) := by
          intro hneq; exact this ⟨hle, hneq⟩
        exact Or.inr (Classical.not_not.mp this)
      · left
        refine (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ?_) (ne_of_lt ?_))
        simp_all only [ne_eq, Nat.find_le_iff, and_self_left, true_and, not_false_eq_true,
          Nat.lt_find_iff, not_and, Decidable.not_not, le_refl, not_true_eq_false, implies_true,
          Nat.find_eq_zero, zero_le, nonpos_iff_eq_zero, and_false, tsub_lt_self_iff, zero_lt_one,
          and_self, tsub_le_iff_right, not_exists, Nat.succ_eq_add_one, Nat.le_find_iff,
          Nat.lt_one_iff, Nat.sub_add_cancel, le_add_iff_nonneg_right, P, k]
        exact Nat.gt_of_not_le hle

    -- 実際には k ≤ card α なので左枝は起きない
    cases hcase with
    | inl _  =>
      simp_all only [ne_eq, Nat.find_le_iff, and_self_left, true_and, not_false_eq_true,
        Nat.lt_find_iff, not_and, Decidable.not_not, le_refl, not_true_eq_false, implies_true,
        Nat.find_eq_zero, zero_le, nonpos_iff_eq_zero, and_false, tsub_lt_self_iff, zero_lt_one,
        and_self, tsub_le_iff_right, gt_iff_lt, false_or, P, k]
    | inr hE => exact hE

--使われている
omit [Fintype α] in
private lemma nextHead?_mem_and_min
  {α} [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {a : α}
  (h : nextHead? R I = some a) :
  a ∈ (applicable R I).image (fun t => t.head) ∧
  ∀ b ∈ (applicable R I).image (fun t => t.head), a ≤ b := by
  classical
  unfold nextHead? at h
  set heads := (applicable R I).image (fun t => t.head) with hH
  by_cases hne : heads.Nonempty
  · simp [hH] at h
    constructor
    · by_cases hne : heads.Nonempty
      case pos =>
        rcases h with ⟨happ, hmin⟩
        have hmem_min :
            (image (fun t => t.head)
                  ({t ∈ R | t.prem ⊆ I ∧ t.head ∉ I})).min'
              (Finset.image_nonempty.mpr happ)
              ∈ image (fun t => t.head)
                      ({t ∈ R | t.prem ⊆ I ∧ t.head ∉ I}) :=
          Finset.min'_mem _ _
        -- `a = min' …` を用いて書き換え（`applicable R I = R.filter …` を使うなら `[applicable]` に直しても可）
        have : a ∈ image (fun t => t.head) (applicable R I) := by
          simpa [applicable, hmin] using hmem_min
        -- 最後に `heads = image …` で `heads` 側へ戻す
        simpa [hH] using this

      case neg =>
        (expose_names; exact False.elim (hne hne_1))
    · intro b hb
      simp_all [heads]
      subst h
      obtain ⟨w, h⟩ := hb
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      subst right
      apply min'_le
      simp_all only [applicable, image_nonempty, mem_image, mem_filter, heads]
      use w

  · constructor
    · simp_all only [applicable, image_nonempty, Option.dite_none_right_eq_some, Option.some.injEq, not_nonempty_iff_eq_empty,
        filter_eq_empty_iff, not_and, Decidable.not_not, mem_image, mem_filter, isEmpty_Prop, not_true_eq_false,
        not_false_eq_true, implies_true, IsEmpty.exists_iff, heads]
    · intro b hb
      simp_all only [applicable, image_nonempty, Option.dite_none_right_eq_some, Option.some.injEq, not_nonempty_iff_eq_empty,
        filter_eq_empty_iff, not_and, Decidable.not_not, mem_image, mem_filter, isEmpty_Prop, not_true_eq_false,
        not_false_eq_true, implies_true, IsEmpty.exists_iff, heads]

--使われている。
lemma step2_superset
  {α} [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ step2 R I := by
  intro x hx
  cases h : nextHead? R I with
  | none   => simpa [step2, h] using hx
  | some a =>
      have : x ∈ insert a I := by exact mem_insert_of_mem hx
      simpa [step2, h] using this

def iter2
  {α} [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) : Nat → Finset α
  | 0     => I
  | k+1   => step2 R (iter2 R I k)

lemma iter2_le_of_le
  {α} [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α)
  {m n : ℕ} (hmn : m ≤ n) :
  iter2 R I m ⊆ iter2 R I n := by
  classical
  induction' hmn with n hmn ih
  · simp
  · intro x hx
    have hx' := ih hx
    simpa [iter2] using (step2_superset R (iter2 R I n) hx')

--使われてない。
private lemma step2_adds_minimal_head
  {α} [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {x : α}
  (hx : x ∈ step2 R I \ I) :
  x ∈ (applicable R I).image (fun t => t.head) ∧
  ∀ b ∈ (applicable R I).image (fun t => t.head), x ≤ b := by
  classical
  rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
  cases h : nextHead? R I with
  | none =>
      simp
      constructor
      · dsimp [nextHead?] at h
        simp at h
        rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
        -- step2 の場合分け
        cases hnh : nextHead? R I with
        | none =>
            -- none なら step2 = I なので矛盾
              have hI : x ∈ I := by
                simpa [step2, hnh] using hx_step
              -- 矛盾から任意の命題が従う
              exact False.elim (hx_notI hI)

        | some a =>
            -- x ∈ insert a I なので x = a か x ∈ I
            have hx_ins : x ∈ insert a I := by simpa [step2, hnh] using hx_step
            rcases Finset.mem_insert.mp hx_ins with hx_eq | hx_inI
            · -- x = a の場合：nextHead?_spec_some から規則 t を取る
              subst hx_eq
              rcases nextHead?_spec_some (R:=R) (I:=I) hnh with ⟨ha_notI, ⟨t, htR, htPrem, htHead⟩⟩
              refine ⟨t, ?_, ?_⟩
              · exact ⟨htR, htPrem, by simpa [htHead] using ha_notI⟩
              · -- 目標は t.head = x。今は x を a に置換済みなので t.head = a で十分
                simp [htHead]
            · -- x ∈ I は sdiff と矛盾
              exact (hx_notI hx_inI).elim

      · intro b hb hb2 hb3 hb4 hb5
        dsimp [nextHead?] at h
        simp at h
        subst hb5
        simp_all only [mem_sdiff, not_false_eq_true, and_self, not_true_eq_false]

  | some a =>
      have hx_ins : x ∈ insert a I := by simpa [step2, h] using hx_step
      rcases Finset.mem_insert.mp hx_ins with rfl | hxI
      · exact nextHead?_mem_and_min (R:=R) (I:=I)  h
      · exact (hx_notI hxI).elim

--使われていない。
private lemma noRuleWith_thead_in_erase
  {α} [DecidableEq α] {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R) :
  ∀ {r}, r ∈ R.erase t → r.head ≠ t.head := by
  classical
  intro r hr
  have hrR : r ∈ R := Finset.mem_of_mem_erase hr
  intro hEq
  have : r = t := hUC hrR ht hEq
  have : r ∉ R.erase t := by
    subst this
    simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true]
  exact this hr

--使われてない
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma step2_eq_iff_applicable_empty
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  step2 R I = I ↔ applicable R I = ∅ := by
  classical
  constructor
  · intro h
    cases hnh : nextHead? R I with
    | none   =>
      simp
      intro x hx hhx
      dsimp [nextHead?] at hnh
      simp at hnh
      simp_all only

    | some a =>
        -- some の場合は step2 = insert a I なので不動点は無理
        have hii: I = insert a I := by simpa [step2, hnh] using h.symm
        -- 矛盾から空を導く（好みで `nextHead?_spec_none` を使う形にしてOK）
        exact False.elim <| by
          have : a ∈ insert a I := by simp
          have : a ∈ I := by
            rw [←hii] at this
            exact this
          rcases nextHead?_spec_some (R:=R) (I:=I) (a:=a) hnh with ⟨haNot, _⟩
          exact haNot this
  · intro h
    -- applicable 空 ⇒ nextHead? = none ⇒ 据え置き
    have : nextHead? R I = none := by
      unfold nextHead?
      simp
      intro x a a_1
      simp_all only [applicable, filter_eq_empty_iff, not_and, Decidable.not_not]
    simp [step2, this]

--使われてない
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma ssubset_step2_of_applicable_nonempty
  [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α}
  (hne : (applicable R I).Nonempty) :
  I ⊂ step2 R I := by
  classical
  refine ⟨step2_superset R I, ?_⟩
  -- nextHead? = some a, その a は I に入っていないので真に増える
  obtain ⟨a, ha⟩ : ∃ a, nextHead? R I = some a := by
    -- heads 非空から some を取る（applicable 非空 ⇒ heads 非空）
    unfold nextHead?
    have : ((applicable R I).image (fun t => t.head)).Nonempty :=
      Finset.image_nonempty.mpr hne
    simp
    let S : Finset (Rule α) := {t ∈ R | t.prem ⊆ I ∧ t.head ∉ I}

    -- hne : (applicable R I).Nonempty から S.Nonempty を作る
    have happ : S.Nonempty := by
      rcases hne with ⟨r, hr⟩
      -- hr : r ∈ applicable R I
      -- applicable を展開
      change r ∈ R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I) at hr
      -- 目標は r ∈ S だが，S はちょうど同じ filter 記法
      refine ⟨r, ?_⟩
      change r ∈ R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I)
      exact hr

    -- 画像の非空性
    have himg : (image (fun t => t.head) S).Nonempty :=
      Finset.image_nonempty.mpr happ

    -- a を「その画像の min'」として取る
    refine ⟨(image (fun t => t.head) S).min' himg, ?_, ?_⟩
    · -- Nonempty の証人
      exact happ
    · -- min' の定義通り
      rfl

  rcases nextHead?_spec_some (R:=R) (I:=I) (a:=a) ha with ⟨ha_notI, -⟩
  intro hEq
  have : a ∈ I := by
    have : a ∈ step2 R I := by
      simp [step2, ha]
    exact hEq this


  exact ha_notI this

--使われてない
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma applicable_lift_of_head_notin
  [DecidableEq α]
  {R : Finset (Rule α)} {I J : Finset α}
  (hIJ : I ⊆ J) {t : Rule α}
  (ht : t ∈ applicable R I) (hnotJ : t.head ∉ J) :
  t ∈ applicable R J := by
  rcases Finset.mem_filter.mp ht with ⟨hR, ⟨hprem, _⟩⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨hR, ⟨?premJ, hnotJ⟩⟩
  intro x hx
  exact hIJ (hprem hx)

--使われてない
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma enter_at_iter2_exists_rule
  [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {x : α}
  (hx : x ∈ step2 R I \ I) :
  ∃ r ∈ R, r.prem ⊆ I ∧ r.head = x := by
  classical
  -- step2 で some a を入れて x=a、`nextHead?_spec_some` を使う
  rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
  cases h : nextHead? R I with
  | none =>
    have hI : x ∈ I := by

      -- step2 を展開（match を hnh で解消）
      simp [step2] at hx_step
      simp_all only [mem_sdiff, not_false_eq_true, and_true]
    exact False.elim (hx_notI hI)

  | some a =>
      have hx_ins : x ∈ insert a I := by simpa [step2, h] using hx_step
      rcases Finset.mem_insert.mp hx_ins with hx_eq | hx_inI
      · subst hx_eq
        rcases nextHead?_spec_some (R:=R) (I:=I) h with ⟨_, ⟨r, hrR, hrPrem, hrHead⟩⟩
        exact ⟨r, hrR, hrPrem, by exact hrHead⟩
      · exact (hx_notI hx_inI).elim

--コメントアウトしたものの中で使われている
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma frozen_forever_of_none
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) {S : Finset α}
  (h : nextHead? R S = none) :
  ∀ m, (Nat.iterate (step2 R) m) S = S := by
  intro m; induction m with
  | zero => rfl
  | succ m ih =>
      -- step2 S = S, かつ以降も S に留まる
      have : step2 R S = S := by simp [step2, h]
      simp [Nat.iterate, ih, this]

--コメントアウトしたものの中で、使われている
omit [DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma all_steps_increase_if_last_increases
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) (N : ℕ)
  (hneq : iter2 R I N ≠ iter2 R I (N+1)) :
  ∀ k ≤ N, iter2 R I k ≠ iter2 R I (k+1) := by
  classical
  intro k hk
  by_contra heq
  -- k 段で据え置きなら nextHead? = none
  have hnone : nextHead? R (iter2 R I k) = none := by
    -- `heq` を `step2` の定義に戻して評価すると `none` が出る
    -- （`some` なら insert で絶対に変わるため）
    cases hnh : nextHead? R (iter2 R I k) with
    | none   => rfl
    | some a =>
      simp
      set S := iter2 R I k

      -- (k+1)段は step2
      have hstep : iter2 R I (k+1) = step2 R S := by
        -- S = iter2 R I k を使って定義展開
        change iter2 R I (k+1) = step2 R (iter2 R I k)
        simp [iter2]

      -- heq：S = iter2 R I (k+1) なので、step2 R S = S が従う
      have hfix : step2 R S = S := by
        have : S = iter2 R I (k+1) := by
          -- S の定義で置換
          change iter2 R I k = iter2 R I (k+1) at heq
          exact heq
        -- S = (k+1)段 = step2 R S
        have : S = step2 R S := this.trans hstep
        exact this.symm

      -- nextHead? = some a なら step2 は insert a
      have hsomeS : nextHead? R S = some a := by
        -- S の定義で置換
        change nextHead? R (iter2 R I k) = some a at hnh
        exact hnh
      have hstep_some : step2 R S = insert a S := by
        simp [step2, hsomeS]

      -- 以上より insert a S = S
      have hins_eq : insert a S = S := by
        -- hfix : step2 R S = S と hstep_some を合成
        apply Eq.trans
        exact id (Eq.symm hstep_some)--hstep_some hfix
        exact hfix

      -- すると a ∈ S が出る（mem を等式で運ぶ）
      have ha_in_S : a ∈ S := by
        -- まず a ∈ insert a S
        have ha_ins : a ∈ insert a S := Finset.mem_insert_self a S
        -- (a ∈ insert a S) = (a ∈ S) に書き換え
        have hmem_eq : (a ∈ insert a S) = (a ∈ S) :=
          congrArg (fun s => a ∈ s) hins_eq
        exact Eq.mp hmem_eq ha_ins

      -- しかし spec_some から a ∉ S なので矛盾
      have ha_notin : a ∉ S := by
        rcases nextHead?_spec_some (R:=R) (I:=S) (a:=a) hsomeS with ⟨ha_not, _⟩
        exact ha_not
      exact ha_notin ha_in_S

  -- 据え置き以降は永遠に据え置き → 特に N+1 段も等しい
  set S := iter2 R I k with hS
  have step_S : step2 R S = S := by
    -- hnone から直ちに step2 R S = S
    have : nextHead? R S = none := by
      -- hnone を S に書き換え
      have : nextHead? R (iter2 R I k) = none := hnone
      simpa [hS] using this
    -- step2 の定義
    simp [step2, this]

  -- d による帰納で iter2 (k + d) = S
  have frozen_from_k : ∀ d : ℕ, iter2 R I (k + d) = S := by
    intro d
    induction' d with d ih
    · -- d = 0
      -- iter2 R I (k+0) = iter2 R I k = S
      exact hS.symm
    · -- d+1
      -- iter2 (k+d+1) = step2 R (iter2 (k+d)) = step2 R S = S
      have h1 : iter2 R I (k + d + 1) = step2 R (iter2 R I (k + d)) := by
        -- iter2 の定義（k+d+1 段は 1 ステップ）
        -- 注意: + の結合の整形が必要
        have : k + d + 1 = (k + d) + 1 := by exact rfl
        -- 上の等式で simp
        simp [iter2]
      calc
        iter2 R I (k + d + 1)
            = step2 R (iter2 R I (k + d)) := h1
        _   = step2 R S := by
                -- 直前の帰納仮定 ih : iter2 R I (k + d) = S
                -- これを使って書き換え
                -- `congrArg` で step2 の引数に等式を適用
                have := congrArg (fun s => step2 R s) ih
                exact this
        _   = S := step_S

  -- N = k + d に分解して、N と N+1 の両方が S に等しいことを示す
  rcases Nat.exists_eq_add_of_le hk with ⟨d, rfl⟩
  -- これで (k+d) 段と (k+d+1) 段の等号が出る
  have hN  : iter2 R I (k + d)     = S := frozen_from_k d
  have hN1 : iter2 R I (k + d + 1) = S := frozen_from_k (d+1)
  -- したがって等しい
  have hEqFinal :
      iter2 R I (k + d) = iter2 R I (k + d + 1) := by
    -- 2つの等式を合成
    apply hN.trans hN1.symm

  -- ところで N = k+d ≤ N なので、特に N= k+d。今の等式は N と N+1 の等式に他ならない。
  -- これは hneq に反する（N は仮定の N）
  -- 形式的には、k+d = N の置換は上で済んでいる（`rcases` で rfl を入れている）。
  exact hneq hEqFinal

end Twostem
/-
-- この補題の前提は矛盾している：
-- parIter R' U (k-1) = parIter R' V (k-1) なら、
-- parIter R' U k = stepPar R' (parIter R' U (k-1)) = stepPar R' (parIter R' V (k-1)) = parIter R' V k
-- となり hneq に矛盾する。
-- したがって前提が False を導くので、この補題は自明に成り立つ（ex falso quodlibet）。
lemma singleton_symmDiff_at_first_diverge
  [DecidableEq α] [Fintype α]
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α} {k : ℕ}
  (hk_pos : 0 < k)
  (hprev : parIter R' U (k-1) = parIter R' V (k-1))
  (hneq  : parIter R' U k ≠ parIter R' V k) :
  ∃ x, ((parIter R' U k \ parIter R' V k) ∪
        (parIter R' V k \ parIter R' U k)) = {x} := by
  -- 前提が矛盾していることを示す
  exfalso
  apply hneq
  -- parIter の定義を展開: parIter R' U k = parIter R' U ((k-1) + 1) = stepPar R' (parIter R' U (k-1))
  have hk_succ : k = Nat.succ (k - 1) := (Nat.succ_pred_eq_of_pos hk_pos).symm
  rw [hk_succ]
  simp only [parIter]
  -- hprev を使う
  rw [hprev]
-/

/-なりたたないとはいえないが、必要ない。
lemma syncCl_eq_of_two_witnesses_ARoute
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B S₁ S₂ : Finset α} {t : Rule α}
  (hUC  : UniqueChild (α:=α) R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)
  (hW₁  : isWitness ρ R B S₁ t)
  (hW₂  : isWitness ρ R B S₂ t) :
  syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂) := by
  classical
  -- 記号
  set R' := R.erase t
  set U  := B ∪ S₁
  set V  := B ∪ S₂

  -- 反証法：closure が異なると仮定
  by_contra hne
  -- hne : syncCl R' U ≠ syncCl R' V
  -- あとは hne を使って、あなたの後続ステップへ
  obtain ⟨k, hk_le, hneq_k, hprev⟩ :=
    exists_min_k_of_syncCl_ne (R' := R') (U := U) (V := V) hne

  revert hne; intro hne

  -- ここからが置き換えパッチ：closure差ではなく段k差からxを取る
  have hk_pos : 0 < k := by
    -- k>0 を仮定で用意しておくのが安全（k=0ケースは別に潰す）
    -- k=0でも同等の議論はできますが、以降の cause 補題を素直に使うため k>0 を推奨
    -- 既に k を「最初に食い違う正の段」として取る補題を使うとよいです
    -- （exists_min_pos_k_of_syncCl_ne のような補題）
    admit

  -- 「段kで違う」から、どちらかの差は非空
  have hdiff_nonempty :
      (parIter R' U k \ parIter R' V k).Nonempty ∨
      (parIter R' V k \ parIter R' U k).Nonempty := by
    by_contra hboth
    -- 両方空なら parIter R' U k = parIter R' V k に矛盾
    sorry

  -- 左枝に進む（右枝は対称）
  cases hdiff_nonempty with
  | inl hL =>
      rcases hL with ⟨x, hx_mem⟩
      have hx_split : x ∈ parIter R' U k ∧ x ∉ parIter R' V k :=
        Finset.mem_sdiff.mp hx_mem
      have hx_in_Uk  : x ∈ parIter R' U k := hx_split.1
      have hx_not_Vk : x ∉ parIter R' V k := hx_split.2

      -- 前段一致を明示
      have hprev_eq : parIter R' U (k-1) = parIter R' V (k-1) := by
        -- あなたの `exists_min_*` 補題が返した “hprev” が
        -- `k = 0 ∨ …` の形なら、k>0 を使って右枝に絞ってください
          simp at hx_mem
          obtain ⟨left, right⟩ := hx_mem
          cases hprev with
          | inl h =>
            subst h
            simp_all only [zero_le, lt_self_iff_false]
          | inr h_1 => simp_all only


      -- ★ ここがポイント：x は前段には入っていない
      have hx_not_prev : x ∉ parIter R' U (k-1) := by
        intro hx_prevU
        -- 前段一致で V 側にも入る
        have hx_prevV : x ∈ parIter R' V (k-1) := by
          -- 書き換え（`simpa` 禁止なので `rw` で）
          have := congrArg (fun S => x ∈ S) hprev_eq
          -- `this : (x ∈ parIter R' U (k-1)) = (x ∈ parIter R' V (k-1))`
          exact (Eq.mp this) hx_prevU
        -- 単調性で段kにも上がってくる
        have hmonoV : parIter R' V (k-1) ⊆ parIter R' V k := by
          sorry
          --parIter_mono_in_steps (R:=R') (I:=V) (k:=k-1)
        have hx_in_Vk : x ∈ parIter R' V k := hmonoV hx_prevV
        exact hx_not_Vk hx_in_Vk

      -- U ⊆ parIter R' U (k-1)（k>0）より x∉U が従う
      have hU_sub_prev : U ⊆ parIter R' U (k-1) := by
        -- 0 ≤ k-1
        have : 0 ≤ k-1 := Nat.succ_le_of_lt hk_pos |> Nat.pred_le_pred
        exact parIter_increasing (R:=R') (I:=U) 0 (k-1) (Nat.zero_le _)
      have hx_not_init : x ∉ U := fun hxU => hx_not_prev (hU_sub_prev hxU)

      -- （この後は原因規則抽出 → Aルートで x = t.head → head 不到達で矛盾）
      -- 例：前段等式を step に上げて cause を取る
      have hstep : stepPar R' (parIter R' U (k-1)) = stepPar R' (parIter R' V (k-1)) :=
        congrArg (stepPar R') hprev_eq
      -- `cause_exists_on_right_of_step_eq` を適用（あなたの補題名のままでOK）
      have hx_cause :=
        cause_exists_on_right_of_step_eq (R:=R') (X:=parIter R' U (k-1)) (Y:=parIter R' V (k-1))
          (hstep := hstep) (f := x)
          -- x ∈ (parIter U k) \ (parIter V k) を “k-1段の step での差” に書き換える
          (by
            -- parIter の定義：parIter … (k) = stepPar R' (parIter … (k-1))
            -- を展開して `hx_mem` を移送します（`simp [parIter]` なしで書くなら
            -- `change` と等式展開で）
            sorry)
      rcases hx_cause with ⟨r, hrR, hprem, rhead⟩

      -- Aルート：最初の差分は t.head
      have hx_eq_head : x = t.head := by
        -- REPLACE: OnlyTLastDiff 系の既存補題名に置換（例：`head_eq_left_sdiff`）
        sorry

      -- head 不到達（witness → erase t の閉包に head は入らない）
      -- REPLACE: t∈R を isWitness から取り出す補題名に置換
      have ht : t ∈ R := by sorry
      have hnot : t.head ∉ syncCl (R.erase t) U := by
        sorry
        --head_not_in_syncCl_of_erase_witness
        --  (ρ := ρ) (R := R) (B := B) (S := S₁) (t := t)
        --  (hUC := hUC) (ht := ht) (hW := hW₁)

      -- x∈parIter U k ⊆ syncCl R' U かつ x=t.head で矛盾
      have hx_in_Ucl : x ∈ syncCl R' U :=
        (parIter_subset_syncCl (R:=R') (I:=U) k) hx_in_Uk
      cases hx_eq_head
      exact hnot hx_in_Ucl

  | inr hR =>
      -- 右枝は対称（U↔V, S₁↔S₂ を入れ替え）
      admit
-/


/-
--noncomputable instance decidable_IsClosed {α : Type _} {R : Finset (Rule α)} : DecidablePred (IsClosed R) :=
--fun I => Classical.dec (IsClosed R I)
noncomputable instance : DecidablePred (fun S : Finset α => isWitness ρ R B S t) :=
  fun S => Classical.dec (isWitness ρ R B S t)

lemma card_witness_le_one_from_unique
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hUC  : UniqueChild (α:=α) R)
  (t : Rule α)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)
  (uniq : ∀ {B S₁ S₂ t},
      Disjoint B S₁ → Disjoint B S₂ →
      isWitness ρ R B S₁ t → isWitness ρ R B S₂ t →
      syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂) →
      S₁ = S₂)
  (B : Finset α)  :
  (Fintype.card {S : Finset α // isWitness ρ R B S t}) ≤ 1 := by
  have hSub : Subsingleton {S : Finset α // isWitness ρ R B S t} := by
    refine ⟨?_⟩; intro x y
    rcases x with ⟨S₁, hW₁⟩; rcases y with ⟨S₂, hW₂⟩
    have hD₁ := isWitness_disjoint ρ R B S₁ t hW₁
    have hD₂ := isWitness_disjoint ρ R B S₂ t hW₂
    -- （必要なら）ここで hEq を用意する補題を呼ぶ：
    --   syncCl_eq_of_two_witnesses ρ (R:=R) (B:=B) (t:=t) hW₁ hW₂
    -- すでに hEq を外から受け取る設計なら uniq に渡すだけ
    have : S₁ = S₂ := by
      apply uniq hD₁ hD₂ hW₁ hW₂
      apply syncCl_eq_of_two_witnesses_ARoute ρ R hUC hNTF hNS hA
      exact hW₁
      exact hW₂

    cases this; rfl
  exact Fintype.card_le_one_iff_subsingleton.mpr hSub
-/


/-
  apply Fintype.card_le_one_iff.mpr (by
    intro x y; cases x; cases y; simp)
  classical
  -- 「witness 全体の集合」の要素は S（と証明）なので、2 つあれば uniq で等しい
  -- 2点からの単点化 → card ≤ 1

  refine Fintype.card_le_one_iff.mpr ?uniq_subtype
  intro x y
  -- x y : {S // isWitness …}, それぞれの underlying と証明を展開
  rcases x with ⟨S₁, hW1⟩
  rcases y with ⟨S₂, hW2⟩
  -- B と S の disjoint は witness 側に既に含めているならそこから、別仮定なら引数で。
  -- ここでは witness が disjoint を内包しない前提でも動くよう、引数の uniq は
  -- disjoint を要求している形のまま残します。あなたの環境に合わせて代入してください。
  -- もし disjoint が witness に含まれるなら、その場で取り出して uniq に渡してください。
  have hD1 : Disjoint B S₁ := (isWitness.disjoint_left hW1)
  have hD2 : Disjoint B S₂ := (isWitness.disjoint_left hW2)
  -- 同期閉包が等しいことは witness から通常得られます（あなたの isWitness API 次第）。
  -- もし `isWitness` がそのまま syncCl 等式を含んでいないなら、あなたが既に使っている
  -- 「witness → addedFamily → syncCl で一致」系の補題をここで挟んで下さい。
  have hSync : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂) :=
    (isWitness.sync_eq_of_same_BT hW1 hW2)  -- ←環境の補題名に合わせて差し替え
  -- ユニーク性仮定から S₁ = S₂
  have : S₁ = S₂ := uniq hD1 hD2 hW1 hW2 hSync
  -- サブタイプの等式へ
  cases this
  rfl
-/
/-古い試み
-- Witness の一意性から閉集合のサイズが全体の半分以下であることを示す補題
-- これは UC (UniqueChild) + TwoStem の性質から導かれるべき深い定理
--
-- 【警告】この補題は現在の形では成り立たない可能性が高い。
-- 反例: α = {1, 2, 3}, R = ∅
--   - I = {1, 2, 3} (全体集合) は閉集合
--   - uniq は空虚に真（isWitness が存在しないため）
--   - しかし 3 ≤ 3/2 = 1 は False
--
-- 成り立つための追加条件候補:
--   - I ≠ univ (I は真部分集合)
--   - R ≠ ∅ かつ R に意味のある構造がある
--   - ∃ t B S, isWitness ρ R B S t (非自明な Witness が存在)
--   - UC (UniqueChild) 性質の明示的な仮定
lemma closed_card_le_half_of_unique_witness
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {I : Finset α}
  (hClosed : IsClosed R I)
  (uniq : ∀ {B S₁ S₂ t},
      Disjoint B S₁ → Disjoint B S₂ →
      isWitness ρ R B S₁ t → isWitness ρ R B S₂ t →
      syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂) →
      S₁ = S₂) :
  (I.card : ℤ) ≤ (Fintype.card α : ℤ) / 2 := by
  -- この証明は以下の理論的な議論を必要とする：
  -- 1. UC (UniqueChild) 性質: 各要素に対して高々1つのルールしかheadとして持たない
  -- 2. Witness の一意性: 同じ B, t に対する Witness S が一意
  -- 3. 閉集合族の対称性/balanced性: I が閉集合なら、その補集合も「ほぼ閉」
  -- 4. Frankl 型の上界定理: このような制約下では |I| ≤ |α|/2
  --
  -- これは組合せ論的な議論を要し、本ファイルの範囲を超える。
  -- さらに、上記の反例が示すように、現在の前提では不十分である。
  sorry

-- 【警告】成り立たなさそう。
-- 反例: α = {1, 2, 3}, R = ∅
--   - Family R = すべての部分集合（空集合からルールがないのですべてが閉集合）
--   - NDS R = Σ_{I ⊆ α} (2|I| - |α|)
--   - I = α = {1,2,3} の項: 2×3 - 3 = 3 > 0
--   - よって NDS R > 0
--
-- この補題が成り立つには、R に非自明な構造（ルールの存在、UC性質など）が必要。
lemma NDS_le_zero_of_unique_S
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (uniq : ∀ {B S₁ S₂ t},
      Disjoint B S₁ → Disjoint B S₂ →
      isWitness ρ R B S₁ t → isWitness ρ R B S₂ t →
      syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂) →
      S₁ = S₂)
  [DecidablePred (fun I => IsClosed R I)] :
  NDS R ≤ 0 := by
  classical
  unfold NDS
  -- NDS(R) = ∑_{I ∈ Family R} (2|I| - |α|)
  -- 各 I に対して 2|I| - |α| ≤ 0 を示せば、総和も ≤ 0 になる
  have hTerm_le : ∀ I ∈ Family R, (2 * (I.card : ℤ) - (Fintype.card α : ℤ)) ≤ 0 := by
    intro I hI
    -- 各 I は閉集合（IsClosed R I）
    have hClosed : IsClosed R I := by exact mem_Family.mp hI
    -- 補助補題を使用
    have hHalf : (I.card : ℤ) ≤ (Fintype.card α : ℤ) / 2 :=
      closed_card_le_half_of_unique_witness ρ hClosed uniq
    -- 2 * (I.card : ℤ) ≤ 2 * ((Fintype.card α : ℤ) / 2) ≤ Fintype.card α
    -- したがって 2 * (I.card : ℤ) - (Fintype.card α : ℤ) ≤ 0
    omega
  -- 各項が ≤0 なので、総和も ≤0
  apply Finset.sum_nonpos
  intro I hI
  exact hTerm_le I hI
-/


/-後ろに移動。
-- 前提： result_right_impossible, result_left_impossible,
--        exists_k_singleton_symmDiff_of_syncEq, disjoint_union_eq_implies_right_eq などは既証明
--あとで、言明や証明をdiff版に置き換え。OnlyTLastDiff ρ R t
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂
  -- U=V なら disjoint から S₁=S₂
  have finish_eq : U = V → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- UC を erase 側へ
  have hUC' : UniqueChild (α:=α) (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhd
    exact hUC (Finset.mem_of_mem_erase hr₁) (Finset.mem_of_mem_erase hr₂) hhd

  -- 等閉包から：U=V か、∃ k f. (k+1段一致 ∧ 最小差が単点)
  cases exists_k_singleton_symmDiff_of_syncEq (R:=R.erase t) hNTF hNS (U:=U) (V:=V) hEq with
  | inl hUV =>
      exact finish_eq hUV
  | inr hK =>
    rcases hK with ⟨k, f, hk, hEqNext, hSingle⟩
    set X := parIter (R.erase t) U k
    set Y := parIter (R.erase t) V k
    -- (k+1) 段一致を step の形に
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) U k)
          = stepPar (R.erase t) (parIter (R.erase t) V k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差が単点 → どちらかの差が空
    have hXYempty_or_YXempty :
      X \ Y = ∅ ∨ Y \ X = ∅ := by
      -- {f} は片側にしか現れない：NoSwap からの「一方の差が空」補題を使う/導出する
      -- 既存のあなたの系（NoSwap：step同値→左右どちらかの差が空）を使ってください
      -- 例: from hNS and hStep
      exact (hNS X Y hStep)

    -- 2分岐の各々で「不可能」を出す（すでに作った補題を使う）
    cases hXYempty_or_YXempty with
    | inl hXYempty =>
      -- 右枝（X\Y=∅ & 原因一意）での矛盾
      -- 「原因一意」は hSingle と NoTwoFreshHeads & UC' から既に引ける設計で準備している想定。
      -- ここでは、既存の result_right_impossible にそのまま渡す。
      have : False :=
        result_right_impossible
          (ρ:=ρ) (R:=R) (t:=t)
          (hUC:=(UniqueChild_iff_UC R).mp hUC) (ht:=ht)
          (B:=B) (S₁:=S₁) (hW1:=hW1)
          (k:=k) (f:=f)
          (U:=U) (V:=V) (hU:=rfl)
          (hEqNext:=hEqNext)
          (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
          (hXYempty:=by simpa [X,Y] using hXYempty)
          -- 「∃! r …」は、あなたの “一意原因” 補題から hSingle・hStep・hUC' を使って供給
          --(hExu:= sorry)
          --             cause_unique_on_right_of_step_eq (R:=R.erase t) (hUC:=hUC') (hstep:=hStep)
                -- 右側単点化から f∈Y\X を作る
                --(mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f)
                  (by
                    -- X\Y=∅ と対称差単点 hSingle から Y\X={f}
                    -- ここは既にあなたの補題群で出せる形
                    admit
                  )
          (hf_head:=by
            -- result_right_impossible が要求する “f = t.head”
            -- これは head_eq_thead_on_right_branch で供給
            exact head_eq_thead_on_right_branch
              ρ R t ((UniqueChild_iff_UC R).mp hUC) ht
              (B:=B) (S₁:=S₁) (hW1:=hW1)
              (k:=k) (U:=U) (V:=V) (hU:=rfl)
              (hEqNext:=hEqNext) (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
              (hXYempty:=by simpa [X,Y] using hXYempty)
              (hExu:=by
                -- 上と同様に “∃! r …” を供給
                admit))
          (hkBound:=hk)
      exact (this.elim)
    | inr hYXempty =>
      -- 左枝（Y\X=∅ & 原因一意）での矛盾
      have : False :=
        result_left_impossible
          (ρ:=ρ) (R:=R) (t:=t)
          (hUC:=(UniqueChild_iff_UC R).mp hUC)
          (B:=B) (S₁:=S₁) (hW1:=hW1)
          (k:=k) (f:=f)
          (U:=U) (V:=V) (hU:=rfl)
          (hEqNext:=hEqNext)
          (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
          (hYXempty:=by simpa [X,Y] using hYXempty)
          (hExuY:=by
            -- “∃! r …” 左枝版を供給
            admit)
          (hf_head:=by
            -- 左枝版の f=t.head も、左右対称の head_eq_thead_on_left_branch で供給
            exact head_eq_thead_on_left_branch
              ρ R t ((UniqueChild_iff_UC R).mp hUC) ht
              (B:=B) (S₁:=S₁) (hW1:=hW1)
              (k:=k) (U:=U) (V:=V) (hU:=rfl)
              (hEqNext:=hEqNext) (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
              (hYXempty:=by simpa [X,Y] using hYXempty)
              (hExuY:=by admit))
          (hkBound:=hk)
      exact (this.elim)
-/

/-
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂
  have finish_eq : U = V → S₁ = S₂ :=
    fun hUV => disjoint_union_eq_implies_right_eq hD1 hD2 hUV

  -- erase側 UC
  have hUC' : UniqueChild α (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhead
    exact hUC (Finset.mem_of_mem_erase hr₁) (Finset.mem_of_mem_erase hr₂) hhead

  -- 同期閉包等式から「等しい or 最小段の一意原因」へ
  have hCause :=
    lastDiff_unique_cause_of_syncEq_unique
      (R' := R.erase t) hNTF hNS (hUC' := hUC')
      (U := U) (V := V) (hSync := hEq)

  -- 分岐処理
  rcases hCause with hUV | ⟨k, f, hkBound, hEqNext, hUniq⟩
  · exact finish_eq hUV
  ·
    -- k段の状態
    set X : Finset α := parIter (R.erase t) U k
    set Y : Finset α := parIter (R.erase t) V k
    have hX : X = parIter (R.erase t) U k := rfl
    have hY : Y = parIter (R.erase t) V k := rfl

    -- (k+1) 段一致の形に直す
    have hEqNext' :
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) := hEqNext

    -- 右枝 or 左枝
    cases hUniq with
    | inl hR =>
        -- 右枝データ
        have hXYempty : X \ Y = ∅ := hR.left
        have hExu : ∃! r, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f := hR.right
        -- まず f = t.head を右枝用補題で取得
        have hf_head : f = t.head := by
          exact head_eq_thead_on_right_branch
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (B:=B) (S₁:=S₁) (hW1:=hW1)
            (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hXYempty:=hXYempty) (hExu:=hExu)

        -- 右枝は不可能（矛盾）→ U=V の枝のみ残る
        exact (False.elim <|
          result_right_impossible
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (hW1:=hW1) (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hXYempty:=hXYempty) (hExu:=hExu)
            (hf_head:=hf_head) (hkBound:=hkBound))

    | inr hL =>
        -- 左枝データ
        have hYXempty : Y \ X = ∅ := hL.left
        have hExuY : ∃! r, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f := hL.right
        -- 左枝でも f = t.head
        have hf_head : f = t.head :=
          head_eq_thead_on_left_branch
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (B:=B) (S₁:=S₁) (hW1:=hW1)
            (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY) (hYXempty:=hYXempty) (hExuY:=hExuY)

        -- 左枝も不可能（矛盾）
        exact (False.elim <|
          result_left_impossible
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (hW1:=hW1) (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hYXempty:=hYXempty) (hExuY:=hExuY)
            (hf_head:=hf_head) (hkBound:=hkBound))

-/

/-
/-- **最終定理（(A) 仮定つき完成版）**：
Witness が 2 組 `(B,S₁,t)` と `(B,S₂,t)` を与え，
`R.erase t` の閉包が一致すれば `S₁ = S₂`。 -/
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 等閉包から分岐パッケージ
  have hpack :=
    eq_or_unique_cause_for_erased (R:=R) (t:=t) hNTF hNS (B:=B) (S₁:=S₁) (S₂:=S₂) hEq
  cases hpack with
  | inl hUV =>
      exact disjoint_union_eq_implies_right_eq (B:=B) (S₁:=S₁) (S₂:=S₂) hD1 hD2 hUV
  | inr hK =>
      rcases hK with ⟨k, f, r, hkBound, hEqNext, hside⟩
      -- t.head は両閉包に出現しない
      have hnot1 : t.head ∉ syncCl (R.erase t) (B ∪ S₁) :=
        head_not_in_syncCl_of_erase_witness (R:=R) (ρ:=ρ) (B:=B) (S:=S₁) (t:=t) hUC ht hW1
      have hnot2 : t.head ∉ syncCl (R.erase t) (B ∪ S₂) :=
        head_not_in_syncCl_of_erase_witness (R:=R) (ρ:=ρ) (B:=B) (S:=S₂) (t:=t) hUC ht hW2
      -- 記号短縮
      set X := parIter (R.erase t) (B ∪ S₁) k
      set Y := parIter (R.erase t) (B ∪ S₂) k
      -- 片側単元差 → 対称差の合併は {f}
      have hUnionSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        cases hside with
        | inl hRight =>
            rcases hRight with ⟨hXemp, hYone, _, _, _⟩

            simp [X, Y, hXemp, hYone]

        | inr hLeft  =>
            rcases hLeft with ⟨hYemp, hXone, _, _, _⟩
            simp [X, Y, hYemp, hXone, union_comm]
      -- (A) により f = t.head
      have hf_head : f = t.head :=
        hA (B:=B) (S₁:=S₁) (S₂:=S₂) (k:=k) (f:=f) hW1 hW2 hEqNext (by simpa [X, Y] using hUnionSingle)
      -- k+1 段で一致しているので、差があった側の k+1 に f は入っている
      have hle_k1_N : k+1 ≤ Fintype.card α := hkBound
      cases hside with
      | inl hRight =>
          -- 右差分のみ：Y\X={f}
          rcases hRight with ⟨hXemp, hYone, _, _, _⟩
          -- f ∈ Y
          have hfY : f ∈ Y := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have : f ∈ Y \ X := by simp [hYone]
            exact (mem_sdiff.mp this).1
          -- f ∈ (k+1) 段（右側）
          have hf_in_k1 : f ∈ parIter (R.erase t) (B ∪ S₂) (k+1) := by
            have : f ∈ stepPar (R.erase t) Y := mem_union.mpr (Or.inl hfY)
            simpa [Y] using this
          -- (k+1) ≤ N から syncCl へ
          have hf_in_sync₂ : f ∈ syncCl (R.erase t) (B ∪ S₂) := by
            have hmono := parIter_le_of_le (R.erase t) (B ∪ S₂) hle_k1_N
            exact hmono hf_in_k1
          -- f = t.head と矛盾
          rename_i right
          subst right
          simp_all only [not_false_eq_true, sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      | inr hLeft  =>
          -- 左差分のみ：X\Y={f}
          rcases hLeft with ⟨hYemp, hXone, _, _, _⟩
          -- f ∈ X
          have hfX : f ∈ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have : f ∈ X \ Y := by simp [hXone]
            exact (mem_sdiff.mp this).1
          -- f ∈ (k+1) 段（左側）
          have hf_in_k1 : f ∈ parIter (R.erase t) (B ∪ S₁) (k+1) := by
            have : f ∈ stepPar (R.erase t) X := mem_union.mpr (Or.inl hfX)
            simpa [X] using this
          -- syncCl へ
          have hf_in_sync₁ : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
            have hmono := parIter_le_of_le (R.erase t) (B ∪ S₁) hle_k1_N
            exact hmono hf_in_k1
          -- f = t.head と矛盾
          let hn := (hnot1 (by simpa [hf_head] using hf_in_sync₁))
          exact False.elim hn

-/


/-古いバージョン。けしてよい
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)     -- ★ ここを復活
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ :=
by
  classical
  -- 記号
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂

  -- U=V → S₁=S₂
  have finish_eq : U = V → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- (補助) UC を erase 側へ
  have hUC' : UniqueChild (α:=α) (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhd
    have hr₁R : r₁ ∈ R := (Finset.mem_erase.mp hr₁).2
    have hr₂R : r₂ ∈ R := (Finset.mem_erase.mp hr₂).2
    exact hUC hr₁R hr₂R hhd

  -- 「OnlyTLastDiff から右枝/左枝で f = t.head」を返す小補題を作る
  -- （あなたの OnlyTLastDiff の定義にそのまま一致するはず）

  have head_eq_right_from_A :
    ∀ {k f},
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) →
      parIter (R.erase t) U k \ parIter (R.erase t) V k = ∅ →
      (∃! r : Rule α,
        r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) U k ∧ r.head = f) →
      f = t.head :=
  by
    -- ★ ここは hA をそのまま適用するだけ（定義に依存）。
    --   もし hA が「この状況の時 f=t.head」をちょうど返す形なら `exact hA ...`。
    --   そうでなければ、あなたの環境の hA のインターフェースに合わせて束縛を並べ替えてください。
    intro k f hEqNext hXYempty hExu
    sorry
    --exact hA.right_branch  -- ← あなたの定義に合わせて差し替え

  have head_eq_left_from_A :
    ∀ {k f},
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) →
      parIter (R.erase t) V k \ parIter (R.erase t) U k = ∅ →
      (∃! r : Rule α,
        r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) V k ∧ r.head = f) →
      f = t.head :=
  by
    intro k f hEqNext hYXempty hExuY
    sorry
    --exact hA.left_branch   -- ← あなたの定義に合わせて差し替え

  -- 等閉包の等式 ⇒ 「U=V」or「最小段 k と単点 f」
  obtain hUV | ⟨k, f, hk, hEqNext, hSingle⟩ :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R' := R.erase t) hNTF hNS (U := U) (V := V) (hSync := hEq)
  · exact finish_eq hUV
  ·
    -- X,Y, step 同一
    set X : Finset α := parIter (R.erase t) U k
    set Y : Finset α := parIter (R.erase t) V k
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) U k)
           = stepPar (R.erase t) (parIter (R.erase t) V k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差 = {f} の3分岐
    have hcases :=
      sdiff_union_singleton_cases (X := X) (Y := Y) (f := f)
        (by
          -- (X\Y) ∪ (Y\X) = {f}
          -- hSingle はまさにこれ（X,Y の定義を戻すだけ）
          -- rw/simp を避けたいなら、定義等式を展開せず `simpa [X, Y]` 相当で渡せます
          -- ここでは membership 等式にならないので `have := hSingle; exact this`
          simp [X, Y]
          exact hSingle
        )


    -- 場合分け
    cases hcases with
    | inl hRight =>
      -- 右枝：X\Y=∅, Y\X={f}
      rcases hRight with ⟨hXYempty, hYsingle⟩

      -- f ∈ Y\X
      have hfY : f ∈ Y ∧ f ∉ X := by
        let man := mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f)
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, not_false_eq_true, and_self, U,
          V, X, Y]

      -- 原因一意 (右枝側は「左の差分が空」→ cause_unique_on_left_of_step_eq を使う形)
      have hExu :
        ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f :=
        cause_unique_on_left_of_step_eq
          (R := R.erase t) (hUC := hUC') (hstep := hStep)
          (hg := by
            -- f ∈ Y \ X
            exact Finset.mem_sdiff.mpr ⟨hfY.left, hfY.right⟩)

      let hXYempty : X \ Y = ∅ := by
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      -- OnlyTLastDiff から f = t.head
      have hf_head : f = t.head :=
        head_eq_right_from_A (k:=k) (f:=f) hEqNext hXYempty hExu

      -- 右枝は不可能
      have contra :
        False :=
          result_right_impossible ρ R t
            ((UniqueChild_iff_UC R).mp hUC) ht
            (B := B) (S₁ := S₁) hW1
            (k := k) (f := f)
            (U := U) (V := V) rfl
            (hEqNext := hEqNext)
            (X := X) (Y := Y) rfl rfl
            (hXYempty := hXYempty) (hExu := hExu)
            (hf_head := hf_head) (hkBound := hk)
      exact contra.elim

    | inr rest =>
      cases rest with
      | inl hLeft =>
        -- 左枝：X\Y={f}, Y\X=∅
        rcases hLeft with ⟨hXsingle, hYXempty⟩

        -- f ∈ X\Y
        have hfX : f ∈ X ∧ f ∉ Y := by
          let man := mem_and_not_mem_of_sdiff_singleton_right (X:=Y) (Y:=X) (f:=f)
          apply man
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, U, V, X, Y]


        -- 原因一意（左枝側は「右の差分が空」→ cause_unique_on_right_of_step_eq）
        have hExuY :
          ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f :=
          cause_unique_on_right_of_step_eq
            (R := R.erase t) (hUC := hUC') (hstep := hStep)
            (hf := by
              -- f ∈ X \ Y
              exact Finset.mem_sdiff.mpr ⟨hfX.left, hfX.right⟩)

        let hYXempty : Y \ X = ∅ := by
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

        -- OnlyTLastDiff から f = t.head
        have hf_head : f = t.head :=
          head_eq_left_from_A (k:=k) (f:=f) hEqNext hYXempty hExuY

        -- 左枝は不可能
        have contra :
          False :=
            result_left_impossible ρ R t
              ((UniqueChild_iff_UC R).mp hUC)
              (B := B) (S₁ := S₁) hW1
              (k := k) (f := f)
              (U := U) (V := V) rfl
              (hEqNext := hEqNext)
              (X := X) (Y := Y) rfl rfl
              (hYXempty := hYXempty) (hExuY := hExuY)
              (hf_head := hf_head) (hkBound := hk)
        exact contra.elim

      | inr hdup =>
        -- 両側 {f} は NoSwap と step 同一に反する
        have hEmpty : X \ Y = ∅ ∨ Y \ X = ∅ := hNS X Y hStep

        -- ところが今は X\Y = {f} かつ Y\X = {f} なので、どちらの枝でも矛盾
        have : False := by
          cases hEmpty with
          | inl hxy =>
              -- f ∈ X\Y （単点 {f} だから）だが、X\Y = ∅ なので矛盾
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                -- X\Y = {f}
                exact by simp [hdup.left]
              have : f ∈ (∅ : Finset α) := by
                simp [hxy]
                apply Finset.notMem_empty f
                simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, U, V, X, Y]
              exact Finset.notMem_empty f this
          | inr hyx =>
              -- f ∈ Y\X だが、Y\X = ∅ なので矛盾
              have hfYX : f ∈ Y \ X := by
                have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                -- Y\X = {f}
                exact by
                  simp [hdup.right]
              have : f ∈ (∅ : Finset α) := by
                simp
                simp_all [U, V, X, Y]
                have hne : ({f} : Finset α) ≠ ∅ := by
                  -- 例えば「f は {f} に属するが、空集合には属さない」から示す
                  intro hE
                  have hf : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  have : f ∈ (∅ : Finset α) := by
                    simp [hE]
                    simp_all only [sdiff_eq_empty_iff_subset, and_true, singleton_ne_empty]
                  exact Finset.notMem_empty f this

                -- ところが hdup.right は ∅ = {f} を主張しているので矛盾
                exact hne (hdup.right.symm)

              exact Finset.notMem_empty f this

        -- 矛盾からは何でも従うので、S₁ = S₂ を得る
        exact this.elim
-/

/-必要か不明なので、コメントアウト
lemma iter2_stabilizes_at_card
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  iter2 R I (Fintype.card α) = iter2 R I (Fintype.card α + 1) := by
  classical
  -- 反証法：動くなら 1 段でサイズが 1 増える。|α| 回までしか増えないので矛盾
  by_contra hneq
  set N := Fintype.card α with hN

  -- まず、N 段目で nextHead? が none なら、その時点で凍結 ⇒ 矛盾
  cases hnh : nextHead? R (iter2 R I N) with
  | none =>
      -- あなたが証明済みの補題（例）:
      -- frozen_forever_of_none :
      --   nextHead? R (iter2 R I k) = none → iter2 R I k = iter2 R I (k+1)
      have hfreeze := frozen_forever_of_none (R:=R)   (h:=hnh)
      apply hneq
      have hstep_fixed : step2 R (iter2 R I N) = iter2 R I N := by
        -- f^[1] x = f x を使って簡約
        exact hfreeze 1

      -- 定義より iter2 の (N+1) 段は step2 を 1 回適用したもの
      have hfix : iter2 R I (N + 1) = iter2 R I N := by
        simpa [iter2] using hstep_fixed

      -- 目標は左右逆なので対称にして終了
      exact hfix.symm

  | some a =>
      -- 「最後の一歩が変化するなら、その前の全ステップも変化する」
      -- all_steps_increase_if_last_increases :
      --   iter2 R I N ≠ iter2 R I (N+1) → ∀ k ≤ N, iter2 R I k ≠ iter2 R I (k+1)
      have hall := all_steps_increase_if_last_increases (R:=R) (I:=I) (N:=N) hneq

      -- 各段で「（k → k+1）は包含」：step2_superset を使う
      -- step2_superset :
      --   ∀ k, iter2 R I k ⊆ iter2 R I (k+1)
      have hmono : ∀ k, iter2 R I k ⊆ iter2 R I (k+1) := by
        intro k
        let ss := step2_superset (R:=R) (I:=I)
        have step2_superset_any : ∀ J : Finset α, J ⊆ step2 R J := by
          intro J x hx
          cases h : nextHead? R J with
          | none =>
              -- step2 R J = J
              simpa [step2, h] using hx
          | some a =>
              -- step2 R J = insert a J
              simp_all only [le_refl, not_false_eq_true, ne_eq, N]
              rw [step2, h]
              simp_all only [mem_insert, or_true]

        -- 目標：iter2 R I k ⊆ iter2 R I (k+1)
        intro x hx
        have hx' : x ∈ step2 R (iter2 R I k) := by
          exact step2_superset_any (iter2 R I k) hx
        simpa [iter2] using hx'


      -- すると、0..N の各ステップで「厳密に増える」：card が毎回少なくとも +1
      -- これを合算して、(N+1) 段目の card ≥ (0 段目の card) + (N+1) ≥ N+1
      -- 一方、全て α の部分集合だから card ≤ |α| = N。矛盾。
      have hstrict_each :
        ∀ k ≤ N, (iter2 R I k).card < (iter2 R I (k+1)).card := by
        intro k hk
        -- 包含 & 不等号 ⇒ 真部分集合 ⇒ card は厳に増加
        have hsubset : iter2 R I k ⊆ iter2 R I (k+1) := hmono k
        have hne     : iter2 R I k ≠ iter2 R I (k+1) := hall k hk
        have hss     : iter2 R I k ⊂ iter2 R I (k+1) := by
          constructor
          · exact hmono k
          · intro h
            apply hne
            exact Subset.antisymm (hmono k) h

        exact Finset.card_lt_card hss

      -- これで「0..N の N+1 回の遷移」で毎回 card が 1 以上増える。
      -- 帰納でまとめる：
      have hsum :
        (iter2 R I (N+1)).card ≥ (iter2 R I 0).card + (N+1) := by
        -- 簡単な帰納（長くなるのでコンパクトに書きます）
        -- base: k=0 は (iter2 1).card ≥ (iter2 0).card + 1
        -- step: k → k+1 で一回分足す
        -- ここでは `Nat.le_of_lt` と加法単調性で積み上げ
        -- （詳しく書く場合は Nat.rec で k を 0..N まで回して積上げます）
        -- 手短版：
        have : ∀ k ≤ N, (iter2 R I (k+1)).card ≥ (iter2 R I 0).card + (k+1) := by
          intro k hk
          induction' k with k ih
          · -- k=0
            have hlt := hstrict_each 0 (Nat.zero_le _)
            have hle := Nat.le_of_lt hlt
            simp
            exact hstrict_each 0 hk
          · -- k+1
            have hkle : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
            have ih' := ih hkle
            sorry
            /-
            --have hlt := hstrict_each (k+1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
            have hle := Nat.le_of_lt hlt
            -- (k+2) 段の card ≥ (k+1) 段の card + 1 ≥ (iter2 0).card + (k+1) + 1
            calc
              (iter2 R I (k+2)).card
                ≥ (iter2 R I (k+1)).card + 1 := by
                      -- (k+1 → k+2) で 1 増
                      -- hstrict_each gives strict <, なので ≥ +1 は自明（Nat なので）
                      have : (iter2 R I (k+1)).card < (iter2 R I (k+2)).card := hstrict_each (k+1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
                      exact Nat.succ_le_of_lt this
            _ ≥ (iter2 R I 0).card + (k+1) + 1 := by exact Nat.add_le_add_right ih' 1
            _ = (iter2 R I 0).card + (k+2) := by omega
            -/
        -- これを k := N に適用
        simpa using this N (Nat.le_refl _)

      -- ところが (iter2 _ _ (N+1)) は α の有限部分集合なので card ≤ N
      have hupper : (iter2 R I (N+1)).card ≤ N := by
        simpa [hN] using Finset.card_le_univ (iter2 R I (N+1))
      -- 下限 N+1 と上限 N の矛盾
      have : N + 1 ≤ N := by
        -- (iter2 0).card ≥ 0 を使えば `hsum` から N+1 ≤ card(N+1) ≤ N
        have h0 : (iter2 R I 0).card ≥ 0 := Nat.zero_le _
        have hsum' : (iter2 R I (N+1)).card ≥ 0 + (N+1) := by
          sorry
          --simpa using (Nat.le_trans (Nat.add_le_add_left h0 _) hsum)
        sorry
        --exact (le_trans hsum' hupper)
      exact Nat.not_succ_le_self N this
-/

/-
-- UC + Two-Stem：addedFamily への写像は witness ごとに高々1本（単射）
--Witnessにも同名で同内容の補題があるので、そっちに移動か。
--一つ上の補題とも同内容。
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hUC : UniqueChild (α:=α) R)
  {B : Finset α} {t : Rule α} {S₁ S₂ : Finset α}
  -- 追加の前提: B と S の分離性
  (hDisj1 : Disjoint B S₁)
  (hDisj2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t)
  (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 差分集合
  let D : Finset α := ((B ∪ S₁) \ (B ∪ S₂)) ∪ ((B ∪ S₂) \ (B ∪ S₁))

  by_cases hD : D = ∅
  · -- 差分なし ⇒ B∪S₁ = B∪S₂ ⇒ S₁=S₂
    have hEqU : B ∪ S₁ = B ∪ S₂ := by
      ext x
      constructor <;> intro hx
      · by_cases h : x ∈ B ∪ S₂
        · exact h
        · have : x ∈ D := by
            apply mem_union_left
            exact mem_sdiff.mpr ⟨hx, h⟩
          rw [hD] at this
          exact absurd this (Finset.notMem_empty x)
      · by_cases h : x ∈ B ∪ S₁
        · exact h
        · have : x ∈ D := by
            apply mem_union_right
            exact mem_sdiff.mpr ⟨hx, h⟩
          rw [hD] at this
          exact absurd this (Finset.notMem_empty x)

    -- B∪S₁ = B∪S₂ かつ Disjoint B S₁, Disjoint B S₂ から S₁ = S₂
    ext x
    constructor <;> intro hx
    · have : x ∈ B ∪ S₂ := by rw [←hEqU]; exact mem_union_right B hx
      cases mem_union.mp this with
      | inl hxB =>
        -- x ∈ B ∩ S₁ は Disjoint B S₁ に矛盾
        exact absurd (mem_inter.mpr ⟨hxB, hx⟩) (disjoint_iff_inter_eq_empty.mp hDisj1 ▸ not_mem_empty x)
      | inr hxS2 => exact hxS2
    · have : x ∈ B ∪ S₁ := by rw [hEqU]; exact mem_union_right B hx
      cases mem_union.mp this with
      | inl hxB =>
        exact absurd (mem_inter.mpr ⟨hxB, hx⟩) (disjoint_iff_inter_eq_empty.mp hDisj2 ▸ not_mem_empty x)
      | inr hxS1 => exact hxS1
  · -- 差分が非空の場合
    -- Two-Stem を使って初回差分座標 f を特定
    obtain ⟨f, hfPred, huniq⟩ :=
      firstDiff_localizes_one_coordinate (α:=α) ρ (R:=R) hTS
        (t:=t) (B:=B) (S₁:=S₁) (S₂:=S₂) hW1 hW2

    -- f が唯一の差分。片側で f∈B∪S₁, f∉B∪S₂ (または逆) を仮定して矛盾を示す
    cases hfPred with
    | inl hL =>
      -- f ∈ B∪S₁ かつ f ∉ B∪S₂ の場合
      obtain ⟨hfU1, hfN2⟩ := hL

      -- syncCl は closure と同じと仮定（または適切な補題で変換）
      have hfCl1 : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
        apply subset_syncCl
        exact hfU1

      -- 閉包の等式から f ∈ syncCl (R.erase t) (B ∪ S₂)
      have hfCl2 : f ∈ syncCl (R.erase t) (B ∪ S₂) := by
        rw [←hEq]
        exact hfCl1

      -- 一方 f ∉ B ∪ S₂ なので、f を導出するには R\{t} の中に head=f のルールが必要
      -- しかし UC により head=f のルールは R 全体で高々1本

      -- f が closure に入るには、ある導出経路が必要
      obtain ⟨path, hpath⟩ := syncCl_has_derivation hfCl2

      -- path の最後のルールを r とする（f を直接導くルール）
      obtain ⟨r, hr_in, hr_head, hr_prem⟩ := derivation_final_step hpath

      -- r ∈ R.erase t かつ r.head = f
      have hr_in_R : r ∈ R := by
        exact erase_subset _ _ hr_in

      -- UC により、R 内で head=f のルールは高々1本
      -- もし t.head = f なら、r = t となるが r ∈ R.erase t に矛盾
      by_cases ht_head : t.head = f
      · -- t.head = f の場合
        have : r = t := hUC hr_in_R (isWitness_implies_t_in_R hW1) (hr_head.trans ht_head.symm)
        exact absurd hr_in (not_mem_erase this)

      · -- t.head ≠ f の場合
        -- r は t と異なり、かつ head = f
        -- しかし witness の最小性により、f は S₁ の最小要素であり、
        -- B∪(S₁\{f}) からは f が導けないはず

        -- これは witness の定義と矛盾
        have : f ∈ S₁ := by
          cases mem_union.mp hfU1 with
          | inl hB => exact absurd (mem_inter.mpr ⟨hB, by assumption⟩)
                            (disjoint_iff_inter_eq_empty.mp hDisj1 ▸ not_mem_empty f)
          | inr hS => exact hS

        have : ¬(f ∈ syncCl (R.erase t) (B ∪ (S₁.erase f))) :=
          witness_minimal hW1 this

        -- しかし r.prem ⊆ B ∪ S₂ ⊆ B ∪ (S₁ の f 以外の要素) となるはず（差分唯一性）
        have : r.prem ⊆ B ∪ (S₁.erase f) := by
          intro x hx
          -- x ∈ r.prem ⊆ B ∪ S₂
          have hx_in : x ∈ B ∪ S₂ := hr_prem hx
          -- x ≠ f なら（f は唯一の差分）、x ∈ B ∪ S₁
          by_cases hxf : x = f
          · -- x = f は r.prem に含まれるが、f ∉ B∪S₂ に矛盾
            rw [hxf] at hx_in
            exact absurd hx_in hfN2
          · -- x ≠ f なので差分集合に含まれない
            have : x ∉ D := huniq x hxf
            -- 従って x ∈ (B∪S₁) ∩ (B∪S₂)
            simp [D] at this
            push_neg at this
            obtain ⟨h1, h2⟩ := this
            cases mem_union.mp (h1 hx_in) with
            | inl hB => exact mem_union_left _ hB
            | inr hS1 => exact mem_union_right _ (mem_erase.mpr ⟨hxf, hS1⟩)

        -- これで r を使って f が B∪(S₁\{f}) から導ける
        exact absurd (syncCl_rule_fires hr_in this hr_head) ‹¬(f ∈ syncCl _ _)›

    | inr hR =>
      -- f ∉ B∪S₁ かつ f ∈ B∪S₂ の場合（対称的に同じ論法）
      obtain ⟨hfN1, hfU2⟩ := hR

      have hfCl2 : f ∈ syncCl (R.erase t) (B ∪ S₂) :=
        subset_syncCl hfU2
      have hfCl1 : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
        rw [hEq]
        exact hfCl2

      -- 以下、上と対称的な論法で矛盾
      obtain ⟨path, hpath⟩ := syncCl_has_derivation hfCl1
      obtain ⟨r, hr_in, hr_head, hr_prem⟩ := derivation_final_step hpath

      have hr_in_R : r ∈ R := erase_subset _ _ hr_in

      by_cases ht_head : t.head = f
      · have : r = t := hUC hr_in_R (isWitness_implies_t_in_R hW1) (hr_head.trans ht_head.symm)
        exact absurd hr_in (not_mem_erase this)
      · have hf_in_S2 : f ∈ S₂ := by
          cases mem_union.mp hfU2 with
          | inl hB => exact absurd (mem_inter.mpr ⟨hB, by assumption⟩)
                            (disjoint_iff_inter_eq_empty.mp hDisj2 ▸ not_mem_empty f)
          | inr hS => exact hS

        have : ¬(f ∈ syncCl (R.erase t) (B ∪ (S₂.erase f))) :=
          witness_minimal hW2 hf_in_S2

        have : r.prem ⊆ B ∪ (S₂.erase f) := by
          intro x hx
          have hx_in : x ∈ B ∪ S₁ := hr_prem hx
          by_cases hxf : x = f
          · rw [hxf] at hx_in
            exact absurd hx_in hfN1
          · have : x ∉ D := huniq x hxf
            simp [D] at this
            push_neg at this
            obtain ⟨h1, h2⟩ := this
            cases mem_union.mp (h2 hx_in) with
            | inl hB => exact mem_union_left _ hB
            | inr hS2 => exact mem_union_right _ (mem_erase.mpr ⟨hxf, hS2⟩)

        exact absurd (syncCl_rule_fires hr_in this hr_head) ‹¬(f ∈ syncCl _ _)›
-/

/- first violation（定義は既存ファイル側のものを使う） -/
-- ここでは型だけ参照： violatesFirst ρ R t I




/-
---以下は検証用コード。しばらく残す。

namespace TestUC

-- ここでは Twostem の定義が Closure 名前空間から見える想定に合わせます
-- 必要なら Twostem. を付け替えてください。
-- 例：Twostem.UniqueChild_iff_UC など。

-- ---------- 具体例: α := Bool ----------
noncomputable instance : DecidableEq (Closure.Rule Bool) := Classical.decEq _
instance : DecidableEq Bool := inferInstance

open Finset

def r1 : Closure.Rule Bool := { head := true,  prem := (∅ : Finset Bool) }
def r2 : Closure.Rule Bool := { head := false, prem := (∅ : Finset Bool) }
def r3 : Closure.Rule Bool := { head := true,  prem := ({false} : Finset Bool) }

noncomputable def Rgood : Finset (Closure.Rule Bool) := insert r2 {r1}   -- = {r1, r2}
noncomputable def Rbad  : Finset (Closure.Rule Bool) := insert r3 {r1}   -- = {r1, r3}

@[simp] lemma mem_Rgood_iff {x : Closure.Rule Bool} :
    x ∈ Rgood ↔ x = r1 ∨ x = r2 := by
  constructor
  · intro hx
    have hx' : x = r2 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl hx2 =>
        right  -- x = r2 なので、ゴール (x = r1 ∨ x = r2) の右側
        exact hx2
    | inr hx1 =>
        have hxeq : x = r1 := (mem_singleton).1 hx1
        left  -- x = r1 なので、ゴール (x = r1 ∨ x = r2) の左側
        exact hxeq
  · intro h
    cases h with
    | inl hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        exact (mem_insert).2 (Or.inr this)
    | inr hx2 =>
        cases hx2
        exact (mem_insert_self r2 _)

@[simp] lemma mem_Rbad_iff {x : Closure.Rule Bool} :
    x ∈ Rbad ↔ x = r1 ∨ x = r3 := by
  constructor
  · intro hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl h =>
        right  -- x = r3 なので、ゴール (x = r1 ∨ x = r3) の右側
        exact h
    | inr h1 =>
        have : x = r1 := (mem_singleton).1 h1
        left  -- x = r1 なので、ゴール (x = r1 ∨ x = r3) の左側
        exact this
  · intro h
    cases h with
    | inl hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        exact (mem_insert).2 (Or.inr this)
    | inr hx3 =>
        cases hx3
        exact (mem_insert_self r3 _)


-- ---------- 一般形：等価の .mp / .mpr がそのまま使える ----------

section general
variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]
variable [DecidableEq (Closure.Rule α)]
variable {R : Finset (Closure.Rule α)}

example (h : Twostem.UniqueChild (α:=α) R) :
    Twostem.UC (α:=α) R :=
  (Twostem.UniqueChild_iff_UC (α:=α) R).mp h

example (h : Twostem.UC (α:=α) R) :
    Twostem.UniqueChild (α:=α) R :=
  (Twostem.UniqueChild_iff_UC (α:=α) R).mpr h
end general

-- ---------- 良い例：UC が成り立つ（＝ head ごとに高々1本） ----------

example : Twostem.UC (α:=Bool) Rgood := by
  intro a
  cases a with
  | false =>
      have hx :
        (Rgood.filter (fun t => t.head = false))
          = ({r2} : Finset (Closure.Rule Bool)) := by
        apply ext; intro x
        constructor
        · intro hxmem
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = false := (mem_filter).1 hxmem |>.2
          have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
          cases hx' with
          | inl h1 =>
              have : r1.head = true := rfl
              cases h1; cases this; cases hH
          | inr h2 => cases h2; exact (mem_singleton).2 rfl
        · intro hxmem
          have hx2 : x = r2 := (mem_singleton).1 hxmem
          have hR2 : r2 ∈ Rgood := by
            apply (mem_insert).2; left; rfl
          have hpair : r2 ∈ Rgood ∧ r2.head = false := And.intro hR2 rfl
          cases hx2; exact (mem_filter).2 hpair
      have hcard : (Rgood.filter (fun t => t.head = false)).card ≤ 1 := by
        have heq :
          (Rgood.filter (fun t => t.head = false)).card
            = ({r2} : Finset (Closure.Rule Bool)).card :=
          congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
        have hone : ({r2} : Finset (Closure.Rule Bool)).card = 1 :=
          card_singleton r2
        have : (Rgood.filter (fun t => t.head = false)).card = 1 :=
          Eq.trans heq hone
        exact Eq.le this
      exact hcard
  | true =>
      have hx :
        (Rgood.filter (fun t => t.head = true))
          = ({r1} : Finset (Closure.Rule Bool)) := by
        apply ext; intro x
        constructor
        · intro hxmem
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = true := (mem_filter).1 hxmem |>.2
          have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
          cases hx' with
          | inl h1 => cases h1; exact (mem_singleton).2 rfl
          | inr h2 => cases h2; cases hH
        · intro hxmem
          have hx1 : x = r1 := (mem_singleton).1 hxmem
          have hR1 : r1 ∈ Rgood :=
            (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
          have hpair : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
          cases hx1; exact (mem_filter).2 hpair
      have heq :
        (Rgood.filter (fun t => t.head = true)).card
          = ({r1} : Finset (Closure.Rule Bool)).card :=
        congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
      have hone : ({r1} : Finset (Closure.Rule Bool)).card = 1 :=
        card_singleton r1
      have hfin : (Rgood.filter (fun t => t.head = true)).card = 1 :=
        Eq.trans heq hone
      exact Eq.le hfin

-- UniqueChild も Rgood では成立（等価で変換）
example : Twostem.UniqueChild (α:=Bool) Rgood :=
  (Twostem.UniqueChild_iff_UC (α:=Bool) Rgood).mpr
    (by
      intro a
      cases a with
      | false =>
          -- a = false の場合
          have hx :
            (Rgood.filter (fun t => t.head = false))
              = ({r2} : Finset (Closure.Rule Bool)) := by
            apply ext; intro x
            constructor
            · intro hxmem
              have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
              have hH : x.head = false := (mem_filter).1 hxmem |>.2
              have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
              cases hx' with
              | inl h1 => cases h1; cases hH
              | inr h2 => cases h2; exact (mem_singleton).2 rfl
            · intro hxmem
              have hx2 : x = r2 := (mem_singleton).1 hxmem
              have hR2 : r2 ∈ Rgood := (mem_insert).2 (Or.inl rfl)
              have hpair : r2 ∈ Rgood ∧ r2.head = false := And.intro hR2 rfl
              cases hx2; exact (mem_filter).2 hpair
          have heq :
            (Rgood.filter (fun t => t.head = false)).card
              = ({r2} : Finset (Closure.Rule Bool)).card :=
            congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
          have hone : ({r2} : Finset (Closure.Rule Bool)).card = 1 :=
            card_singleton r2
          have hfin :
            (Rgood.filter (fun t => t.head = false)).card = 1 :=
            Eq.trans heq hone
          exact Eq.le hfin
      | true =>
          -- a = true の場合
          have hx :
            (Rgood.filter (fun t => t.head = true))
              = ({r1} : Finset (Closure.Rule Bool)) := by
            apply ext; intro x
            constructor
            · intro hxmem
              have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
              have hH : x.head = true := (mem_filter).1 hxmem |>.2
              have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
              cases hx' with
              | inl h1 => cases h1; exact (mem_singleton).2 rfl
              | inr h2 => cases h2; cases hH
            · intro hxmem
              have hx1 : x = r1 := (mem_singleton).1 hxmem
              have hR1 : r1 ∈ Rgood :=
                (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
              have hpair : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
              cases hx1; exact (mem_filter).2 hpair
          have heq :
            (Rgood.filter (fun t => t.head = true)).card
              = ({r1} : Finset (Closure.Rule Bool)).card :=
            congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
          have hone : ({r1} : Finset (Closure.Rule Bool)).card = 1 :=
            card_singleton r1
          have hfin :
            (Rgood.filter (fun t => t.head = true)).card = 1 :=
            Eq.trans heq hone
          exact Eq.le hfin
    )

-- ---------- 悪い例：UniqueChild も UC も成り立たない ----------

example : ¬ Twostem.UniqueChild (α:=Bool) Rbad := by
  intro hUC
  have hr1 : r1 ∈ Rbad :=
    (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
  have hr3 : r3 ∈ Rbad :=
    (mem_insert).2 (Or.inl rfl)
  have hhead : r1.head = r3.head := rfl
  have h_eq : r1 = r3 := hUC hr1 hr3 hhead
  have hprem : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h_eq
  have hneq : (∅ : Finset Bool) ≠ ({false} : Finset Bool) := by
    intro h
    have : false ∈ (∅ : Finset Bool) := by
      rw [h]; exact mem_singleton_self false
    exact (List.mem_nil_iff false).mp this
  exact hneq hprem


example : ¬ Twostem.UC (α:=Bool) Rbad := by
  intro hUC
  have hr1 : r1 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r1 ∈ Rbad :=
      (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
    have : r1 ∈ Rbad ∧ r1.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  have hr3 : r3 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r3 ∈ Rbad := (mem_insert).2 (Or.inl rfl)
    have : r3 ∈ Rbad ∧ r3.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  have hneq : r1 ≠ r3 := by
    intro h
    have : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h
    have : (∅ : Finset Bool) = ({false} : Finset Bool) := this
    have : false ∈ (∅ : Finset Bool) := by
      rw [this]; exact mem_singleton_self false
    exact (List.mem_nil_iff false).mp this

  have hsubset : insert r3 ({r1} : Finset (Closure.Rule Bool))
                  ⊆ Rbad.filter (fun t => t.head = true) := by
    intro x hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_insert).1 hx
    cases hx' with
    | inl hx3 => cases hx3; exact hr3
    | inr hx1 =>
        have : x = r1 := (mem_singleton).1 hx1
        cases this; exact hr1
  have hpair : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card = 2 := by
    have hnot : r3 ∉ ({r1} : Finset (Closure.Rule Bool)) := by
      intro hx; apply hneq; exact (mem_singleton).1 hx |>.symm
    have hbase : ({r1} : Finset (Closure.Rule Bool)).card = 1 := card_singleton r1
    have : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card
              = ({r1} : Finset (Closure.Rule Bool)).card + 1 :=
      card_insert_of_notMem hnot
    rw [hbase] at this
    exact this
  have hge2 : 2 ≤ (Rbad.filter (fun t => t.head = true)).card := by
    calc 2 = (insert r3 ({r1} : Finset (Closure.Rule Bool))).card := hpair.symm
         _ ≤ (Rbad.filter (fun t => t.head = true)).card := card_le_card hsubset

  have hle1 : (Rbad.filter (fun t => t.head = true)).card ≤ 1 := hUC true
  omega

end TestUC
-/


/-

--単射性の証明に使う？Unique Childはいらないのか。そのままではなりたたない。
/-- Two-Stem による「初回差の 1 座標局在」の仕様（抽象化）。
    実装では「B∪S と B∪S' の (R\{t})-closure を同期的に回したとき、
    最初に分岐する箇所は Free の 1 座標 f に限る」ことを述べる。 -/
private lemma firstDiff_localizes_one_coordinate
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (hTS : TwoStemR R) (B S S' : Finset α) (t : Rule α)
  (hS : isWitness (α:=α) ρ R B S t)
  (hS' : isWitness (α:=α) ρ R B S' t)
  (hne : S ≠ S')
  (hEq : syncCl (R.erase t) (B ∪ S) = syncCl (R.erase t) (B ∪ S')) :
  ∃ f,
    f ∈ (S ∆ S') ∧
    ((f ∈ B ∪ S ∧ f ∉ B ∪ S') ∨ (f ∉ B ∪ S ∧ f ∈ B ∪ S')) ∧
    (∀ g, g ≠ f → g ∉ ((B ∪ S) \ (B ∪ S') ∪ (B ∪ S') \ (B ∪ S))) := by
  classical

  -- 対称差が非空であることを確認
  have hNonempty : (S ∆ S').Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have : S = S' := by
      ext x
      constructor <;> intro hx
      · by_contra hnx
        have : x ∈ S ∆ S' := by
          simp [symmDiff_def, Finset.mem_sdiff]
          exact Or.inl ⟨hx, hnx⟩
        rw [h] at this
        exact Finset.notMem_empty x this
      · by_contra hnx
        have : x ∈ S ∆ S' := by
          simp [symmDiff_def, Finset.mem_sdiff]
          exact Or.inr ⟨hx, hnx⟩
        rw [h] at this
        exact Finset.notMem_empty x this
    exact hne this

  -- 対称差の最小要素を f とする
  obtain ⟨f, hf_mem, hf_min⟩ := (S ∆ S').exists_min_image id hNonempty

  use f

  constructor
  · exact hf_mem

  constructor
  · -- f は B∪S と B∪S' の一方にのみ属する
    simp [symmDiff_def, Finset.mem_sdiff] at hf_mem
    cases hf_mem with
    | inl h =>
      obtain ⟨hfS, hfnS'⟩ := h
      left
      constructor
      · exact Finset.mem_union_right B hfS
      · intro hf
        cases Finset.mem_union.mp hf with
        | inl hB =>
          -- f ∈ B ∩ S は分離性から矛盾（witness の性質）
          have : Disjoint B S := isWitness_disjoint hS
          exact absurd (Finset.mem_inter.mpr ⟨hB, hfS⟩)
            (Finset.disjoint_iff_inter_eq_empty.mp this ▸ Finset.notMem_empty f)
        | inr hS' => exact hfnS' hS'
    | inr h =>
      obtain ⟨hfS', hfnS⟩ := h
      right
      constructor
      · intro hf
        cases Finset.mem_union.mp hf with
        | inl hB =>
          have : Disjoint B S' := isWitness_disjoint hS'
          exact absurd (Finset.mem_inter.mpr ⟨hB, hfS'⟩)
            (Finset.disjoint_iff_inter_eq_empty.mp this ▸ Finset.not_mem_empty f)
        | inr hS => exact hfnS hS
      · exact Finset.mem_union_right B hfS'

  · -- f の一意性：g ≠ f なら g は差分に含まれない
    intro g hgf
    intro hg

    simp [Finset.mem_union, Finset.mem_sdiff] at hg

    -- g が差分集合に属するなら、g ∈ S ∆ S'
    have hg_symmDiff : g ∈ S ∆ S' := by

      cases hg with
      | inl h =>

        obtain ⟨⟨hgBS, hgnBS'⟩, _⟩ := h
        cases Finset.mem_union.mp hgBS with
        | inl hgB =>
          -- g ∈ B なら両側に属するはず（B は共通部分）
          have : g ∈ B ∪ S' := Finset.mem_union_left S' hgB
          exact absurd this hgnBS'
        | inr hgS =>
          cases Finset.mem_union.mp hgnBS' with
          | inl =>
            left
            constructor
            · exact hgS
            · intro hgS'
              exact absurd (Finset.mem_union_right B hgS') hgnBS'
          | inr =>
            left
            constructor
            · exact hgS
            · intro hgS'
              exact absurd (Finset.mem_union_right B hgS') hgnBS'
      | inr h =>
        obtain ⟨⟨hgBS', hgnBS⟩, _⟩ := h
        cases Finset.mem_union.mp hgBS' with
        | inl hgB =>
          have : g ∈ B ∪ S := Finset.mem_union_left S hgB
          exact absurd this hgnBS
        | inr hgS' =>
          right
          constructor
          · exact hgS'
          · intro hgS
            exact absurd (Finset.mem_union_right B hgS) hgnBS

    -- g ∈ S ∆ S' かつ f が最小 ⇒ f ≤ g
    have : ρ.toFun f ≤ ρ.toFun g := hf_min g hg_symmDiff

    -- しかし Two-Stem の下で、f より大きい g が本質的差分であることは不可能
    -- なぜなら：
    -- 1) B ∪ (S ∩ S') から出発して同期的閉包を構成
    -- 2) f を追加する/しないで最初の分岐が生じる
    -- 3) その後の g での差分は f の分岐の結果にすぎない

    -- 共通部分を定義
    let common := B ∪ (S ∩ S')

    -- f を含む側と含まない側の閉包を考える
    have hClosure_analysis :
      ∃ (step : ℕ),
        let cl_with_f := iterate_syncCl (R.erase t) (common ∪ {f}) step
        let cl_without_f := iterate_syncCl (R.erase t) common step
        g ∈ cl_with_f ∧ g ∉ cl_without_f := by
      sorry -- この部分は iterate_syncCl の詳細な性質が必要

    obtain ⟨step, hstep⟩ := hClosure_analysis

    -- g を導出するルール r が存在
    obtain ⟨r, hr_in, hr_head, hr_prem⟩ :=
      element_has_rule_in_closure hstep.1

    -- Two-Stem: r.prem.card ≤ 2
    have hTS_r : r.prem.card ≤ 2 := hTS r hr_in

    -- r.prem ⊆ cl_with_f かつ g = r.head
    -- r.prem の要素で cl_without_f に含まれないものを分析

    have : ∃ x ∈ r.prem, x ∈ cl_with_f ∧ x ∉ cl_without_f := by
      by_contra h
      push_neg at h
      -- すべての r.prem が cl_without_f に含まれるなら
      have : r.prem ⊆ cl_without_f := fun x hx =>
        (h x hx).2 (hr_prem hx)
      -- g = r.head も cl_without_f に含まれるはず
      have : g ∈ cl_without_f :=
        syncCl_rule_fires hr_in this hr_head
      exact hstep.2 this

    obtain ⟨x, hx_prem, hx_diff⟩ := this

    -- x での差分が f より小さい位置で生じる
    -- しかし f は最小差分なので矛盾

    -- x が f より小さいか f 自身かを判定
    by_cases hxf : x = f
    · -- x = f の場合：f が r.prem に直接含まれる
      -- これは許容（f が直接使われて g が導出される）
      -- しかし g ≠ f なので、g は f の後の段階で導出される
      -- つまり g は本質的差分ではなく派生的差分
      sorry -- 詳細な段階解析が必要
    · -- x ≠ f の場合：x も差分要素
      have : x ∈ S ∆ S' := by
        sorry -- x が差分であることを示す
      -- x ∈ S ∆ S' かつ x が f より先に差分を生じる
      -- しかし f は最小差分なので ρ.toFun f ≤ ρ.toFun x
      have : ρ.toFun f ≤ ρ.toFun x := hf_min x ‹x ∈ S ∆ S'›
      -- Two-Stem により |r.prem| ≤ 2 なので
      -- r.prem = {f, y} または {x, y} の形
      -- いずれにしても f より小さい本質的差分 x が存在することになり
      -- f の最小性に矛盾
      sorry
-/


/-証明はとおっているが、コメントアウトしたもので使っているだけ。消しても良い。
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma in_symmDiff_ne_f_impossible
  [DecidableEq α]
  {R : Finset (Rule α)} {U V : Finset α} {m : ℕ} {f x : α}
  (hLast : (parIter R U m \ parIter R V m ∪ parIter R V m \ parIter R U m) ⊆ {f})
  (hx : x ∈ parIter R U m \ parIter R V m ∪ parIter R V m \ parIter R U m)
  (hxf : x ≠ f) : False := by
  classical
  have : x ∈ ({f} : Finset α) := hLast hx
  have : x = f := by simpa [Finset.mem_singleton] using this
  exact hxf this
-/

/-なりたたないかも
lemma symmDiff_mono_under_NoSwap'
  [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R)
  (U V : Finset α) (k : ℕ) (f : α)
  (hEqNext : parIter R U (k+1) = parIter R V (k+1))
  (hk : let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m);
        D k = {f}) :
  let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
  ∀ m ≤ k, D m ⊆ {f} := by
  classical
  -- 記法短縮
  let D : ℕ → Finset α :=
    fun n => (parIter R U n \ parIter R V n) ∪ (parIter R V n \ parIter R U n)
  intro D m hm
  -- 逆向き（k から m へ）の降順帰納を使うのが自然
  -- 命題 Q(n): D n ⊆ {f}
  -- Q(k) は仮定から成り立つ。
  -- n < k → Q(n+1) から Q(n) を示すのに必要なのは、
  --   D n ⊆ D (n+1) ∪ {f} という“1ステップ抑え込み”補題。
  -- これを NoSwap と「最終段(k+1)の一致」と組み合わせれば出せます。
  -- d := k - m を固定
  --set d : ℕ := k - m with hdm
  generalize hdm : k - m = d
  -- m を一般化して d で帰納
  revert m
  induction' d with d ih
  -- base : d = 0
  case zero =>
    intro m hm hdm
    -- k - m = 0 ⇒ k ≤ m。hm : m ≤ k と合わせて m = k
    have hkm0 : k - m = 0 := hdm
    have hkm : k ≤ m :=by exact Nat.le_of_sub_eq_zero hdm
    have : m = k := le_antisymm hm hkm
    subst this
    -- ここで P k を示す
    -- ...（あなたの目的に応じて書く）
    exact Finset.subset_of_eq hk

  -- step : d → d+1
  case succ _ _ _ _ _ ih =>
    -- k - m = d+1 > 0 ⇒ m < k
    intro m hm hdm
    have hm_lt : m < k := by
      have : 0 < d.succ := Nat.succ_pos d
      -- k - m > 0 ↔ m < k
      exact Nat.lt_of_sub_eq_succ hdm
    -- m+1 も k 以下
    have hm1 : m + 1 ≤ k := Nat.succ_le_of_lt hm_lt
    -- 算術：k - (m+1) = d
    have hdm1 : k - (m+1) = d := by
      -- k - (m+1) = (k - m) - 1, かつ k - m = d+1
      have : k - (m+1) = k - m - 1 := by
        simpa using (Nat.sub_sub k m 1).symm
      simp [this, hdm]   -- → d

    -- 帰納法で P (m+1)
    apply ih

    exact hm
    sorry
  -/

/-なりたたないよう。
-- 補助補題2：NoSwapの下での差分の非増加性
lemma symmDiff_mono_under_NoSwap [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R)
  (U V : Finset α) (m k : ℕ) (f : α)
  (hk : let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
        D k = {f}) :
  let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
  ∀ m ≤ k, D m ⊆ {f} := by
  classical
  -- D を束縛
  let D : ℕ → Finset α :=
    fun n =>
      (parIter R U n \ parIter R V n) ∪
      (parIter R V n \ parIter R U n)

  -- ゴール：∀ m ≤ k, D m ⊆ {f}
  intro D m hm

  -- 「set … with hd」は使わず generalize にするのが安定
  generalize hdm : k - m = d
  -- d で帰納（m を generalizing）
  induction' d with d ih generalizing m

  -- base: d = 0 → k - m = 0 → m = k
  · intro DD hm
    have hk_le_m : k ≤ m := by exact Nat.le_of_sub_eq_zero hdm--Nat.sub_eq_zero.mp hdm
    have hm_eq : m = k := by (expose_names; exact Nat.le_antisymm hm_1 hk_le_m)--(le_antisymm hm hk_le_m).symm
    have hk' : D k = ({f} : Finset α) := by simpa [D] using hk
    subst hm_eq
    simp_all only [mem_singleton, le_refl, tsub_self, D]

  -- step: d.succ → d
  · intro DD hm
    -- hdm : k - m = d.succ ⇒ m < k
    have hlt : m < k := by
      have : k - m ≠ 0 := by
        rename_i D_2 hm_1
        simp_all only [subset_singleton_iff, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
          not_false_eq_true]

      apply  Nat.lt_of_le_of_ne
      rename_i D_2 hm_1
      simp_all only [subset_singleton_iff, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true]
      intro hh
      rw [hh] at this
      simp at this

    -- 算術整形：k - (m+1) = d
    have hdm1 : k - (m+1) = d := by
      have h : k - (m+1) = k - m - 1 := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using (Nat.sub_sub k m 1).symm
      simpa [hdm, Nat.succ_sub_one] using h

    -- 帰納仮説を m+1 に適用：D (m+1) ⊆ {f}

    have ih' : D (m+1) ⊆ ({f} : Finset α) := by
      -- ih : ∀ m, m ≤ k → k - m = d → D m ⊆ {f}
      -- hdm1 を渡す
      exact ih (m + 1) hlt hdm1

    -- NoSwap 一歩補題：D m ⊆ D (m+1) ∪ {f}
    --have hstep : D m ⊆ D (m+1) ∪ ({f} : Finset α) := by
      -- ここはあなたの補題に差し替え
    let isn := @in_symmDiff_ne_f_impossible _ _ _ _ _ _ R U V m f

    search_proof


        --(or.inr True.intro)
        --(x:=x) (hx:=hx) (hxf:=hxf)


    -- 合成して D m ⊆ {f}
    have :D (m + 1) ∪ {f} = {f} := by
      exact union_eq_right.mpr (ih (m + 1) hlt hdm1)

    have : D m ⊆ ({f} : Finset α) := by
      rw [this] at hstep
      exact hstep
    exact this hm
-/


/- これもなりたたないっぽい
-- メイン補題での使用
lemma input_symmDiff_singleton_of_syncEq
  {R : Finset (Rule α)} (hNTF : NoTwoFreshHeads R) (hNS : NoSwap R)
  {U V : Finset α}
  (hSync : syncCl R U = syncCl R V) :
  U = V ∨ ∃ f, (U \ V) ∪ (V \ U) = {f} := by
  classical
  have hED :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R':=R) hNTF hNS (U:=U) (V:=V) hSync
  cases hED with
  | inl hUV =>
    exact Or.inl hUV
  | inr hK =>
    rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩

    let D : Nat → Finset α := fun m =>
      (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)

    have hDk : D k = {f} := by
      simpa [D] using hSingle

    -- 切り出した補題を使用
    have hMono : ∀ m, m ≤ k → D m ⊆ {f} := by
      apply symmDiff_mono_under_NoSwap R hNS U V k
      intro D_1
      simp_all only [D, D_1]

    have hD0_sub : D 0 ⊆ ({f} : Finset α) :=
      hMono 0 (Nat.zero_le _)

    by_cases hD0_empty : D 0 = ∅
    · left
      have : (U \ V) ∪ (V \ U) = (∅ : Finset α) := by
        simpa [D, parIter] using hD0_empty
      ext x
      constructor <;> intro hx <;> by_contra hcontra
      · have : x ∈ U \ V := Finset.mem_sdiff.mpr ⟨hx, hcontra⟩
        have : x ∈ (U \ V) ∪ (V \ U) := Finset.mem_union_left _ this
        rw [‹(U \ V) ∪ (V \ U) = ∅›] at this
        exact Finset.notMem_empty x this
      · have : x ∈ V \ U := Finset.mem_sdiff.mpr ⟨hx, hcontra⟩
        have : x ∈ (U \ V) ∪ (V \ U) := Finset.mem_union_right _ this
        rw [‹(U \ V) ∪ (V \ U) = ∅›] at this
        exact Finset.notMem_empty x this

    · right
      use f
      have hD0_nonempty : (D 0).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hD0_empty
      have hEq : D 0 = {f} := by
        have : ∀ x ∈ D 0, x = f := by
          intro x hx
          have : x ∈ ({f} : Finset α) := hD0_sub hx
          simpa using this
        obtain ⟨y, hy⟩ := hD0_nonempty
        have : y = f := this y hy
        rw [this] at hy
        ext x
        simp
        constructor
        · intro hx
          (expose_names; exact this_1 x hx)
        · intro hx
          rw [hx]
          exact hy
      simpa [D, parIter] using hEq

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
/-- 上の補題をそのまま使える形（`t ∈ R` を引数に含める版）。 -/
lemma erased_cause_head_ne_thead'
  {R : Finset (Rule α)} {t r : Rule α}
  (hUC : UniqueChild α R) (ht : t ∈ R) (hrErase : r ∈ R.erase t) :
  r.head ≠ t.head := by
  classical
  have hrR : r ∈ R := mem_of_mem_erase hrErase
  intro hEq
  have : r = t := hUC hrR ht hEq
  exact ne_of_mem_erase hrErase this
-/
