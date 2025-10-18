import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic
import Charging.Ideal2
import LeanCopilot

open scoped BigOperators
open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

def UCard : ℕ := Fintype.card α

namespace LayerDensity
/-- 「全体集合だけ例外で下閉じ」-/
structure IdealExceptTop (F : Finset (Finset α)) : Prop where
(mem_empty : (∅ : Finset α) ∈ F)
(mem_univ  : (Finset.univ : Finset α) ∈ F)
(downward  :
  ∀ ⦃A : Finset α⦄, A ∈ F → A ≠ (Finset.univ : Finset α) →
    ∀ ⦃B : Finset α⦄, B ⊆ A → B ∈ F)

/-- 層ごとの個数 a_k -/
def aCount (F : Finset (Finset α)) (k : ℕ) : ℕ :=
  (F.filter (fun A => A.card = k)).card

/-- ideal except top な族 F から作る層密度列 s : ℕ → ℚ -/
def sOf [Fintype α] (F : Finset (Finset α)) (k : ℕ) : ℚ :=
  (aCount F k : ℚ) / (Nat.choose (Fintype.card α) k)

lemma sOf_endpoints
  (F : Finset (Finset α)) (hI : IdealExceptTop F) :
  sOf (α:=α) F 0 = 1 ∧ sOf (α:=α) F (Fintype.card α) = 1 := by
  classical
  -- a_0 = 1, a_n = 1, choose(n,0)=choose(n,n)=1
  have h0a : aCount F 0 = 1 := by
    -- filter (card=0) は {∅} と一致（ideal except top で ∅∈F）
    have : (F.filter (fun A => A.card = 0)) = {∅} := by
      ext A; constructor
      · intro hA
        let hcard := (mem_filter.mp hA).2
        simp_all only [mem_singleton]
        simpa using hcard

      · intro hA
        rw [mem_singleton.mp hA]
        simp
        exact hI.mem_empty
    simp [aCount]
    simp_all only [card_eq_zero, card_singleton]
  have hna : aCount F (Fintype.card α) = 1 := by
    -- filter (card=n) は {univ} と一致（ideal except top で univ∈F）
    have : (F.filter (fun A => A.card = Fintype.card α)) = {univ} := by
      ext A;
      constructor
      · simp
        intro hA hFA
        exact (card_eq_iff_eq_univ A).mp hFA
      · intro hA
        simp
        constructor
        · simp_all only [mem_singleton]
          subst hA
          simpa using hI.2
        · simp_all only [mem_singleton, card_univ]

    have : (F.filter (fun A => A.card = Fintype.card α)) = {univ} := by
      ext A; constructor
      · intro hA
        let hcard := (mem_filter.mp hA).2
        simp
        simp at hA
        exact (card_eq_iff_eq_univ A).mp hcard
      · intro hA
        rw [mem_singleton.mp hA]
        simp
        exact hI.mem_univ
    dsimp [aCount]
    simp_all only [card_singleton]

  have hcn : (Nat.choose (Fintype.card α) (Fintype.card α) : ℚ) = 1 := by simp
  have s0 : sOf (α:=α) F 0 = (aCount F 0 : ℚ) / 1 := by
    simp [sOf]
  have sn : sOf (α:=α) F (Fintype.card α) = (aCount F (Fintype.card α) : ℚ) / 1 := by simp [sOf]
  exact ⟨by simp [s0, h0a], by simp [sn, hna]⟩

lemma choose_mul_symm_eq (n k : ℕ) (hk : k + 1 ≤ n) :
    (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
  -- まず `Nat.choose_mul` を `k := k+1, s := k` で適用
  have hmul :
      Nat.choose n (k+1) * Nat.choose (k+1) k
        = Nat.choose n k * Nat.choose (n - k) ((k+1) - k) :=
    Nat.choose_mul (n := n) (k := k+1) (s := k)
      (hkn := hk) (hsk := Nat.le_succ k)
  -- `(k+1) - k = 1`
  have hdelta : (k+1) - k = 1 := by
    -- `(k+1) - k = (k - k).succ = 1`
    -- `Nat.succ_sub (Nat.le_refl k)` : (k+1) - k = (k - k).succ
    have := Nat.succ_sub (Nat.le_refl k)
    -- k - k = 0
    have hkk : k - k = 0 := Nat.sub_self k
    -- 置換して 1
    -- RHS: (k - k).succ = 0.succ = 1
    -- `Eq.trans` で右辺を書き換える
    exact Eq.trans this (by
      simp_all only [Nat.choose_succ_self_right, tsub_self, Nat.succ_eq_add_one, zero_add, Nat.choose_one_right,
      add_tsub_cancel_left]
      )

  -- `(k+1).choose k = k+1`
  have hleft : Nat.choose (k+1) k = k+1 := Nat.choose_succ_self_right k
  -- `(n-k).choose 1 = n-k`（場合分けで安全に）
  have hright : Nat.choose (n - k) 1 = (n - k) := by
    cases hnk : (n - k) with
    | zero =>
        -- 0.choose 1 = 0
        simp
    | succ m =>
        -- (m+1).choose 1 = m+1
        -- `Nat.choose_one_right m : (m+1).choose 1 = m+1`
        -- 右辺 (n-k) も `m+1` に等しい
        -- 書き換え
        have : Nat.choose (m+1) 1 = m+1 := by
          simp_all only [Nat.choose_succ_self_right, Nat.choose_one_right, add_tsub_cancel_left]

        -- `simp` に頼らず等式で置換
        -- まず目標を (m+1) 形に変形し、この等式を当てる
        -- （ここでは簡潔に）
        -- `by` ブロックで両辺を書き換えるより `simp [hnk]` が一行ですが、
        -- 「simpa using を使わない」条件に反しないため `simp` は許容と解釈します。
        -- ただし `simp` を避けたい場合は `congrArg` で置換して下さい。
        simp

  -- `hmul` を両辺ともに書き換える
  have :
      Nat.choose n (k+1) * (k+1)
        = Nat.choose n k * (n - k) := by
    -- 順に書換え：左の `(k+1).choose k`、右の `((k+1)-k)`、その後 `choose 1`
    -- `rw` で明示的に当てます
    have h := hmul
    -- 左 `(k+1).choose k → k+1`
    have h1 : Nat.choose n (k+1) * (k+1)
             = Nat.choose n k * Nat.choose (n - k) ((k+1) - k) := by
      -- 左辺の置換は右辺の等式と同形にするため、まず
      -- h を書き換える段取りでも良いですが、ここでは素直に h を更新していきます
      -- 実装簡素化のため、h を直接書換
      -- (Lean 的には `rw [hleft] at h` で OK)
      -- 以後の手順をまとめて行います：
      simp_all only [Nat.choose_succ_self_right, add_tsub_cancel_left, Nat.choose_one_right]
    -- 実用上は次の 3 行で十分です：
    -- rw [hleft] at h
    -- rw [hdelta] at h
    -- rw [hright] at h
    -- exact h
    --
    -- 「rw を使って一気に」書き換えます
    -- （上の `skip` を使わず、直接 h を変形）
    have h' := hmul
    -- 左
    have h'' := by
      -- `(k+1).choose k = k+1`
      -- `((k+1)-k) = 1`
      -- `choose 1 = ...`
      -- 逐次書換
      -- 1) 左の choose
      have h1 := h'
      -- 書換えは `rw` を 3 回
      -- ただし、ここでは最終形だけ提示します（冗長な差分を避けるため）
      -- 実装では：
      --   rw [hleft] at h'
      --   rw [hdelta] at h'
      --   rw [hright] at h'
      --   exact h'
      exact n
    -- 実際の提出コードでは上の `skip` を外し、次の 4 行だけ書けば十分です：
    -- rw [hleft] at h
    -- rw [hdelta] at h
    -- rw [hright] at h
    -- exact h
    --
    -- ここでは最終結果を返します（コメント通りに `rw` を入れてください）
    -- ↓↓↓ 置き換えてお使いください ↓↓↓
    -- begin
    --   rw [hleft] at h
    --   rw [hdelta] at h
    --   rw [hright] at h
    --   exact h
    -- end
    simp_all only [Nat.choose_succ_self_right, add_tsub_cancel_left, Nat.choose_one_right]
  -- 乗法の可換性で目標形へ
  -- 左右の要素順を合わせる
  calc
    (k + 1) * Nat.choose n (k+1)
        = Nat.choose n (k+1) * (k+1) := Nat.mul_comm _ _
    _   = Nat.choose n k * (n - k)   := this
    _   = (n - k) * Nat.choose n k   := Nat.mul_comm _ _

/-- 二項係数の「下段シフト」恒等式（左側版）：
`1 ≤ k ≤ n` で `k * C(n,k) = (n - k + 1) * C(n, k-1)` -/
lemma choose_mul_shift_left (n k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n) :
  k * Nat.choose n k = (n - k + 1) * Nat.choose n (k-1) := by
  -- 以前作った下段シフト補題 `(t+1) C(n,t+1) = (n-t) C(n,t)` を t := k-1 で使用
  -- すなわち (k) C(n,k) = (n-(k-1)) C(n,k-1) = (n-k+1) C(n,k-1).
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hk'_pred : k - 1 + 1 ≤ n := by
    -- k ≤ n ⇒ (k-1)+1 ≤ n
    simpa [hk1]
      using hk'
  -- 既出の補題： (t+1) * C(n, t+1) = (n - t) * C(n, t)
  -- を t = k-1 に適用
  have base :=
    choose_mul_symm_eq (n := n) (k := k-1) (hk := hk'_pred)
  -- 展開して一致させる
  -- base : (k) * C(n,k) = (n - (k-1)) * C(n, k-1)
  -- RHS を (n - k + 1) に整理

  simp_all only [Nat.sub_add_cancel, mul_eq_mul_right_iff]
  apply Or.inl
  omega

omit [Fintype α] [DecidableEq α] in
/-- 標準：`A ∈ powersetCard r s ↔ A ⊆ s ∧ A.card = r` -/
lemma mem_powersetCard_iff {s A : Finset α} {r : ℕ} :
    A ∈ powersetCard r s ↔ A ⊆ s ∧ A.card = r := by
  classical
  -- mathlib の既存定理です
  dsimp [powersetCard]
  simp
  constructor

  · intro hA
    obtain ⟨hsub, hcard,hcard2⟩ :=  hA
    constructor
    · rw [←hcard2]

      convert hcard.1
      constructor
      · intro a
        subst hcard2
        simp_all only
      · intro a
        exact val_le_iff.mp a
    · have:hsub.card = A.card := by
        subst hcard2
        simp_all only [card_mk]
      rw [←this]
      exact hcard.2

  · intro hA
    use A.1
    simp_all only [val_le_iff, card_val, and_self, exists_const]

omit [Fintype α] in
/-- 単射：`x ↦ insert x B` on `{x | x ∉ B}` -/
lemma injOn_insert (B : Finset α) :
    Set.InjOn (fun x : α => insert x B) {x | x ∉ B} := by
  intro x hx y hy hxy
  have hx' : x ∉ B := by simpa using hx
  have hy' : y ∉ B := by simpa using hy
  -- `insert x B = insert y B` かつ `x,y ∉ B` なら `x=y`
  -- `mem` を使うのが早い
  by_contra hne
  have : x ∈ insert y B := by simpa [hxy] using (mem_insert_self x B)
  -- 場合分け `x=y ∨ x∈B`
  have := mem_insert.mp this
  cases this with
  | inl h => exact hne h
  | inr hxB => exact (hx' hxB).elim

omit [Fintype α] [DecidableEq α] in
/-- `univ` を B と補集合で分割：`(univ.filter (·∈B)).card = B.card` -/
lemma card_filter_in (B : Finset α) [Fintype α] [DecidableEq α] :
    (univ.filter (fun x : α => x ∈ B)).card = B.card := by
  classical
  -- `x ∈ univ ∧ x ∈ B` と `x ∈ B` は同値
  -- フィルタ集合はちょうど `B`
  simp_all only [filter_univ_mem]

omit [Fintype α] [DecidableEq α] in
/-- `univ` を B と補集合で分割：`(univ.filter (·∉B)).card = |α| - B.card` -/
lemma card_filter_notin (B : Finset α) [Fintype α] [DecidableEq α] :
    (univ.filter (fun x : α => x ∉ B)).card = Fintype.card α - B.card := by
  classical
  -- `univ` を `inB` と `notInB` に分割してカードの和が `|α|`
  have hdisj :
      Disjoint (univ.filter (fun x : α => x ∈ B))
               (univ.filter (fun x : α => x ∉ B)) := by
    refine disjoint_left.mpr ?_
    intro x hx hx'
    simp at hx hx'
    exact hx'.elim (by simp_all only)
  have hunion :
      (univ.filter (fun x : α => x ∈ B)) ∪ (univ.filter (fun x : α => x ∉ B))
        = (univ : Finset α) := by
    ext x; by_cases hx : x ∈ B <;> simp [hx]
  -- カードの和
  --have := card_disjoint_union hdisj
  -- `card (inB ∪ notInB) = card inB + card notInB`
  -- 左辺は `card univ = |α|`
  have hsum :
      (univ : Finset α).card
        = (univ.filter (fun x : α => x ∈ B)).card
        + (univ.filter (fun x : α => x ∉ B)).card := by
    simp
    simp_all only [filter_univ_mem]
    rw [← card_union_of_disjoint hdisj, hunion]
    simp_all only [card_univ]

  -- 整理
  have : (univ.filter (fun x : α => x ∉ B)).card
        = Fintype.card α - (univ.filter (fun x : α => x ∈ B)).card := by
    -- `a = |α| - b` に直す
    exact Nat.eq_sub_of_add_eq' hsum.symm
  -- `card (inB) = card B`
  simpa [card_filter_in B]

omit [Fintype α] [DecidableEq α] in
lemma card_insert_if [DecidableEq α] (s : Finset α) (a : α) :
    (insert a s).card = if a ∈ s then s.card else s.card + 1 := by
  by_cases h : a ∈ s
  · -- a ∈ s ⇒ insert a s = s
    simp [insert_eq_of_mem, h]
  · -- a ∉ s ⇒ card(insert a s) = card s + 1
    rw [card_insert_of_notMem h]
    simp [h]

noncomputable def fromFun
  (B : Finset α) (AllA : Finset (Finset α))
  (uniqueDiff : ∀ {A : Finset α}, A ∈ AllA → (A \ B).card = 1)
  (t : {A // A ∈ AllA}) : {x // x ∉ B} :=
by
  classical
  rcases t with ⟨A,hA⟩
  have hx_exists : ∃ a, A \ B = {a} := Finset.card_eq_one.mp (uniqueDiff hA)
  let cc := Classical.choose hx_exists
  refine ⟨cc, ?_⟩
  -- 証明：choose ∉ B
  have hx : A \ B = {cc} := Classical.choose_spec hx_exists
  -- {choose} ⊆ A \ B なので choose ∉ B
  -- 具体的には choose ∈ A \ B、よって choose ∉ B
  --have hxmem : Classical.choose hx_exists ∈ A \ B := by
  have : cc ∈ A \ B := by
    -- `cc ∈ {cc}` を hx で書き換え
    simp [hx]-- using Finset.mem_singleton_self cc
  exact (Finset.mem_sdiff.mp this).2

omit [Fintype α] in
lemma fromFun_val
  (B : Finset α) (AllA : Finset (Finset α))
  (uniqueDiff : ∀ {A : Finset α}, A ∈ AllA → (A \ B).card = 1)
  (A : Finset α) (hA : A ∈ AllA) :
  ((fromFun B AllA uniqueDiff ⟨A,hA⟩ : {x // x ∉ B}) : α)
  = Classical.choose (Finset.card_eq_one.mp (uniqueDiff hA)) :=
by
  -- まさに def の定義通りなので反射律
  rfl

omit [Fintype α] [DecidableEq α] in
lemma card_subsets_size_k_containing_B
  [DecidableEq α] [Fintype α]
  {B : Finset α} {k : ℕ} (hk : k >= 1)
  (hB : B.card = k - 1) :
  ((powersetCard k (univ : Finset α)).filter (fun A : Finset α => B ⊆ A)).card
  = (univ.filter (fun x : α => x ∉ B)).card := by
  classical
  -- 記号
  set AllA : Finset (Finset α) :=
    (powersetCard k (univ : Finset α)).filter (fun A => B ⊆ A) with hAllA

  -- ドメインとコドメインを「部分型」の Fintype として扱い，明示的な全単射を作る
  -- D := {x | x ∉ B}
  let D := {x : α // x ∉ B}
  -- T := {A | A ⊆ univ ∧ |A|=k ∧ B ⊆ A} ・・・AllA のメンバーを部分型化したもの
  let T := {A : Finset α // A ∈ AllA}

  -- φ : D → T,  x ↦ insert x B
  -- まず `insert x B ∈ AllA` を示す
  have himage :
  ∀ {x : α}, x ∉ B → (insert x B : Finset α) ∈ AllA := by -- 修正点
    intro x hx
    have hcard : (insert x B : Finset α).card = k := by -- 修正点
      simp [card_insert_of_notMem hx, hB, Nat.sub_add_cancel hk]
    have hSubUniv : (insert x B : Finset α) ⊆ (univ : Finset α) := by -- 修正点
      exact subset_univ _
    have inPow : (insert x B : Finset α) ∈ powersetCard k (univ : Finset α) := by -- 修正点
      simp [mem_powersetCard, hSubUniv, hcard]
    have Bsubset : B ⊆ (insert x B : Finset α) := by exact subset_insert x B
    simpa [hAllA] using mem_filter.mpr ⟨inPow, Bsubset⟩
   /-
  have himage :
    ∀ {x : α}, x ∉ B → insert x B ∈ AllA := by
    intro x hx
    -- `insert x B ⊆ univ` は自明、`card = k` は `#B = k-1` と `x ∉ B` から
    have hcard : (insert x B).card = k := by
      -- card_insert_if で `x ∉ B` のとき `= B.card + 1`
      have := card_insert_if (B) x
      simp [hx, hB] at this
      simp_all only [ge_iff_le, not_false_eq_true, card_insert_of_notMem, Nat.sub_add_cancel, AllA]
    -/

    -- `insert x B` が `powersetCard k univ` に属し，かつ `B ⊆ insert x B`


  -- ψ : T → D を構成するため、A\B の濃度が 1 であることを示す
  have uniqueDiff :
    ∀ {A : Finset α}, A ∈ AllA → (A \ B).card = 1 := by
    intro A hA
    -- hA から `A.card = k` と `B ⊆ A` を取り出す
    have hA' : A ⊆ (univ : Finset α) ∧ A.card = k ∧ B ⊆ A := by
      -- hA : A ∈ (powersetCard k univ).filter (B ⊆ ·)
      rcases mem_filter.mp (by
        simp
        exact mem_filter.mp hA
      ) with ⟨hPow, hBsub⟩
      rcases (by simpa [mem_powersetCard] using hPow) with ⟨hAu, hAk⟩
      constructor
      · exact subset_univ A
      · constructor
        · exact rfl
        · exact hBsub
    have hBA : B ⊆ A := hA'.2.2
    -- `card (A \ B) = card A - card (A ∩ B)`。B ⊆ A なら `A ∩ B = B`
    -- よって = k - (k-1) = 1
    have hInter : (A ∩ B).card = B.card := by
      -- `A ∩ B = B` （B⊆A） から従う
      -- 具体的には `subset_antisymm` とカードで閉じるか，`by ext` で要素同値を示す
      apply le_antisymm
      · -- (A ∩ B) ⊆ B
        have : A ∩ B ⊆ B := by
          intro y; intro hy
          exact (mem_inter.mp hy).2
        exact card_le_card this
      · -- B ⊆ A ∩ B
        have : B ⊆ A ∩ B := by
          intro y hyB
          exact mem_inter_of_mem (hBA hyB) hyB
        -- ここでもカード比較で ≥ を得る
        exact card_le_card this

    -- `card_sdiff`： (A \ B).card = A.card - (A ∩ B).card
    -- ただし `B ⊆ A` が必要、今持っている
    have hsdiff : (A \ B).card = A.card - (A ∩ B).card := by
      simp [sdiff_eq_filter]
      rw [hInter]
      let cs := card_sdiff (by exact hBA)
      rw [←cs]
      rw [@filter_notMem_eq_sdiff]

    -- まとめ
    simp [hsdiff, hA'.2.1, hInter, hB]   -- `k - (k-1) = 1`
    exact Nat.sub_sub_self hk

  -- 逆写像 ψ: AllA → D を構成（A\B の唯一の元を返す）
  -- A\B の濃度が 1 なので、その唯一要素 x を `choose` で取り出せる
  /-
    have fromFun :
    T → D := by
    intro t
    rcases t with ⟨A, hA⟩
    have h1 : (A \ B).card = 1 := uniqueDiff hA

    -- ここを `rcases` ではなく Classical.choose で書く
    have hx_exists : ∃ a, A \ B = {a} := (Finset.card_eq_one.mp h1)
    let x : α := Classical.choose hx_exists
    have hx : A \ B = {x} := Classical.choose_spec hx_exists

    -- `hx : A \ B = {x}` から `x ∈ A ∧ x ∉ B` を取り出す
    have hxAB : x ∈ A ∧ x ∉ B := by
      have : x ∈ A \ B := by
        -- `x ∈ {x}` を hx で書き換え
        simp [hx]-- using Finset.mem_singleton_self x
      exact Finset.mem_sdiff.mp this

    -- 目標 `D = {x // x ∉ B}` の要素を返す
    exact ⟨x, hxAB.2⟩
  -/


  -- 順方向 φ と逆方向 ψ が互いに逆写像であることを示す
  /-have left_inv :
    ∀ x : D, fromFun ⟨Finset.insert x.1 B, by exact himage x.property⟩ = x := by
    intro x
    -- fromFun は (A\B) の唯一元を返す。A = insert x B のとき A\B = {x}
    -- よって fromFun φ(x) = x
    -- 具体的には上で使った `card_eq_one` の性質から一意性を利用
    -- 直接 `A \ B = {x}` を示す：
    have : (insert x.1 B \ B) = ({x.1} : Finset α) := by
      -- `insert x B \ B` は {x}（x∉B の仮定）
      ext y; constructor <;> intro hy
      · rcases mem_sdiff.mp hy with ⟨hyIns, hyNotB⟩
        -- y ∈ insert x B ⇒ y = x ∨ y ∈ B
        rcases mem_insert.mp hyIns with h | h
        · simp [h]
        · exact False.elim (hyNotB h)
      · -- y = x → y ∈ insert x B \ B
        simp
        simp_all only [mem_filter, mem_powersetCard, subset_univ, not_false_eq_true, card_insert_of_notMem, true_and,
          subset_insert, and_true, and_imp, mem_singleton, true_or, AllA]
        subst hy
        obtain ⟨val, property⟩ := x
        simp_all only [not_false_eq_true]
    -/

    -- 以上から ψ(φ x) = x
    -- ψ は「A\B の唯一要素」を返す関数なので，上の等式から従う
    -- 形式的には fromFun の定義展開と `card_eq_one` を使い同一性に落とすのが定石だが、
    -- ここでは `Subtype.ext` で第一成分の等号を示せばよい
    -- すなわち返ってくる元が `x.1` と一致することを言えば十分
    -- （詳細展開は省き、等式として返します）
    -- 実装を簡潔にするため `rfl` で済ませられるよう定義を整えています
    --show fromFun ⟨insert (↑x) B, ⋯⟩ = x

  have left_inv :
    ∀ x : D, fromFun B AllA uniqueDiff ⟨(insert x.1 B : Finset α), by exact himage x.property⟩ = x := by
    -- 修正点: `(insert ...)` に `: Finset α` を追加
    intro x
    simp only [fromFun]
    have h_diff : (insert x.val B : Finset α) \ B = {x.val} := by
      let fs := @Finset.sdiff_insert α _ B
      simp_all only [ge_iff_le, mem_filter, mem_powersetCard, subset_univ, not_false_eq_true, card_insert_of_notMem,
        Nat.sub_add_cancel, and_self, subset_insert, implies_true, true_and, and_imp, AllA]
      obtain ⟨val, property⟩ := x
      simp_all only [not_false_eq_true, insert_sdiff_cancel]

    --have h_choose_eq : Classical.choose (Finset.card_eq_one.mp (by rw [h_diff]; simp)) = x.val := by
    --  apply Classical.choose_unique
    --  simp [h_diff]
    --simp [h_choose_eq]

    --intro x
    -- 記号整理
    let A : Finset α := insert x.1 B
    have hA : A ∈ AllA := himage x.property
    -- `fromFun ⟨A,hA⟩` の第1成分は
    -- `Classical.choose (Finset.card_eq_one.mp (uniqueDiff hA))`
    -- で与えられる（A\B がちょうど1点集合）。
    -- 一方で `this : insert x.1 B \ B = {x.1}` があるので，
    -- choose される元は x.1 に等しいことが従う。
    apply Subtype.ext
    -- 目標： (fromFun ⟨A,hA⟩).1 = x.1
    --change (fromFun ⟨A, hA⟩).1 = xx.1
    -- fromFun を展開して「choose の中身」に落とす
    --unfold fromFun
    -- 以後，choose で取り出される元を「y」と名付けて扱う
    set hx_exists := (Finset.card_eq_one.mp (uniqueDiff hA)) with hxdef
    have hy : A \ B = {Classical.choose hx_exists} :=
      Classical.choose_spec hx_exists
    -- 既知：A = insert x.1 B に対して A\B = {x.1}
    have hIns : A \ B = ({x.1} : Finset α) := by
      -- あなたが直前で作っている補題 `this : insert (↑x) B \ B = {↑x}`
      -- を A の定義で書換えて使う
      rw [hy]
      dsimp [A] at hy
      simp at hy
      by_cases hxb : @Subtype.val α (fun x => x ∉ B) x ∈ B
      · -- 矛盾
        exfalso
        have ib: (insert (@Subtype.val α (fun x => x ∉ B) x) B) \ B = ∅ := by
          apply sdiff_eq_empty_iff_subset.mpr
          exact insert_subset hxb fun ⦃a⦄ a => a
        simp [ib] at hy
        have hcard := congrArg Finset.card hy
        -- これで 0 = 1 に簡約される
        have h01 : (0 : ℕ) = 1 := by
          simp
          simp at hcard


        -- 0 ≠ 1 の定理で矛盾
        exact Nat.zero_ne_one h01


      · have : (@Subtype.val α (fun x => x ∉ B) x) ∈ insert (@Subtype.val α (fun x => x ∉ B) x) B \ B := by
          simp
          exact hxb
        have :  A \ B = {@Subtype.val α (fun x => x ∉ B) x} := by
          exact insert_sdiff_cancel hxb
        let cc := Classical.choose_spec hx_exists
        rw [cc] at this
        exact this

    -- 2つの単集合が等しいので中の要素が等しい
    have hSingleton :
        {Classical.choose hx_exists} = ({x.1} : Finset α) := by
      -- hy : A\B = {choose …} から {choose …} = A\B
      -- これと hIns を合成
      simp [hIns]

    have hElem :
        Classical.choose hx_exists = x.1 :=
      Finset.singleton_injective hSingleton
    -- 以上で第1成分が一致

    have hsingle :
      ({Classical.choose hx_exists} : Finset α) = {((x : {x // x ∉ B}).1)} := by
      -- hy と hIns を合わせるだけ
      -- hy : A \ B = {choose},  hIns : A \ B = {x}
      -- よって {choose} = {x}
      -- （左右の書き換え順はお好みで）
      exact hSingleton

    have hchoose_eq : Classical.choose hx_exists = (x : {x // x ∉ B}).1 := by
      -- 単集合 membership で閉じる
      have : Classical.choose hx_exists ∈ ({Classical.choose hx_exists} : Finset α) := by simp
      -- 書き換え
      simpa [hsingle] using this

    -- もうゴールは値（coee）の等式なので Subtype.ext は使わずそのまま出す
    -- fromFun の値は choose という補題を使う
    have hval :
      (↑(fromFun B AllA uniqueDiff ⟨A,hA⟩) : α)
      = Classical.choose hx_exists :=
      fromFun_val B AllA uniqueDiff A hA

    -- 仕上げ
    -- ↑(fromFun …) = choose = ↑x
    calc
      (↑(fromFun B AllA uniqueDiff ⟨A,hA⟩) : α)
          = Classical.choose hx_exists := hval
      _   = (x : {x // x ∉ B}).1      := hchoose_eq

    /-

    congr
    have hchoose_eq : Classical.choose hx_exists = (x : D).1 := by
    -- {choose} = {x} を作る
      have hsingle_eq : ({Classical.choose hx_exists} : Finset α) = {((x : D).1)} := by
        -- hy と hIns を突き合わせるだけ
        -- hy : A \ B = {choose}, hIns : A \ B = {x}
        -- よって {choose} = {x}
        have := hy
        -- 書き換え順だけ合わせる
        calc
          ({Classical.choose hx_exists} : Finset α)
              = A \ B := by
                exact id (Eq.symm hy)
          _   = {((x : D).1)} := hIns
      -- 単集合に属することから要素等号へ
      have hc_mem : Classical.choose hx_exists ∈ ({((x : D).1)} : Finset α) := by
        -- choose ∈ {choose}
        have : Classical.choose hx_exists ∈ ({Classical.choose hx_exists} : Finset α) := by
          simp
        -- これを {x} へ書き換える
        simpa [hsingle_eq]
      -- 単集合の membership は等号と同値
      simpa using hc_mem

    -- ゴール: fromFun ⟨insert (↑x) B, ⋯⟩ = x
    -- Subtype の値成分が等しければ OK

    -/

  have right_inv :
    ∀ t : T, ⟨insert (fromFun B AllA uniqueDiff t).1 B, by exact himage (fromFun B AllA uniqueDiff t).2⟩ = t := by
    intro t
    rcases t with ⟨A, hA⟩
    -- さきほどの議論：`A \ B` の唯一元 x を取り、`A = insert x B` を示せばよい
    have h1 : (A \ B).card = 1 := uniqueDiff hA
    rcases card_eq_one.mp h1 with ⟨x, hx⟩
    have hxAB : x ∈ A ∧ x ∉ B := by
      have : x ∈ A \ B := by
        simp [hx]

      exact mem_sdiff.mp this
    -- 任意の y∈A は y∈B か y=x。したがって A ⊆ insert x B。
    have A_subset_insert : A ⊆ insert x B := by
      intro y hyA
      by_cases hyB : y ∈ B
      · exact subset_insert _ _ hyB
      · -- y ∈ A \ B = {x} ⇒ y = x
        have : y ∈ A \ B := by exact mem_sdiff.mpr ⟨hyA, hyB⟩
        have : y = x := by
          have : y ∈ ({x} : Finset α) := by simpa [hx] using this
          simpa using (mem_singleton.mp this)
        subst this
        exact mem_insert_self _ _
    -- 逆向き：insert x B ⊆ A は明らか（B⊆A と x∈A）
    have insert_subset_A : insert x B ⊆ A := by
      intro y hy
      rcases mem_insert.mp hy with hxy | hyB
      · simpa [hxy] using hxAB.1
      · simp_all only [mem_filter, mem_powersetCard, subset_univ, true_and, Subtype.forall,
        card_singleton, mem_insert, or_true, AllA, D]
        obtain ⟨left, right⟩ := hA
        obtain ⟨left_1, right_1⟩ := hxAB
        subst left
        apply right
        simp_all only

    -- 包含が両向きに成り立つので等号
    have : insert x B = A := by exact subset_antisymm insert_subset_A A_subset_insert
    -- したがって ψ の後に φ を適用すると元に戻る
    -- Subtype の等号は担保された「要素の等号」から従う
    -- （`Subtype.ext` を使うなら `simp` 一行でも可）
    -- ここでは等式を明示して返す
    -- 最後にサブタイプの証明成分は `himage` で自動的に合う
    --（Lean は `rfl` で閉じます）
    subst this
    simp_all only [true_and, Subtype.forall, card_singleton, not_false_eq_true, insert_sdiff_cancel,
      mem_insert, true_or, subset_refl, AllA, D, T]


  -- 上の left_inv, right_inv から全単射を得る
  let e : D ≃ T :=
  { toFun := fun x => ⟨insert x.1 B, himage x.2⟩
    , invFun := fun t => fromFun B AllA uniqueDiff t
    , left_inv := left_inv
    , right_inv := right_inv }

  -- Finite 型間同型のカード一致から，Finset のカード一致へ
  -- `Fintype.card_coe` で `T` や `D` のカードと対応する finset のカードが一致
  have hD : Fintype.card D = (univ.filter (fun x : α => x ∉ B)).card := by
    -- {x // x ∉ B} の Fintype.card は `univ.filter (·∉B)` のカード
    -- これは標準事実（要素はすべて有限）
    -- `Fintype.card_coe` を使う
    classical
    exact Fintype.card_subtype fun x => x ∉ B

  have hT : Fintype.card T = AllA.card := by
    -- こちらも同様に `Subtype` のカードはその母集合 finset のカード
    classical
    -- `AllA` の要素を Subtype にしたのが `T`
    exact Fintype.card_coe AllA

  -- 仕上げ：同型のカード一致 → 両 Finset のカード一致
  -- `Fintype.card_congr e` で `card D = card T`
  have := Fintype.card_congr e
  -- 置換して結論
  simpa [hAllA] using (by
    -- `card T = card D`
    have := Fintype.card_congr e
    -- 両辺を finset のカードに書き換える
    -- `hT` と `hD` を適用
    simp_all only [mem_filter, mem_powersetCard, subset_univ, true_and, Fintype.card_subtype_compl,
      Fintype.card_coe, AllA, D, T]
  )

omit [Fintype α] in
lemma card_image_sigma_to_prod_eq_sum_choose
  (F : Finset (Finset α)) (k : ℕ) :
  ( (image (fun p => (p.fst, p.snd))
           (F.filter (fun A => A.card = k) |>.sigma (fun A => powersetCard (k-1) A))).card
    =
    ∑ A ∈ (F.filter (fun A => A.card = k)),
      (A.card).choose (k - 1) ) := by
  classical
  -- 記号
  set Fk := (F.filter (fun A => A.card = k)) with hFk
  set S  := (Fk.sigma (fun A => powersetCard (k-1) A)) with hS
  set P  := (image (fun p => (p.fst, p.snd)) S) with hP

  -- 1) その写像は S 上で単射：card(image) = card(S)
  have inj_on : Set.InjOn (fun p : (Σ A : Finset α, Finset α) => (p.1, p.2)) S := by
    intro p1 hp1 p2 hp2 hpair
    -- p1 = ⟨A1, B1⟩, p2 = ⟨A2, B2⟩ と分解して、(A1,B1)=(A2,B2) から p1=p2
    rcases p1 with ⟨A1, B1⟩
    rcases p2 with ⟨A2, B2⟩
    -- 直積の等式から成分等式
    have hA : A1 = A2 := congrArg Prod.fst hpair
    have hB : B1 = B2 := congrArg Prod.snd hpair
    -- 置換して反射律
    cases hA; cases hB
    rfl

  have h_card_image : P.card = S.card := by
    -- card_image_of_injOn
    refine Finset.card_image_of_injOn ?fInj
    -- `image` 側の injOn は同じ写像を使うだけ
    intro p1 hp1 p2 hp2 hpair
    exact inj_on hp1 hp2 hpair

  -- 2) card_sigma と card_powersetCard で評価
  have h_card_sigma : S.card = ∑ A ∈ Fk, (powersetCard (k-1) A).card := by
    -- Finset.card_sigma: |Σ_{A∈Fk} fibers(A)| = ∑_A |fiber(A)|
    simp [S]

  have h_fiber_choose :
      ∀ {A : Finset α}, A ∈ Fk → (powersetCard (k-1) A).card = Nat.choose A.card (k-1) := by
    intro A hA
    simp

  -- 仕上げ：すべて代入
  -- 左辺の P を S に置換して card を落とし、右辺の fiber を choose に変換
  have : P.card = ∑ A ∈ Fk, (A.card).choose (k-1) := by
    calc
      P.card
          = S.card := by simpa [P] using h_card_image
      _   = ∑ A ∈ Fk, (powersetCard (k-1) A).card := h_card_sigma
      _   = ∑ A ∈ Fk, (A.card).choose (k-1) := by
            refine Finset.sum_congr rfl ?_
            intro A hA;
            simp

  simpa [P, S, Fk] using this

omit [Fintype α] in
lemma card_image_sigma_flip_eq_sum
  (F : Finset (Finset α)) (k : ℕ) :
  let Fk   := F.filter (fun A : Finset α => A.card = k)
  let Fkm1 := F.filter (fun B : Finset α => B.card = k - 1)
  let S    := Fkm1.sigma (fun B => Fk.filter (fun A => B ⊆ A))
  let Q    := S.image (fun p => (p.snd, p.fst))
  Q.card
  =
  ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
  classical
  intro Fk Fkm1 S Q
  -- まず、反転写像が `S` 上で単射
  have hInj : Set.InjOn (fun p : Finset α × Finset α => (p.2, p.1)) (S.image (fun s => (s.1, s.2)) : Finset (Finset α × Finset α)) := by
    intro p hp q hq hEq
    -- 成分ごとの等式に分解して p = q
    rcases p with ⟨A,B⟩
    rcases q with ⟨A',B'⟩
    -- hEq : (B,A) = (B',A')
    have h₁ : B = B' := congrArg Prod.fst hEq
    have h₂ : A = A' := congrArg Prod.snd hEq
    -- したがって元の順序のペアも等しい
    cases h₁; cases h₂; rfl

  -- 単射なので image のカードは元集合のカードに等しい
  have hCardImage : Q.card = S.card := by
    -- `card_image_of_injOn` を使う。`S.image f` のカード = `S` のカード（fが InjOn）
    let fc := Finset.card_image_of_injOn (s := S) (f := fun ⟨A, B⟩ => (B, A)) ?_
    exact fc
    convert hInj
    simp
    constructor
    · exact fun a => Set.InjOn.image_of_comp a
    · intro h
      simp_all only [coe_image, coe_sigma, coe_filter, mem_filter, S, Fkm1, Fk]
      intro x a x₂ a_1 a_2
      simp_all only [Set.mem_sigma_iff, Set.mem_setOf_eq, Prod.mk.injEq, and_self]
      obtain ⟨fst, snd⟩ := x
      obtain ⟨fst_1, snd_1⟩ := x₂
      obtain ⟨left, right⟩ := a_1
      obtain ⟨left_1, right_1⟩ := a_2
      obtain ⟨left, right_2⟩ := left
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_2, right_3⟩ := left_2
      subst left_1 right_3 right_1
      simp_all only

  -- `card_sigma` で `S.card = ∑_{B∈Fkm1} |{A∈Fk | B⊆A}|`
  have hSigma : S.card = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
    -- 標準の `card_sigma`
    simp_all only [card_sigma, Q, S, Fkm1, Fk]

  -- 連結して結論
  exact hCardImage.trans hSigma

lemma card_P_right_eq
  (F : Finset (Finset α)) (hI : IdealExceptTop F)
  (k : ℕ) (hk : 1 ≤ k) (hk_top : k ≤ Fintype.card α - 1) :
  let Fk   := F.filter (fun A => A.card = k)
  let Fkm1 := F.filter (fun B => B.card = k-1)
  let P    := (Fk.sigma (fun A => powersetCard (k-1) A)).image (fun p => (p.1, p.2))
  P.card = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
  classical
  intro Fk Fkm1 P
  -- P.card = S.card = （A 固定の総和）
  have hL : P.card = ∑ A ∈ Fk, (A.card).choose (k-1) := by
    -- 前補題を `rw` で合わせる
    have := card_image_sigma_to_prod_eq_sum_choose (F) (k)
    -- 左辺の image の引数が `Fk` で書かれていないので、定義で合わせる
    -- 今回の P, Fk の定義に合わせる書換
    -- 略：あなたのファイル内の `cis` と同じ要領で `rw` を当てて整形してください
    -- （以下は流れだけ）
    simp_all only [P, Fk]

  -- 一方、右側：B 側の sigma にも同じだけ要素がある（真の同数性）
  -- これは (A,B) ↦ (B,A) の全単射を作れば従う：
  have hR : ∑ A ∈ Fk, (A.card).choose (k-1)
           = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
    -- `card_sigma` を B 側でも使うには、S と T の間に明示的な Finset 同型を作る。
    -- 具体的には S := Fk.sigma (λ A, powersetCard (k-1) A)
    --            T := Fkm1.sigma (λ B, Fk.filter (λ A, B ⊆ A))
    -- で `φ(A,B) = (B,A)`、逆 `ψ(B,A) = (A,B)` が well-defined であることを
    -- （ideal で B ∈ F を保証、`mem_powersetCard_iff` で B⊆A と |B|=k-1 を両向きに使う）
    -- チェックしてから `card_sigma` を両側に適用して等式化します。
    have hP_eq_right :
      #P = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
      -- Q を作る
      let Q :=
        ((Fkm1.sigma (fun B => Fk.filter (fun A => B ⊆ A))).image (fun p => (p.2, p.1)))
      -- P = Q を示す（説明通り：mem_powersetCard_iff と hI.downward を使う）
      have hPQ : P = Q := by
        -- `ext` で (A,B) ごとに両方向の ↔ を証明
        -- 左向き：P の定義 ⇒ B⊆A, |B|=k-1, A∈Fk ⇒（ideal性）B∈Fkm1 ⇒ Q
        -- 右向き：Q の定義 ⇒ B∈Fkm1, A∈Fk, B⊆A ⇒（|A|=k, |B|=k-1）⇒ P
        -- ここはやや長いのであなたの補題をそのまま展開してください
        -- 最終行だけ：
        ext p; constructor
        · intro hp
          dsimp [P, Q] at hp
          dsimp [Q]
          simp at hp
          simp
          obtain ⟨A, B, hAinFk, hBinPow, hBsubA, heq⟩ := hp
          use B
          use A
          simp
          constructor
          · dsimp [Fkm1]
            -- B ∈ F, |B|=k-1
            have hBcard : B.card = k-1 := by
              -- mem_powersetCard_iff で B⊆A と |A|=k から従う
              simp_all only [mem_filter, P, Fk]
            simp [hBcard]
            have hAF : A ∈ F ∧ A.card = k := by
  -- Fk = {A ∈ F | A.card = k} なので定義を開くだけ
              have hA : A ∈ Fk := hAinFk.left
              -- Fk の定義: Fk := F.filter (fun A => A.card = k)
              -- よって A∈F ∧ A.card = k
              simpa [Fk] using hA

            have hAinF : A ∈ F := hAF.left
            have hAcard : A.card = k := hAF.right
            have hBsubset : B ⊆ A := hAinFk.right.left

            -- A ≠ univ を示す（さもなくば A.card = |α| となり k = |α| と矛盾）
            have hA_ne_univ : A ≠ (Finset.univ : Finset α) := by
              intro hAu
              -- A = univ なら A.card = Fintype.card α
              have hAc_eq : A.card = Fintype.card α := by
                simp [hAu]
              -- hAcard : A.card = k なので k = |α|
              have hk_eq : k = Fintype.card α := by
                -- k = A.card = |α|
                calc
                  k = A.card := by simpa using hAcard.symm
                  _ = Fintype.card α := hAc_eq
              -- hk_top : k ≤ |α| - 1 より (k+1) ≤ |α|
              have hk_succ_le : k.succ ≤ Fintype.card α := by
                -- k ≤ |α| - 1 ⇒ k+1 ≤ (|α|-1)+1 = |α|
                let nc := Nat.succ_le_succ hk_top
                subst hAu hAcard
                simp_all only [card_univ, mem_filter, and_self, subset_univ, true_and, and_true, Nat.succ_eq_add_one,
                  add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, P, Fk]
                rw [← hAinFk] at nc
                simp_all only [card_univ, Nat.succ_eq_add_one, Nat.sub_add_cancel, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
                  one_ne_zero]
              -- しかし hk_eq から k.succ = |α|.succ なので |α|.succ ≤ |α| の矛盾
              have : (Fintype.card α).succ ≤ Fintype.card α := by
                simp
                subst hAu hAcard
                simp_all only [card_univ, Nat.succ_eq_add_one, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, P, Fk]

              exact Nat.not_succ_le_self _ this

            -- 下閉（univ を除く）を適用して B ∈ F
            have hB_in_F : B ∈ F :=
              hI.downward hAinF hA_ne_univ hBsubset

            -- これでゴール `B ∈ F` が得られます。
            exact hB_in_F
          · constructor
            · exact hAinFk.1
            · exact hAinFk.2.1
        · intro hq
          dsimp [P, Q] at hq
          dsimp [P]
          simp at hq
          simp
          obtain ⟨B, A, hBinFkm1, hAinFk, hBsubA, heq⟩ := hq
          use A
          use B
          constructor
          · constructor
            · exact hBinFkm1.2.1
            · constructor
              · exact hBinFkm1.2.2
              · have hB_in_F_and_card : B ∈ F ∧ B.card = k - 1 := by
                  have hB_in : B ∈ Fkm1 := hBinFkm1.left
                  -- フィルタのメンバーシップを展開
                  simpa [Fkm1] using hB_in
                -- 目的は #B = k - 1
                exact hB_in_F_and_card.right
          · exact rfl

      -- Q のカードを `card_sigma` → `sum`、`image` の単射性で評価

      have hQ :
        #Q = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
        -- card of sigma is sum of fiber cards
        -- image by (fun p => (p.2, p.1)) preserves card (単射)：
        -- `Finset.card_image_iff` or `Finset.card_image_of_injOn` を使用
        dsimp [Q]
        dsimp [Fkm1]
        exact card_image_sigma_flip_eq_sum F k

      -- P=Q と Q のカード式から P のカード式を得る
      have : #P = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
        -- `rw [hPQ, hQ]`
        have t := hQ
        -- まず P=Q で左を置換
        --   `rw [hPQ]` は #P を #Q に変える
        -- 次に #Q の評価 hQ を適用
        --   `exact t`
        -- （simpa は使わない）
        rw [hPQ]
        exact t

      exact
        by
          -- 左：hL で #P を置換、右：上で得た式で #P を置換して等式連鎖
          -- 「両辺とも #P に等しい」から等式
          -- 1) 左辺を #P に： `have eqL : ∑ A∈Fk … = #P := by exact hL.symm`
          have eqL : ∑ A ∈ Fk, (#A).choose (k - 1) = #P := by
            -- `hL : #P = ∑ A∈Fk …` の左右反転
            exact Eq.symm hL
          -- 2) 右辺を #P に： `have eqR : #P = ∑ B∈Fkm1 … := by exact this`
          have eqR : #P = ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
            exact this
          -- 3) 連結：左 = #P = 右
          --    まず左 = #P を使い、次に #P = 右を使う
          --    `rw [eqL, eqR]`
          -- （simpa を使わずに書換）
          simp_all only [P, Fk, Q, Fkm1]

    simp_all only [P, Fk, Fkm1]

  -- 連結：P.card = 左総和 = 右総和
  exact Eq.trans hL hR

omit [Fintype α] [DecidableEq α] in
lemma double_count_main_ineq_left
  [Fintype α] [DecidableEq α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F)
  (k : ℕ) (hk : 1 ≤ k) (hk_top : k ≤ Fintype.card α - 1) :
  k * aCount F k ≤ (Fintype.card α - k + 1) * aCount F (k-1) := by
  classical
  set n := Fintype.card α with hn

  -- F の k 層 / (k-1) 層
  let Fk   : Finset (Finset α) := F.filter (fun A => A.card = k)
  let Fkm1 : Finset (Finset α) := F.filter (fun B => B.card = (k-1))

  have hFk_mem : ∀ {A}, A ∈ Fk → A ∈ F ∧ A.card = k := by
    intro A hA; simpa [Fk] using hA
  have hFkm1_mem : ∀ {B}, B ∈ Fkm1 → B ∈ F ∧ B.card = k-1 := by
    intro B hB; simpa [Fkm1] using hB

  -- 対象のペア集合：P := Σ A∈Fk, (A の (k-1)-部分集合)
  let P : Finset ((Finset α) × (Finset α)) :=
    (Fk.sigma (fun A => powersetCard (k-1) A)).image (fun p => (p.1, p.2))

  -- A 側で数える：|fiber| = choose k (k-1) = k
  have card_P_left :
      P.card = k * aCount F k := by
    -- Σ のカード＝ fiber のカード和
    have hσ := Finset.card_sigma (s := Fk) (t := fun A => powersetCard (k-1) A)
    -- 各 fiber の大きさ＝ choose (A.card) (k-1) = choose k (k-1) = k
    have fiber_eq :
      ∀ {A}, A ∈ Fk → (powersetCard (k-1) A).card = k := by
      intro A hA
      rcases hFk_mem hA with ⟨_, hAk⟩
      -- card of powersetCard
      have h := (Finset.card_powersetCard (s := A) (n := k-1))
      -- h : (powersetCard (k-1) A).card = Nat.choose A.card (k-1)
      -- A.card = k に書換え
      have : (powersetCard (k-1) A).card = Nat.choose k (k-1) := by
        simp [hAk]

      -- choose k (k-1) = k
      -- `Nat.choose_succ_self_right (k-1)` : choose ((k-1)+1) (k-1) = (k-1)+1
      have hk1 : Nat.choose k (k-1) = k := by
        -- (k-1)+1 = k
        have := Nat.choose_succ_self_right (k-1)
        -- this : Nat.choose ((k-1)+1) (k-1) = (k-1)+1
        subst hAk
        simp_all only [mem_filter, and_self, one_le_card, implies_true, card_sigma, card_powersetCard, Nat.choose_symm,
          Nat.choose_one_right, Nat.sub_add_cancel, n, Fk, Fkm1]


      -- 連結
      exact this.trans hk1
    -- 和を「定数 k」の和に置換
    have h₁ :
      ∑ A ∈ Fk, (powersetCard (k-1) A).card
        = ∑ A ∈ Fk, k := by
      refine Finset.sum_congr rfl ?_
      intro A hA
      exact congrArg id (fiber_eq hA)
    -- ∑ A∈Fk k = k * |Fk|
    have h₂ : ∑ A ∈ Fk, k = k * Fk.card := by
      classical
      -- sum_const_nat：制限和の定数は c * |s|
      -- `simp` で落ちますが、展開して書きます
      -- （`Finset.card` と合わせて機械的に閉じる）
      --have := Finset.sum_const_nat k (s := Fk)
      -- `sum_const_nat` の定義展開を避け、既知として扱うなら：
      -- `simp [Finset.sum_const_nat]`
      -- ここでは `by` で置換
      simp_all only [mem_filter, and_self, implies_true, card_sigma, sum_const, smul_eq_mul, card_powersetCard,
       Nat.choose_symm, Nat.choose_one_right, n, Fk, Fkm1]
      rw [mul_comm]

    -- Σ のカードに等式を代入
    -- `aCount F k = Fk.card` は定義
    have : P.card = (∑ A ∈ Fk, (powersetCard (k-1) A).card) := by
      simp [P]
      show #(image (fun p => (p.fst, p.snd)) (Fk.sigma fun A => powersetCard (k - 1) A)) = ∑ x ∈ Fk, (#x).choose (k - 1)
      exact card_image_sigma_to_prod_eq_sum_choose F k
    calc
      P.card
          = (∑ A ∈ Fk, (powersetCard (k-1) A).card) := this
      _   = (∑ A ∈ Fk, k) := h₁
      _   = k * Fk.card := h₂
      _   = k * aCount F k := by rfl

  -- B 側で上から抑える：各 B（|B|=k-1）に対し fiber ≤ |univ\B| = n - (k-1)
  have fiber_le :
    ∀ {B}, B ∈ Fkm1 →
      (Fk.filter (fun A => B ⊆ A)).card ≤ (n - k + 1) := by
    intro B hB
    rcases hFkm1_mem hB with ⟨hBF, hBcard⟩
    -- A を「全候補」から上から抑える
    -- 候補集合： AllA = {A | A⊆univ, |A|=k, B⊆A}（F 無視の上界）
    let AllA : Finset (Finset α) :=
      (powersetCard k (univ : Finset α)).filter (fun A => B ⊆ A)
    -- 包含：Fk.filter (B⊆A) ⊆ AllA
    have subset_All :
      (Fk.filter (fun A => B ⊆ A)) ⊆ AllA := by
      intro A hA
      -- hA : A∈F ∧ A.card=k ∧ B⊆A
      have hAf : A ∈ F ∧ A.card = k := by
        -- `A ∈ Fk` から
        have hAk : A ∈ Fk := by
          -- `mem_filter` から取り出す
          have := hA
          -- `hA : A ∈ Fk ∧ B ⊆ A`
          have hA' := (mem_filter.mp hA).left
          exact hA'
        have := hFk_mem hAk
        exact this
      have hBA : B ⊆ A := by
        have : A ∈ Fk ∧ B ⊆ A := mem_filter.mp hA
        exact this.right
      -- `A ⊆ univ` は自明，`A.card = k` は hAf
      have Ain : A ∈ powersetCard k (univ : Finset α) := by
        have : A ⊆ (univ : Finset α) := by
          intro x hx; exact mem_univ _
        have : A ⊆ (univ : Finset α) ∧ A.card = k := And.intro this hAf.right
        simpa [mem_powersetCard_iff] using this
      -- AllA の条件を満たす
      have : A ∈ (powersetCard k (univ : Finset α)).filter (fun A => B ⊆ A) := by
        -- `mem_filter` で両条件
        have : A ∈ powersetCard k (univ : Finset α) ∧ B ⊆ A := And.intro Ain hBA
        simpa [AllA, mem_filter] using this
      exact this
    -- したがってカードは AllA.card で上から抑えられる
    have le1 : (Fk.filter (fun A => B ⊆ A)).card ≤ AllA.card :=
      card_le_card subset_All
    -- AllA は挿入写像 `x ↦ insert x B (x ∉ B)` の像に入る（単射像のカード ≤ 候補数）
    -- 候補数は `|{x | x ∉ B}| = n - (k-1)`
    -- 具体に `AllA.card ≤ (univ.filter (·∉B)).card`
    have card_AllA_le :
      AllA.card ≤ (univ.filter (fun x : α => x ∉ B)).card := by
      -- 単射像の上界：`card_image_of_injOn`
      -- 写像 φ : {x | x∉B} → AllA,  φ(x) = insert x B
      -- まず φ(x) が AllA に入ることを確認
      have himage :
        ∀ {x}, x ∈ (univ.filter (fun x : α => x ∉ B)) →
          insert x B ∈ AllA := by
        intro x hx
        have hxU : x ∈ (univ : Finset α) := by
          have : x ∈ (univ.filter (fun x : α => x ∉ B)) := hx
          exact mem_univ x
        have hxNot : x ∉ B := by
          have : x ∈ (univ.filter (fun x : α => x ∉ B)) := hx
          exact (by
            have := (mem_filter.mp this).right
            simpa using this)
        -- `insert x B` は univ の部分集合，サイズは (k-1)+1 = k，かつ B⊆insert x B
        have hAin : insert x B ⊆ (univ : Finset α) := by
          intro y hy; exact mem_univ _
        have hAcard : (insert x B).card = k := by
          -- |B|=k-1 なので |insert x B| = k（x∉B）
          have : B.card = k - 1 := by simpa using hBcard
          -- `card_insert` を使う（`x ∉ B`）
          have := card_insert_if (s := B) (a := x)
          -- `card_insert_if` : (insert x B).card = if x∈B then B.card else B.card+1
          -- 今回は `x∉B` なので = B.card+1 = (k-1)+1 = k
          --have hxB : Decidable (x ∈ B) := Classical.decEq _
          classical
          have : (insert x B).card = B.card + 1 := by
            -- 直接：`by` で分岐してもよいが、今は `bycases`
            -- ここでは既知 hxNot を使う
            have : x ∉ B := hxNot
            -- `card_insert` の標準版
            simp [this]-- using card_insert_if (s := B) (a := x)

          calc
            (insert x B).card = B.card + 1 := this
            _ = (k - 1) + 1 := by simp [hBcard]
            _ = k := Nat.sub_add_cancel hk
        have hBsub : B ⊆ insert x B := by
          -- `subset_insert` の標準補題
          exact subset_insert _ _
        -- まとめて AllA の条件を満たす
        have : insert x B ∈ powersetCard k (univ : Finset α) := by
          have : insert x B ⊆ (univ : Finset α) ∧ (insert x B).card = k :=
            And.intro hAin hAcard
          simpa [mem_powersetCard_iff] using this
        -- filter の条件も満たす
        have : insert x B ∈ AllA := by
          have : insert x B ∈ powersetCard k (univ : Finset α) ∧ B ⊆ insert x B :=
            And.intro this hBsub
          simpa [AllA, mem_filter] using this
        exact this
      -- φ の単射性
      have hInj : Set.InjOn (fun x : α => insert x B) {x | x ∉ B} :=
        injOn_insert B
      -- `image` による上界
      -- `AllA` は φ の像の部分集合（実は等しいが、「≤」評価で十分）
      -- したがって `AllA.card ≤ (# {x|x∉B})`
      -- まず φ の像集合を作る
      --have subImage :
      --  AllA ⊆ ( (univ.filter (fun x : α => x ∉ B)).image
      --              (Embedding.subtype ?dec).trans ?iEmb ) := by
        -- 実は AllA = {insert x B | x ∉ B} を使いたいが、
        -- ここは上界評価だけ使うので省略しても成立します。
        -- 代わりに、`card_le_of_subset` を避け、`card_image_of_injOn` を直接使う：
        --   AllA.card ≤ (#候補) をそのまま返す
        -- ここはダミー（実際には不要）ので `exact subset_rfl`
      --  exact subset_rfl
      -- 直接 `card_AllA ≤ (#候補)` を返す（像の方が多い or 同数なので）
      -- `card_image_of_injOn` を使うには、`AllA` 自身が像である必要があるが、
      -- 今は「上界」でよいので，下のように単純化する：
      -- `AllA.card ≤ (# {x|x∉B})` は、像が {insert x B | x∉B} であり、
      -- それが候補数に等しいことから従う。
      -- ここでは長い同型の証明を避け、直接この不等式を採用します。
      -- 形式的には、次の補題を使うと楽です：
      --   `AllA.card ≤ (univ.filter (·∉B)).card`（構成ずみ）
      -- したがって：
      apply le_of_le_of_eq (le_of_eq rfl)
      exact card_subsets_size_k_containing_B hk hBcard
    -- 候補数の評価
    have cand :
      (univ.filter (fun x : α => x ∉ B)).card = n - (k - 1) := by
      -- `= |α| - |B|` かつ `|B| = k-1`
      have := card_filter_notin (B := B)
      -- 書き換え
      have hB : B.card = k - 1 := by simpa using hBcard
      calc
        (univ.filter (fun x : α => x ∉ B)).card
            = Fintype.card α - B.card := this
        _   = n - (k - 1) := by
              simp [hn, hB]
    -- 以上を連鎖
    have : (Fk.filter (fun A => B ⊆ A)).card ≤ n - (k - 1) := by
      apply le_trans le1
      exact le_of_le_of_eq card_AllA_le cand
    -- `n - (k-1) = n - k + 1`
    have nshift : n - (k - 1) = n - k + 1 := by
      have := Nat.sub_sub n k 1
      -- n - (k - 1) = n - k + 1  は標準の書換
      -- `by omega` 的にも出せるが、等式連鎖で：
      -- n - (k - 1) = n - k + 1
      -- （実用上は `Nat.succ_sub` 経由でも OK）
      -- ここでは `tsub_eq` 系の等式が必要ない安全な書換として採用
      have hkpos : 1 ≤ k := hk
      -- n - (k-1) = (n - k) + 1
      -- 直に：
      exact by
        -- `Nat` の減算は安全に扱うため、標準等式を使わずに書換
        -- `Nat.sub_add_eq_add_sub` 等を通してもよい
        -- ここでは完成形だけ与える
        -- （環境差があれば `by decide` で数式を壊さないよう注意）
        -- 最終形：
        -- (数学的には自明)
        exact (by
          have : n - (k - 1) = n - k + 1 := by
            -- succ-sub の一歩版
            -- n - (k-1) = (n+1) - k = (n - k) + 1
            have : (n + 1) - k = n - k + 1 := by
              simp_all only [mem_filter, and_self, implies_true, n, Fk, Fkm1, P, AllA]
              omega

            -- さらに (n - (k-1)) = (n+1) - k
            -- この等式は標準
            -- ここでは最終形だけ返す
            simp_all only [mem_filter, and_self, implies_true, n, Fk, Fkm1, P, AllA]
            omega

          exact this)
    -- 仕上げ
    simpa [nshift] using this

  -- B 側で和をとって上界に
  have card_P_right_le :
      P.card ≤ (n - k + 1) * aCount F (k-1) := by
    -- まず fiber の和で抑える
    have : P.card ≤ ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
      -- `P = Σ A∈Fk, (k-1)-subs of A` を `Σ B∈Fkm1, {A∈Fk | B⊆A}` に埋め込む
      -- 形式化は長いので、ここは「各 fiber を数えると同数かそれ以下」から
      -- 上限としてこの和を採用する（厳密には `card_le_of_subset` ベース）
      -- ここは簡潔に「≤」を受け入れます
      -- （必要なら、具体的な埋め込み `(A,B) ↦ (B,A)` の membership を書いて閉じられます）
      apply le_trans (le_of_eq (by rfl))
      dsimp [P]
      show #(image (fun p => (p.fst, p.snd)) (Fk.sigma fun A => powersetCard (k - 1) A)) ≤ ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A})
      let cis := card_image_sigma_to_prod_eq_sum_choose F k
      rw [cis]
      have hc : P.card = ∑ A ∈ Fk, (A.card).choose (k - 1) := by
        -- あなたの `cis` は `{A ∈ F | #A = k}` 形式になっていると思うので
        -- Fk = {A ∈ F | A.card = k}, P = image ... の定義を開いて合わせます
        -- すでに `cis` がその形なら `simpa [Fk, P] using cis` でOKです
        simpa [Fk, P] using cis

      -- 次に、右辺の {A ∈ Fk | B ⊆ A} を filter 形式にあわせる
      have hRewrite :
        (∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}))
        = (∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card) := by
        -- 内側の集合の定義を展開して同型であることを言うだけ
        -- `by ext` ＋ `simp [Fk]` でも、`rfl` でもよい実装状況が多いです
        -- ここでは `rfl` が通る定義にしてあると仮定：
        rfl

      -- `card_P_right_le : P.card ≤ ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card`
      have hPairsBound := by exact α--card_P_right_le

      -- 仕上げ：左辺を hc で、右辺を hRewrite で置換
      -- 目標の形へ `simpa` で落とす
      have : ∑ A ∈ Fk, (A.card).choose (k - 1)
            ≤ ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
        have h' :
          ∑ A ∈ Fk, (A.card).choose (k - 1)
            ≤ ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
    -- card_P_right_le : P.card ≤ …

          have h := @card_P_right_eq α
           -- 左辺 P.card を hc で置換
            -- （`simpa [hc] using h` の代わりに rw + exact を使う）
            -- h : P.card ≤ …
            -- rw [hc] at h で h : (∑ …) ≤ …
          have hR : #P = ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}) :=
            h (F := F) hI k hk hk_top

          -- 等式 #P = #P から ≤ を作り、それを左右とも書き換えて
          -- 目標の形に変形していきます（simpa 不使用）
          have base : #P ≤ #P := le_of_eq rfl

          -- 左辺 #P を「左側和」に、右辺 #P を「右側和」に置換
          -- hc : #P = ∑ A∈Fk …
          -- hR : #P = ∑ B∈Fkm1 …
          -- よって ←hc で左を、hR で右をそれぞれ書き換える
          have goal' :
            ∑ A ∈ Fk, (#A).choose (k - 1) ≤ ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}) := by
            -- base : #P ≤ #P を目標の形に変える
            -- 左側：#P → (∑ A∈Fk …) は「#P = …」の左右反転 ←hc を使う
            -- 右側：#P → (∑ B∈Fkm1 …) は hR をそのまま使う
            have h₀ : ∑ A ∈ Fk, (#A).choose (k - 1) ≤ #P := by
              -- base を左だけ ←hc で書き換える
              -- base : #P ≤ #P
              -- ←hc : #P = (∑ A∈Fk …)
              -- したがって、rw [←hc] を base の左側に適用
              -- いきなり両辺を書き換えるのは煩雑なので、中間項を作らず直接書き換えます：
              have t := base
              -- 左辺を書き換え
              -- （`rw [←hc] at t` は左右の #P のうち「左側」を目的に合わせます）
              -- ただし `rw` はすべての出現箇所を置換するので、段階を分けるのが安全です。
              -- ここは一旦 t を返します（次のステップで両辺まとめて書き換えます）。
              exact Nat.le_of_eq (id (Eq.symm cis))
            -- 両辺をいっぺんに置換する方が簡潔です：
            have t := base
            -- 左の #P を ←hc で置換
            -- 右の #P を hR で置換
            -- 2回の `rw` を順に当てます
            -- 先に左（←hc）、次に右（hR）
            -- 注意：`rw` は等式をゴール全体に適用するので、順番をこのように固定します
            -- （片側だけに適用したい時は `change` 等を併用しますが、ここでは順に当ててOK）
            -- まず左辺：#P → (∑ A∈Fk …)
            --   等式の向きを合わせるために ←hc を使います
            have : ∑ A ∈ Fk, (#A).choose (k - 1) ≤ #P := by
              -- base をコピーし、左を置換
              have u := base
              -- 左を ←hc で置換
              --   (#P) ＝ (∑ A∈Fk …) なので、←hc : (#P) = (∑ …)
              --   これで u の左辺が目標の左辺になります
              -- Lean ではゴールに対しての `rw` をしたいので、u を使わずに
              -- 直接 t を書き換えていきます。ここでは説明を簡潔にするため
              -- 結論だけ返し、次のステップで両辺を同時に置換します。
              apply le_of_eq
              exact id (Eq.symm cis)
            -- ここからは実際に目標を書き換えるやり方（短く仕上げ）：
            -- ゴールそのものを置換して「#P ≤ #P」に変形し、それを `le_of_eq rfl`
            -- で閉じます。
            -- つまり、ゴールに対して `rw [hc, hR]` を当てる向きに気をつけて（`hc` は左辺、`hR` は右辺に）
            -- 変形します。
            -- 具体的には、`have : ∑ A∈Fk … ≤ ∑ B∈Fkm1 … := by` を作り、
            -- その中で `have z : #P ≤ #P := le_of_eq rfl;` を作ってから
            -- `rw [hc] at z; rw [hR] at z; exact z` とします。
            have z : #P ≤ #P := le_of_eq rfl
            -- 左辺の書換：#P を (∑ A∈Fk …) に
            --   等式 hc : #P = (∑ A∈Fk …) を使うと、
            --   目標「(∑ A∈Fk …) ≤ …」にしたいので、z の **左側** を `hc` の **正向き** で置換します。
            --   そのためには `rw [hc] at z` とします（この一回で z の両辺の #P が全部置換される点に注意）。
            --   なので、順番を工夫して右辺を最後に整えます。
            -- いったん右辺の置換を先にやりましょう：右を `hR` の「逆向き」で #P に戻す必要はありません。
            -- むしろ `z` は #P ≤ #P なので、**左側**を `hc` で「和」に、**右側**を `hR` で「右側の和」に変えたい。
            -- したがって「左を hc の逆向き」「右を hR の正向き」ではなく、
            -- `z` に対し **左を ←hc**、**右を hR** で一発で目標に一致します。
            -- しかし `rw` は式中の全出現を書き換えるため、段階を分けます：

            -- まず左を ←hc で置換
            have z1 : ∑ A ∈ Fk, (#A).choose (k - 1) ≤ #P := by
              -- start from base
              have u := base
              -- ←hc を「左辺」にだけ当てたいのですが、`rw` は両辺に当たります。
              -- そこで、先に右側を hR で置換してから左を処理するか、
              -- 逆順に 2 つの補助値を作って繋げます。
              -- ここでは最終的な結論だけ返します（下の最終ステップで一括して変形します）。
              apply le_of_eq
              exact id (Eq.symm cis)

            -- 最終：一括で変形して終了
            have zfinal : ∑ A ∈ Fk, (#A).choose (k - 1)
                        ≤ ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}) := by
              -- z : #P ≤ #P
              -- 左を ←hc、右を hR で置換
              -- これを実現するために `have t := z;` → `rw [←hc] at t; rw [hR] at t; exact t`
              have t := z
              -- 左：#P → (∑ A∈Fk …)
              -- `←hc : (∑ A∈Fk …) = #P` なので、#P を左に残しておきたいときは正向き、
              -- 今回は #P を「和」にしたいので **←hc を左辺に適用**します。
              -- `rw` は両辺に当たるため、`←hc` の向きに注意してください。
              -- ここでは段階をまとめて、以下のように 2 回の書換を順に当てます：
              -- 1) 左を ←hc で置換
              -- 2) 右を  hR  で置換
              -- 実コード：
              --   rw [←hc] at t
              --   rw [hR]  at t
              --   exact t
              -- （`simpa` は使用しません）
              simp_all only [mem_filter, and_self, implies_true, and_imp, le_refl, n, Fk, Fkm1, P]

            exact zfinal
          --rw [hc] at h
          --exact h
          exact goal'

        -- 2) 右辺を {A ∈ Fk | B ⊆ A} の記法へそろえるための等式
        have hR :
            ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card
              = ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}) := by
          -- 各項で `rfl`（filter のカードと内包表記の Finset が定義上一致）
          apply Finset.sum_congr rfl
          intro B hB
          rfl

        -- 3) h' の右辺を hR で置換して結論
        have h'' :
            ∑ A ∈ Fk, (A.card).choose (k - 1)
              ≤ ∑ B ∈ Fkm1, #({A ∈ Fk | B ⊆ A}) := by
          -- `simpa [hR] using h'` の代替：rw を使ってから exact
          have htmp := h'
          rw [hR] at htmp
          exact htmp

        -- 目標に一致
        exact h''




      -- さらに `{A ∈ Fk | B ⊆ A}` 形式に戻すなら：
      simp
      exact this



    -- 各 B で ≤ n - k + 1
    have : ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card
           ≤ ∑ B ∈ Fkm1, (n - k + 1) := by
      refine sum_le_sum ?H
      intro B hB
      exact fiber_le hB
    -- 右辺は定数和
    have rhs : (∑ _ ∈ Fkm1, (n - k + 1)) = (n - k + 1) * Fkm1.card := by
      classical
      -- `sum_const_nat`
      simp --using (Finset.sum_const_nat (n - k + 1) (s := Fkm1))
      simp_all only [mem_filter, and_self, implies_true, and_imp, sum_const, smul_eq_mul, n, Fk, Fkm1, P]
      ring

    -- 連鎖
    have : P.card ≤ (n - k + 1) * Fkm1.card :=
      le_trans ‹_› (by simpa [rhs])
    -- `aCount F (k-1) = Fkm1.card`
    simpa [Fkm1, aCount] using this

  -- 左右結合
  -- 左：k * aCount F k，右：(n - k + 1) * aCount F (k-1)
  have : k * aCount F k ≤ (n - k + 1) * aCount F (k-1) := by
    -- `P.card = 左辺` かつ `P.card ≤ 右辺`
    -- より `左辺 ≤ 右辺`
    -- `card_P_left` と `card_P_right_le` を使う
    -- 書換で閉じます
    have := card_P_right_le
    -- `P.card = k * aCount F k`
    -- ここは `calc` でもよいですが `rw` で十分
    -- 小さくまとめるため：
    exact (by
      -- 右辺の式そのまま
      -- 左辺を書換え
      have hL : P.card = k * aCount F k := card_P_left
      simpa [hL])
  -- 仕上げ：n = |α|
  simpa [hn] using this

/- sorryがたくさんあり、まるっきり描き直したので、消せる。
lemma double_count_main_ineq_left2
  [Fintype α] [DecidableEq α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F)
  (k : ℕ) (hk : 1 ≤ k) (hk_top : k ≤ Fintype.card α - 1) :
  k * aCount F k ≤ (Fintype.card α - k + 1) * aCount F (k-1) := by
  classical
  -- 記号
  set n := Fintype.card α with hn

  -- Fk, F(k-1)
  let Fk   : Finset (Finset α) := F.filter (fun A => A.card = k)
  let Fkm1 : Finset (Finset α) := F.filter (fun B => B.card = (k-1))

  have hFk_mem : ∀ {A}, A ∈ Fk → A ∈ F ∧ A.card = k := by
    intro A hA; simpa [Fk] using hA

  have hFkm1_mem_card : ∀ {B}, B ∈ Fkm1 → B ∈ F ∧ B.card = k-1 := by
    intro B hB; simpa [Fkm1] using hB

  -- 対象のペア集合：P := Σ A∈Fk, (A の (k-1)-部分集合)
  -- これを A 側で数えると、各 fiber の大きさは `choose k (k-1)=k`。
  -- よって |P| = k * aCount F k。
  let P : Finset ((Finset α) × (Finset α)) := (Fk.sigma (fun A => powersetCard (k-1) A)).image (fun p => (p.1, p.2))

  have card_P_left :
      P.card = k * aCount F k := by
    -- card_sigma： Σ のカードは fiber のカード和
    have hσ := Finset.card_sigma (s := Fk) (t := fun A => powersetCard (k-1) A)
    -- 各 fiber： (powersetCard (k-1) A).card = choose A.card (k-1) = k
    have fiber_eq :
      ∀ {A}, A ∈ Fk →
        ((powersetCard (k-1) A).card = k) := by
      intro A hA
      rcases hFk_mem hA with ⟨_, hAk⟩
      -- `card_powersetCard` と `choose_succ_self_right (k-1)` を使う
      -- (choose k (k-1) = k)
      have := (Finset.card_powersetCard (s := A) (n := k-1))
      -- A.card = k で書き換え
      -- choose k (k-1) = k は `Nat.choose_succ_self_right (k-1)`
      -- （`(k-1).succ = k`）
      have hk1 : (k-1).succ = k := by
        have := Nat.sub_add_cancel hk
        exact this
      -- まとめ
      -- `this : (powersetCard (k-1) A).card = Nat.choose A.card (k-1)`
      -- 書き換えで `= Nat.choose k (k-1) = k`
      -- 明示的に：
      --   simp [hAk, hk1, Nat.choose_succ_self_right] at this
      -- でも行けますが、`rw` で順に。
      -- ここは `simp` で簡潔に：
      simp [hAk]
      subst hAk
      simp_all only [mem_filter, and_self, implies_true, n, Fk, Fkm1]
      simp_all only [one_le_card, card_sigma, card_powersetCard, and_true, Nat.choose_symm,
        Nat.choose_one_right, Nat.succ_eq_add_one]

    have sum_const :
      ∑ A ∈ Fk, ((powersetCard (k-1) A).card) = k * Fk.card := by
      -- 全項が k（前項の fiber_eq）
      have hconst : ∀ A ∈ Fk, ((powersetCard (k-1) A).card) = k :=
        fun A hA => fiber_eq hA
      -- ∑ を項ごとに書き換える（`sum_congr`）
      have h₁ :
        ∑ A ∈ Fk, ((powersetCard (k-1) A).card)
        = ∑ A ∈ Fk, k := by
        refine Finset.sum_congr rfl ?_
        intro A hA
        exact congrArg id (hconst A hA)
      -- ∑ A∈Fk k = k * |Fk| は `sum_const_nat`
      -- （`simp` で落とす）
      have h₂ : ∑ A ∈ Fk, k = k * Fk.card := by
        -- `sum_const_nat` の型は `sum (λ _ => c) s = c * s.card`
        -- restricted sum の形なので `by classical; simpa` …は使わない方針なので
        -- 明示 `Finset.sum_const_nat` を使う
        -- mathlib4: `by classical exact Finset.sum_const_nat k _`
        classical
        simp_all only [mem_filter, and_self, implies_true, card_sigma, sum_const, smul_eq_mul, card_powersetCard,
          Nat.choose_symm, Nat.choose_one_right, n, Fk, Fkm1]
        rw [mul_comm]

      -- 連結
      -- h₁ で左辺を定数和にし、h₂ で評価
      -- `rw` の連鎖で仕上げ
      -- ここも `simp` を避けて `rw` で
      have := h₁
      -- `rw [h₂]` を適用
      -- 実際には `rw [h₁, h₂]` と 2 行で終わります
      -- ここでは最終等式を返します
      rw [this]
      exact h₂

    -- 仕上げ
    -- |P| = ∑_A |fiber| = ∑_A k = k * |Fk| = k * aCount F k
    -- Fk.card = aCount F k は定義そのもの
    simp [P, Fk, aCount]
    have hId : (fun p : (Finset α × Finset α) => (p.1, p.2)) = id := by
      funext p; cases p; rfl
    -- よって `image id s = s`
    -- P の定義から `P = (Fk.sigma ...).image id = Fk.sigma ...`
    --have P_eq :
    --  P = (Fk.sigma (fun A => powersetCard (k-1) A)) := by
      -- `by ext` で十分
      -- `simp [P, hId]`
      -- `simpa` を避け、`rw` で
      -- 実コードでは： `dsimp [P]; rw [hId]; simpa`
      -- ここでは結論だけ返します
    --  rfl
    -- これで `P.card = card_sigma = ∑_A |fiber|`
    -- さらに (1-2) より k * |Fk|
    -- 最後に `aCount F k = Fk.card` を定義から代入
    -- 仕上げ
    -- `aCount F k = (F.filter (·.card = k)).card = Fk.card`
    have aCount_eq : aCount F k = Fk.card := by
      -- `aCount` の定義を展開するだけ
      -- `aCount F k := (F.filter (fun A => A.card = k)).card`
      -- ここでは Fk と一致
      -- `rfl`
      rfl
    -- 連結
    -- `P.card = ∑ = k*Fk.card = k * aCount F k`
    -- `card_sigma` を呼ぶ
    have hσ := Finset.card_sigma (s := Fk) (t := fun A => powersetCard (k-1) A)
    -- `hσ : (Fk.sigma _).card = ∑ A∈Fk, (powersetCard ...).card`
    -- 左辺を書き換え（P_eq）
    -- 右辺を書き換え（sum_const）
    -- 仕上げに aCount_eq
    -- 実コードでは `rw` で 3 回
    -- 最後だけ等式で返す
    -- ここでは完成形を返します：
    --   P.card = k * aCount F k
    -- 具体実装は：
    --   have := hσ; rw [←P_eq] at this; rw [sum_const] at this; rw [aCount_eq] at this; exact this
    exact
      by
        have h' := hσ
        -- 書換の詳細はあなたの環境で `rw` を連続適用してください
        -- 最終形だけ返します
        -- `exact ...`
        -- ここでは完成形の等式が得られることだけ示して終えます
        -- （上の材料で機械的に閉じます）
        sorry


  /- 右側：|P| を B 固定で上から抑える。
     （`ideal` により、k ≤ n-1 ⇒ A≠univ ⇒ B∈F が保証される。）
     各 B（|B|=k-1）について、`A∈Fk` かつ `B ⊆ A` の個数は
     「候補 x ∈ (univ \ B)」の個数（= n - (k-1)）以下。
     和をとって `(n - k + 1) * aCount F (k-1)` が上界。 -/

  -- P を B 側で表す：P に含まれる (A,B) は必ず B∈Fkm1（ideal で）。
  -- よって |P| ≤ ∑_{B∈Fkm1} |{A∈Fk | B⊆A}|.
  have card_P_right_le :
      P.card ≤ ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card := by
    -- 定義から (A,B) ∈ P なら A∈Fk, B∈powersetCard(k-1)A。
    -- `mem_powersetCard` で B⊆A ∧ B.card=k-1。
    -- ideal の "U 以外で下閉" で B∈F を付与（A≠univ は k≤n-1 より）。
    -- それを使い、各 (A,B) を一意に fiber（B 固定の A の集合）へ落とす。
    -- この射は単射なので |P| ≤ Σ_B |fiber|.
    -- 実装はやや長いので、標準的な `card_le_of_subset` を fiber 毎に足し合わせる形に
    -- 変換するのが簡単です。
    -- ここでは、`card_sigma` の universal property を用いる代替：P を
    -- `Fkm1.sigma (fun B => Fk.filter (fun A => B ⊆ A))` に「埋め込み」ます。
    -- 具体的には、(A,B) ↦ (B,A) で `mem` 条件が満たされることを示してから
    -- `card_le_of_subset` を適用します。
    dsimp [P]
    sorry
  -- 各 B について fiber の大きさ上界：
  -- |{A∈Fk | B⊆A}| ≤ |{A⊆univ | |A|=k ∧ B⊆A}| = |univ\B| = n - (k-1) = n - k + 1
  have fiber_le :
    ∀ {B}, B ∈ Fkm1 →
      (Fk.filter (fun A => B ⊆ A)).card ≤ (n - k + 1) := by
    intro B hB
    have hBfacts : B ∈ F ∧ B.card = k-1 := hFkm1_mem_card hB
    -- まず、上側の「全候補」集合
    let AllA : Finset (Finset α) :=
      (powersetCard k (univ : Finset α)).filter (fun A => B ⊆ A)
    -- 包含：Fk.filter (B⊆A) ⊆ AllA
    have subset_All :
      (Fk.filter (fun A => B ⊆ A)) ⊆ AllA := by
      intro A hA
      have hAf : A ∈ F ∧ A.card = k := by
        constructor
        · simp_all only [mem_filter, and_self, implies_true, n, Fk, Fkm1, P]
        · simp_all only [mem_filter, and_self, implies_true, n, Fk, Fkm1, P]
      -- A ⊆ univ は自明、|A|=k、B⊆A は hA から
      have : A ∈ powersetCard k (univ : Finset α) := by
        -- mem_powersetCard ↔ ⟨A ⊆ univ, A.card = k⟩
        -- A ⊆ univ は `subset_univ`
        have : A ⊆ (univ : Finset α) := by intro x hx; exact mem_univ _
        -- まとめ
        exact (by
          -- `simp [mem_powersetCard, this, hAf.right]`
          have : A ⊆ (univ : Finset α) ∧ A.card = k := And.intro this hAf.right
          simpa [mem_powersetCard] using this)
      -- B ⊆ A は `hA` の右側フィルタ条件から
      have hBA : B ⊆ A := by
        -- `hA : A ∈ Fk ∧ B ⊆ A` via `mem_filter`
        simp_all only [mem_filter, and_self, implies_true, true_and, mem_powersetCard, subset_univ, n, Fk, Fkm1, P]

      -- AllA の filter 条件に合致
      simp [AllA, mem_filter, this, hBA]

    -- したがって card ≤
    have le1 :
      (Fk.filter (fun A => B ⊆ A)).card ≤ AllA.card := by exact card_le_card subset_All

    -- AllA と `univ.filter (·∉B)` の間の全単射： x ↦ insert x B
    have card_AllA :
      AllA.card = ( (univ.filter (fun x : α => x ∉ B)).card ) := by
      -- 全単射 φ : {x ∈ univ | x ∉ B} ≃ {A ⊆ univ | |A|=k ∧ B⊆A}
      -- φ(x) = insert x B
      -- 逆は A ↦ 唯一の x ∈ A\B（|A\B|=1 を使う）
      -- mathlib で書くには `Finset.card_eq_iff_equiv_finset` ルートより、
      -- ここでは単純に `card_eq` を示す構成が長くなるので、
      -- あなたの既存補題（「B から 1 点足して作る k 集合の個数 = n - (k-1)」）を使うのが最短です。
      -- ない場合は、下の一行で評価：
      -- |univ\B| = n - |B| = n - (k-1)
      have cCand :
        (univ.filter (fun x : α => x ∉ B)).card = n - (k-1) := by
        -- 分割：univ = {x∈B} ⊔ {x∉B}
        -- よって card (¬∈B) = n - card B
        -- さらに card B = k-1
        have : (univ.filter (fun x : α => x ∈ B)).card = B.card := by
          -- これは `filter_subtype` の一行版
          -- `simp` で閉じます
          simp_all only [mem_filter, and_self, implies_true, filter_univ_mem, n, Fk, Fkm1, P, AllA]
                  -- `disjoint (inB) (¬inB)` と `card_disjoint_union`
        have hdisj :
          Disjoint (univ.filter (fun x : α => x ∈ B))
                   (univ.filter (fun x : α => x ∉ B)) := by
          refine disjoint_left.mpr ?_
          intro x hx hx'
          simp at hx hx'
          exact hx' hx
        have hunion :
          (univ.filter (fun x : α => x ∈ B)) ∪ (univ.filter (fun x : α => x ∉ B))
            = (univ : Finset α) := by
          ext x; by_cases hx : x ∈ B <;> simp [hx]
        -- card univ = 和
        --have := (Finset.card_union (univ.filter (fun x : α => x ∈ B)) (univ.filter (fun x : α => x ∉ B))) hdisj
        -- 整理
        -- univ.card = card(inB) + card(notInB)
        -- よって card(notInB) = n - card(inB) = n - card B
        -- さらに card B = k-1
        -- 書換
        have : (Finset.univ.filter (fun x : α => x ∉ B)).card
              = Fintype.card α - B.card := by
          -- 代入して整理
          -- ここ、`n = univ.card` なので
          -- 最終的に `= n - (k-1)`
          -- 手続きは rw 連打で閉じます
          -- 簡潔化：
          --   exact by linarith でも通りますが、`Nat` 等式は `rw` で。
          -- ここは一気に：
          -- （実際の環境では `simp [*]` で多くが落ちます）
          --let fc := Finset.filter_card_add_filter_neg_card_eq_card (fun (x : α) => (x ∈ B) : α → Prop) (by decide)
          have : B.card + ({x | x ∉ B} : Finset α).card = Fintype.card α := by
            -- using @ to help type inference: we explicitly supply the type parameter α
            let p : α → Prop := fun x => x ∈ B
            let fc := @Finset.filter_card_add_filter_neg_card_eq_card  α (Finset.univ : Finset α) p
            have : Finset.univ.card = Fintype.card α := Finset.card_univ
            rw [this] at fc
            dsimp [p]  at fc
            rw [←this] at fc;
            simp at fc
            have : B.card =  #{x | x ∈ B} := by
              (expose_names; exact id (Eq.symm this_1))
            rw [this]
            apply fc

          rw [←this]
          exact Nat.eq_sub_of_add_eq' rfl

        -- 仕上げ
        -- `simp [hn, this, hBfacts.right]`
        -- card B = k-1
        have : (univ.filter (fun x : α => x ∉ B)).card
              = n - (k-1) := by
          -- 上の式に `hn` と `hBfacts.right` を代入
          -- `simp [hn, this, hBfacts.right]`
          simp_all only [mem_filter, and_self, implies_true, filter_univ_mem, n, Fk, Fkm1, P, AllA]
        exact this
      -- さらに、AllA のカードは「x の個数」に一致（挿入が全単射）
      -- よって AllA.card = n - (k-1)
      -- ここでは値だけ使えば十分

      simp [AllA]
      rw [cCand]
      dsimp [powersetCard]

      sorry

    -- したがって上界：
    -- |Fk.filter (B⊆A)| ≤ |AllA| = |univ\B| = n - (k-1) = n - k + 1
    have : (Fk.filter (fun A => B ⊆ A)).card ≤ (n - k + 1) := by
      -- le1 並びに card_AllA と n - (k-1) = n - k + 1
      -- `simp [card_AllA, Nat.sub_eq, Nat.add_comm]` 的に整理
      -- 簡単に：
      have : (Fk.filter (fun A => B ⊆ A)).card ≤ AllA.card := le1
      -- 書換
      have : (Fk.filter (fun A => B ⊆ A)).card ≤ (n - k + 1) := by
        -- `card_AllA` と k-1 の関係で整形
        -- card_AllA : AllA.card = n - k + 1
        -- まず右辺を書き換える：
        -- exact le_trans le1 (by simpa [card_AllA])
        -- 上の 1 行だけで十分ですが、明示化：
        have := le1
        -- これに `card_AllA` を適用
        -- 右辺置換
        -- done
        apply le_trans this
        rw [card_AllA]
        have : #{x | x ∉ B} = n - #B := by
          dsimp [n]
          let p : α → Prop := fun x => x ∈ B
          let fc := @Finset.filter_card_add_filter_neg_card_eq_card  α (Finset.univ : Finset α) p
          have : Finset.univ.card = Fintype.card α := Finset.card_univ
          rw [this] at fc
          dsimp [p]  at fc
          rw [←this] at fc;
          simp at fc
          have : B.card =  #{x | x ∈ B} := by
            exact Eq.symm (card_filter_in B)

          rw [this]
          have : #{x | x ∈ B} + #{a | a ∉ B} = Fintype.card α := by
            exact fc
          exact Nat.eq_sub_of_add_eq' fc

        rw [this]
        rw [hBfacts.right]
        exact tsub_tsub_le_tsub_add
      exact this

    exact this


  -- 和をとる：|P| ≤ ∑_B ≤ ∑_B (n - k + 1) = (n - k + 1) * |Fkm1|
  have card_P_le :
      P.card ≤ (n - k + 1) * aCount F (k-1) := by
    -- まず Σ_B の和で上から抑える
    have : ∑ B ∈ Fkm1, (Fk.filter (fun A => B ⊆ A)).card
         ≤ ∑ B ∈ Fkm1, (n - k + 1) := by
    { exact sum_le_sum (λ B hB=> fiber_le hB) }

    -- 右辺は定数和
    have rhs : (∑ _ ∈ Fkm1, (n - k + 1)) = (n - k + 1) * Fkm1.card := by
      simp
      exact Nat.mul_comm (#Fkm1) (n - k + 1)
    -- そして aCount F (k-1) = Fkm1.card
    have Fkm1_is : Fkm1.card = aCount F (k-1) := by
      rfl
    -- まとめ
    -- |P| ≤ Σ_B ... ≤ (n - k + 1) * |Fkm1| = (n - k + 1) * aCount F (k-1)
    exact
      le_trans card_P_right_le (by
        simpa [rhs, Fkm1_is])

  -- 左右を結合
  -- |P| = k * aCount F k かつ |P| ≤ (n - k + 1) * aCount F (k-1)
  have : k * aCount F k ≤ (n - k + 1) * aCount F (k-1) := by
    have := card_P_le
    -- 左側を card_P_left で置換
    -- `rw [card_P_left]` は等号を左側に適用するので、`have h := ...; exact h`
    -- とせず、`have := ...;` → `simpa [card_P_left]` が簡潔
    simpa [card_P_left] using this

  simpa [hn] using this
-/

lemma choose_succ_shift_compl (n k : ℕ) (hk : k + 1 ≤ n) :
    (n - (k+1) + 1) * Nat.choose n (n - (k+1) + 1)
  = (n - (n - (k+1))) * Nat.choose n (n - (k+1)) := by
  -- r := n - (k+1)
  set r := n - (k+1)
  -- r+1 = n - k
  have t1 : r + 1 = n - k := by
    dsimp [r];
    omega
  -- r+1 ≤ n
  have hr1 : r + 1 ≤ n := by
    -- `n - k ≤ n`
    have : n - k ≤ n := Nat.sub_le _ _
    -- 書き換え
    simp [t1]
  -- 下段シフト恒等式を r に適用
  have h :
    (r + 1) * Nat.choose n (r + 1)
      = (n - r) * Nat.choose n r := by

    apply choose_mul_symm_eq (n := n)
    exact hr1
  -- r を元に戻す
  dsimp [r] at h
  exact h

lemma frac_le_of_cross_mul
  {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d)
  (h : a * d ≤ c * b) :
  a / b ≤ c / d := by
  -- 目標は (div_le_iff hb).mpr (a ≤ (c/d)*b)
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hd0 : d ≠ 0 := ne_of_gt hd
  -- h : a*d ≤ c*b から、(le_div_iff hd).mpr で a ≤ (c*b)/d
  have h1 : a ≤ (c * b) / d := by exact (le_div_iff₀ hd).mpr h
  -- (c*b)/d = (c/d)*b
  have h2 : (c * b) / d = (c / d) * b := by
    -- `div_mul_eq_mul_div : (c/d) * b = c * b / d`
    have := (div_mul_eq_mul_div (a := c) (b := d) (c := b))
    -- 上は ((c/d) * b) = (c * b) / d なので、対称にする
    exact this.symm
  -- a ≤ (c/d)*b
  have h3 : a ≤ (c / d) * b := by
    -- h1 の右辺を h2 で置換
    have := h1
    -- 置換
    -- `calc ...` を避けて `rw` で
    -- ここでは簡潔に：
    simpa [h2]
  -- div へ戻す
  -- (div_le_iff hb).mpr : (a ≤ (c/d)*b) → a/b ≤ c/d
  exact (div_le_div_iff₀ hb hd).mpr h

lemma Nat.choose_mul_symm_eq {n k : ℕ} (hk : k + 1 ≤ n) :
    (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
  -- 補助: 「残り段数」に対する恒等式
  -- 省略記法
  --set n' := Fintype.card α
  set r  := n - (k + 1)

  -- r+1 ≤ n' を用意（hk_le : k+1 ≤ n' がある）
  have hr1 : r + 1 ≤ n := by
    -- r + 1 = n' - k
    have t1 : r + 1 = n - k := by
      simp_all only [r]
      omega
    -- n' - k ≤ n'
    have : n - k ≤ n := Nat.sub_le _ _
    -- 置換して結論
    exact t1 ▸ this

  -- Nat.choose_mul を k := r+1, s := r で適用
  --   n'.choose (r+1) * (r+1).choose r = n'.choose r * (n' - r).choose ((r+1) - r)
  have hmul :
      n.choose (r+1) * (r+1).choose r
    = n.choose r * (n - r).choose ((r+1) - r) :=
    Nat.choose_mul (n := n) (k := r+1) (s := r)
      (hkn := hr1) (hsk := Nat.le_succ r)

  -- 左右の二項係数を簡約： (r+1).choose r = r+1,  ((r+1)-r)=1,  (n'-r).choose 1 = n'-r
  have hmul' :
      n.choose (r+1) * (r+1)
    = n.choose r * (n - r) := by
    -- (n'-r).choose 1 = n'-r は `cases` で処理
    have h_choose1 : (n - r).choose 1 = (n - r) := by
      cases hnr : (n - r) with
      | zero =>
          simp
      | succ m =>
          -- Nat.choose_one_right : (m.succ).choose 1 = m.succ
          simp

    -- まとめて書き換え
    -- (r+1).choose r = r+1 は `Nat.choose_succ_self_right`
    have h_left : (r+1).choose r = r+1 := Nat.choose_succ_self_right r
    have h_delta : (r+1) - r = 1 := by exact Nat.add_sub_self_left r 1
    -- hmul に代入
    -- n'.choose (r+1) * (r+1) = n'.choose r * (n' - r)
    --   ← それぞれ h_left, h_delta, h_choose1 で書き換える
    -- `simp` を使わず等式変形で行くなら `rw` を3回ずつ当ててください。
    -- ここでは簡潔さを優先して `simp` を使っています（「simpa using」は使っていません）。
    simpa [h_left, h_delta, h_choose1] using hmul

  -- 乗法の可換性で最終形へ（左右の因子順を合わせる）
  have h_core :
      (r+1) * n.choose (r+1)
    = (n - r) * n.choose r := by
    calc
      (r+1) * n.choose (r+1)
          = n.choose (r+1) * (r+1) := Nat.mul_comm _ _
      _   = n.choose r * (n - r) := hmul'
      _   = (n - r) * n.choose r := Nat.mul_comm _ _

  -- r = n' - (k+1) を元の記法へ戻して `h₁` 完成
  have h₁ :
    (n - (k + 1) + 1) * Nat.choose n (n - (k + 1) + 1)
    = (n - (n - (k + 1))) * Nat.choose n (n - (k + 1)) := by
    -- rfl を使って両辺を置換
    --  (r+1) = (n' - (k+1) + 1),  (n' - r) = n' - (n' - (k+1))
    --  choose の引数も同様に置換
    dsimp [r] at h_core
    -- そのまま一致
    exact h_core

  -- 整数の整理: n - (k+1) + 1 = n - k,  n - (n - (k+1)) = k + 1
  have t1 : n - (k + 1) + 1 = n - k := by omega --exact?--Nat.sub_add_cancel hk
  have t2 : n - (n - (k + 1)) = k + 1 := Nat.sub_sub_self hk

  -- 書き換えにより形を揃える
  have h₂ :
    (n - k) * Nat.choose n (n - k)
      = (k + 1) * Nat.choose n (n - (k + 1)) := by
    rw [←t2] at h₁
    simp_all only [Nat.choose_symm]

  -- 二項係数の対称性 choose n (n - r) = choose n r
  have sum1 : k + (n - k) = n := by
    apply Nat.add_sub_of_le
    apply Nat.le_of_lt_succ
    exact Nat.lt_succ_of_lt hk
  have sum2 : (k + 1) + (n - (k + 1)) = n := Nat.add_sub_of_le hk

  have ch1 : Nat.choose n (n - k) = Nat.choose n k := by
    have hk' : k ≤ n := by omega
    exact (Nat.choose_symm hk')
  have ch2 : Nat.choose n (n - (k + 1)) = Nat.choose n (k + 1) := by
    apply Nat.choose_symm
    exact hk


  -- すべてを置換して等式完成
  rw [ch1, ch2] at h₂
  exact h₂.symm

omit [Fintype α] [DecidableEq α] in
lemma sOf_monotone_on_init_ge2 [Fintype α] [DecidableEq α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F)
  (n : ℕ) (h_n : n = Fintype.card α) (h2 : 2 ≤ n) :
  ∀ k, k ≤ n - 2 → sOf F k ≥ sOf F (k+1) := by
  classical
  -- 典型の二重計数： (k+1) a_{k+1} ≤ (UCard - k) a_k
  -- choose 恒等式で割って、a_{k+1}/C(n,k+1) ≤ a_k/C(n,k)
  intro k hk
  by_cases h_n0 : Fintype.card α = 0
  · have : k = 0:= by
      subst h_n
      simp_all only [zero_tsub, nonpos_iff_eq_zero]
    dsimp [this, sOf, aCount]
    simp_all


  · have hk1 : 1 ≤ k+1 := Nat.succ_le_succ (Nat.zero_le _)

    have hk_le : k+1 ≤ Fintype.card α := by
      have : k ≤ Fintype.card α - 1 := by
        subst h_n
        simp_all only [le_add_iff_nonneg_left, zero_le]
        omega
      apply Nat.succ_le_of_lt
      apply Nat.lt_of_le_of_lt this
      rw [← h_n]
      subst h_n
      simp_all only [le_add_iff_nonneg_left, zero_le, tsub_lt_self_iff, zero_lt_one, and_true]
      positivity

      --(Nat.lt_of_le_of_lt this (Nat.lt_of_le_of_lt (Nat.le_of_eq rfl) (Nat.lt_succ_self _)))
    -- 分母正
    have hpos1 : 0 < (Nat.choose n (k+1) : ℚ) := by
      have := by
        apply Nat.choose_pos (n:=n) (k:=k+1)
        subst h_n
        simp_all only [le_add_iff_nonneg_left, zero_le]
      exact_mod_cast this
    have hpos0 : 0 < (Nat.choose (Fintype.card α) k : ℚ) := by
      have hk0 : k ≤ Fintype.card α := by

        apply Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
        subst h_n
        simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos, tsub_le_iff_right, le_add_iff_nonneg_right]
      have := Nat.choose_pos (n:=UCard) (k:=k) hk0
      exact_mod_cast this
    -- 主不等式（自然数）：(k+1) * a_{k+1} ≤ (UCard - k) * a_k
    have main_nat :
      (k+1) * aCount F (k+1) ≤ (Fintype.card α - k) * aCount F k := by
      -- 「A 固定で数える」と「B 固定で数える」の標準形
      -- 既知の補題として導入済みとみなす（あなたの別ファイルにある内容）
      -- ここでは冗長な展開を避け、既存と同名の補題に倣って証明する
      -- ※ 実運用では、前にお渡しした `card_pairs_left/right` ベースの証明ブロックをここにインラインで貼れば閉まります
      exact
        by
          -- 既に別セクションで証明済みのブロックを再利用する想定
          -- （Lean 上はそのブロックを同ファイルに持ってくるだけでこの `exact` が通ります）
          let dcm := double_count_main_ineq_left F hI (k + 1) hk1
          simp at dcm
          simp
          have :(Fintype.card α - (k + 1) + 1) = (Fintype.card α - k) := by omega
          rw [this] at dcm
          apply dcm
          simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos]
          have hsub : Fintype.card α - (k+1) + 1 = Fintype.card α - k := by
            -- `Nat.sub_add_cancel` に落ちます
            have hk1_le : k + 1 ≤ Fintype.card α := by
              apply Nat.le_trans
              exact hk_le
              exact Fintype.card_le_of_injective (fun ⦃a₁⦄ => a₁) fun ⦃a₁ a₂⦄ a => a
            exact this
          have h_k2_le_n : k + 2 ≤ n := by
            -- k ≤ n - 2 ⇒ k + 2 ≤ (n - 2) + 2
            have := Nat.add_le_add_right hk 2
            -- (n - 2) + 2 ≤ n は常に成り立つ（`Nat.sub_add_le`）
            have h' : k + 2 ≤ Fintype.card α := by
              apply this.trans
              subst h_n
              simp_all only [Nat.sub_add_cancel, le_refl]
            simpa [h_n] using h'

          -- `k + 1 ≤ n - 1` と `k + 2 ≤ n` は同値（どちらも片側に 1 を足す関係）
          -- ただし `((n - 1).succ = n)` を使うために `1 ≤ n` が要るが、
          -- 上の `h_k2_le_n` から明らかに `2 ≤ n`、したがって `1 ≤ n`。
          have hn_pos : 1 ≤ n := le_trans (by decide : 1 ≤ 2)
                                            (by
                                              -- h_k2_le_n: k+2 ≤ n ⇒ 2 ≤ n
                                              exact (le_trans (by exact Nat.le_add_left _ _) h_k2_le_n))

          -- succ を両辺に付けてから戻す：
          have : (k + 1).succ ≤ (n - 1).succ := by
            -- 左は k+2、右は n
            simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hn_pos] using h_k2_le_n
          -- succ を落として結論へ
          have hk_succ : k + 1 ≤ n - 1 := (Nat.succ_le_succ_iff).1 this
          exact le_of_le_of_eq hk_succ (congrFun (congrArg HSub.hSub h_n) 1)

          --exact double_count_main_ineq F hI k
    -- choose の恒等式：(k+1) C(n,k+1) = (n-k) C(n,k)
    have choose_id :
      ((k+1 : ℚ) * (Nat.choose (Fintype.card α) (k+1) : ℚ))
        = (((Fintype.card α) - k : ℚ) * (Nat.choose (Fintype.card α) k : ℚ)) := by
      have natId :
        (k + 1) * Nat.choose (Fintype.card α) (k + 1)
          = (Fintype.card α - k) * Nat.choose (Fintype.card α) k := by
        let ns := Nat.succ_mul_choose_eq (n := Fintype.card α) (k := k)

        exact Nat.choose_mul_symm_eq hk_le

      have choose_id :
        ((k+1 : ℚ) * (Nat.choose (Fintype.card α) (k+1) : ℚ))
          = (((Fintype.card α) - k : ℚ) * (Nat.choose (Fintype.card α) k : ℚ)) := by
          have h₁ :
            (Fintype.card α - (k+1) + 1)
              * Nat.choose (Fintype.card α) (Fintype.card α - (k+1) + 1)
            = (Fintype.card α - (Fintype.card α - (k+1)))
              * Nat.choose (Fintype.card α) (Fintype.card α - (k+1)) := by
              let nsm := Nat.succ_mul_choose_eq (n := Fintype.card α) (k := Fintype.card α - (k+1))
              simp at nsm
              apply Nat.choose_mul_symm_eq
              subst h_n
              simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos]
              omega

          -- 左右の「- (k+1) + 1」や「n - (n - (k+1))」を簡約
          have h₂ :
            (Fintype.card α - k) * Nat.choose (Fintype.card α) (Fintype.card α - k)
            = (k+1) * Nat.choose (Fintype.card α) (Fintype.card α - (k+1)) := by
            -- n - (k+1) + 1 = n - k
            have t1 : Fintype.card α - (k+1) + 1 = Fintype.card α - k := by
              subst h_n
              simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos, Nat.choose_symm]
              omega
            -- n - (n - (k+1)) = k+1
            have t2 : Fintype.card α - (Fintype.card α - (k+1)) = k+1 :=
              Nat.sub_sub_self hk_le
            simpa [t1, t2] using h₁

          -- choose の対称性で `choose n (n - r) = choose n r` に書き換える
          have sum1 : k + (Fintype.card α - k) = Fintype.card α := by
            apply Nat.add_sub_of_le
            apply Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self k))
            exact Nat.le_of_succ_le hk_le
          have sum2 : (k+1) + (Fintype.card α - (k+1)) = Fintype.card α :=
            Nat.add_sub_of_le hk_le

          have ch1 :
            Nat.choose (Fintype.card α) (Fintype.card α - k)
              = Nat.choose (Fintype.card α) k := by
            -- choose_symm_add : choose (a+b) a = choose (a+b) b
            -- ここでは n = k + (n-k)
            subst h_n
            simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos, Nat.choose_symm, mul_eq_mul_left_iff,
              add_tsub_cancel_of_le]
            cases h₂ with
            | inl h => simp_all only
            | inr h_1 =>
              simp_all only [zero_mul, nonpos_iff_eq_zero, mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false, false_or,
                mul_zero, add_zero, Nat.choose_succ_self, lt_self_iff_false]

          have ch2 :
            Nat.choose (Fintype.card α) (Fintype.card α - (k+1))
              = Nat.choose (Fintype.card α) (k+1) := by
            subst h_n
            simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos, Nat.choose_symm, add_tsub_cancel_of_le]

          -- 置換して目標の左右と一致
          have h₃ :
            (Fintype.card α - k) * Nat.choose (Fintype.card α) k
            = (k+1) * Nat.choose (Fintype.card α) (k+1) := by
            simpa [ch1, ch2] using h₂

          -- 目標はこの等式の両辺を入れ替えただけ
          have hk' : k ≤ Fintype.card α := by
            apply Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self k))
            exact Nat.le_of_succ_le hk_le

          -- h₃ を ℚ へキャスト（左右をゴールに合わせるために対称にしておく）
          have hQ' :
            ((k + 1 : ℕ) : ℚ) * (↑((Fintype.card α).choose (k + 1)) : ℚ)
              = (↑(Fintype.card α - k) : ℚ) * (↑((Fintype.card α).choose k) : ℚ) := by
            -- h₃ : (|α| - k) * choose k = (k+1) * choose (k+1)
            -- を左右反転して exact_mod_cast
            exact_mod_cast h₃.symm

          -- (k+1) と (|α|-k) のキャストを目標の形に整形
          have hadd : ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 := by
            simp [Nat.cast_add, Nat.cast_one]

          have hsub :
            (↑(Fintype.card α - k) : ℚ) = (Fintype.card α : ℚ) - (k : ℚ) :=
            Nat.cast_sub hk'

          -- 仕上げ：書き換えて目標と一致させる
          have : ((k : ℚ) + 1) * ↑((Fintype.card α).choose (k + 1))
                = ((Fintype.card α : ℚ) - (k : ℚ)) * ↑((Fintype.card α).choose k) := by
            simpa [hadd, hsub] using hQ'

          exact this
          --exact h₃.symm



        -- ℕ の等式 `natId` をそのまま ℚ にキャスト
      subst h_n
      simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos]



    have :
      (aCount F (k+1) : ℚ) / (Nat.choose (Fintype.card α) (k+1) : ℚ)
        ≤ (aCount F k : ℚ) / (Nat.choose (Fintype.card α) k : ℚ) := by
      -- a/b ≤ c/d ↔ a*d ≤ c*b （b,d>0）
      -- main_nat を実数化し、choose_id を掛け合わせる
      have mainR :
        ((k+1 : ℚ) * (aCount F (k+1) : ℚ))
          ≤ ((Fintype.card α - k : ℚ) * (aCount F k : ℚ)) := by
        have :(k + 1) * aCount F (k + 1) ≤ (Fintype.card α - k) * aCount F k := by
          exact_mod_cast main_nat
        have hk' : k ≤ Fintype.card α := by
          apply Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self k))
          exact Nat.le_of_succ_le hk_le

        -- 自然数の不等式 main_nat を ℚ へキャスト
        have hQ :
          ((k + 1 : ℕ) : ℚ) * (aCount F (k + 1) : ℚ)
            ≤ (↑(Fintype.card α - k) : ℚ) * (aCount F k : ℚ) := by
          exact_mod_cast main_nat

        -- (k+1) と (|α|-k) のキャストを目標の形に書き換え
        have hadd : ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 := by
          simp [Nat.cast_add, Nat.cast_one]
        have hsub : (↑(Fintype.card α - k) : ℚ) = (Fintype.card α : ℚ) - (k : ℚ) :=
          Nat.cast_sub hk'

        -- 仕上げ：書き換えて目標と一致
        have : ((k : ℚ) + 1) * (aCount F (k + 1) : ℚ)
              ≤ ((Fintype.card α : ℚ) - (k : ℚ)) * (aCount F k : ℚ) := by
          simpa [hadd, hsub] using hQ

        exact this

        --sorry--exact_mod_cast main_nat
      -- 両辺に正の量をかけて整理：詳細は algebra 的等価変形
      -- 完全展開は長くなるので、`div_le_iff` を2回で機械的に閉じるのが無難です
      have hb : 0 < (Nat.choose (Fintype.card α) (k+1) : ℚ) := by
        subst h_n
        simp_all only [le_add_iff_nonneg_left, zero_le, Nat.cast_pos]
      have hd : 0 < (Nat.choose (Fintype.card α) k : ℚ) := hpos0
      -- (a/b ≤ c/d) ↔ (a*d ≤ c*b)
      -- ここでは右向きの形を作る

      let a1  : ℚ := (aCount F (k+1) : ℚ)
      let ak  : ℚ := (aCount F k     : ℚ)
      let Ck1 : ℚ := (Nat.choose (Fintype.card α) (k+1) : ℚ)
      let Ck  : ℚ := (Nat.choose (Fintype.card α) k     : ℚ)
      let kp1 : ℚ := (k+1 : ℚ)
      let nk  : ℚ := (Fintype.card α : ℚ) - k

      have step1 :
        (kp1 * a1) * Ck ≤ (nk * ak) * Ck :=
        mul_le_mul_of_nonneg_right mainR (le_of_lt hd)

      -- (2) 結合順を揃えて `kp1 * (a1*Ck) ≤ nk * (ak*Ck)` にする
      have step1' :
        kp1 * (a1 * Ck) ≤ nk * (ak * Ck) := by
        have h := step1
        -- (x*y)*z ↔ x*(y*z) を両辺に適用
        -- 左右とも `mul_assoc` がちょうど一回ずつ当たります
        rw [mul_assoc, mul_assoc] at h
        exact h

      -- (3) choose_id から ((n-k)*Ck) = (k+1)*Ck1 を取り出して、右辺を差し替える
      have step2 :
        nk * (ak * Ck) = kp1 * (Ck1 * ak) := by
        -- nk * (ak * Ck) = (nk * Ck) * ak
        have H1 : nk * (ak * Ck) = (nk * Ck) * ak := by
          -- nk * (ak * Ck) = (nk * ak) * Ck = ak * (nk * Ck) = (nk * Ck) * ak
          calc
            nk * (ak * Ck) = (nk * ak) * Ck := by rw [mul_assoc]
            _              = (ak * nk) * Ck := by rw [mul_comm nk ak]
            _              = ak * (nk * Ck) := by rw [mul_assoc]
            _              = (nk * Ck) * ak := by rw [mul_comm]
        -- ((nk * Ck) * ak) を (kp1 * Ck1) * ak に置換
        have H2 : (nk * Ck) * ak = (kp1 * Ck1) * ak :=
          congrArg (fun x : ℚ => x * ak) choose_id.symm
        -- (kp1 * Ck1) * ak = kp1 * (Ck1 * ak)
        have H3 : (kp1 * Ck1) * ak = kp1 * (Ck1 * ak) := by
          rw [mul_assoc]
        exact H1.trans (H2.trans H3)

      -- (4) 右辺を置換して `kp1 * (a1*Ck) ≤ kp1 * (Ck1*ak)` を得る
      have step3 :
        kp1 * (a1 * Ck) ≤ kp1 * (Ck1 * ak) := by
        have h := step1'
        -- 右辺 nk*(ak*Ck) を等式 step2 で置換
        rw [step2] at h
        exact h

      -- (5) 左から掛かっている kp1 を消す（kp1 > 0）
      have hkpos : 0 < kp1 := by
        -- hk1 : 1 ≤ k+1
        exact Nat.cast_add_one_pos k

      have cross :
        a1 * Ck ≤ ak * Ck1 := by
        -- `le_of_mul_le_mul_left : 0 < a → a*x ≤ a*y → x ≤ y`
        -- step3 を適用し、右辺は乗法可換で並べ替え
        have h := le_of_mul_le_mul_left step3 hkpos
        -- RHS: Ck1*ak を ak*Ck1 に
        -- LHS はそのまま
        -- `mul_comm` で右辺を書き換えれば一致
        have : a1 * Ck ≤ Ck1 * ak := h
        -- 並べ替え
        simpa [mul_comm] using this

      -- (6) 交差乗法 → 分数不等式
      have :
        (aCount F (k+1) : ℚ) / (Nat.choose (Fintype.card α) (k+1) : ℚ)
          ≤ (aCount F k : ℚ) / (Nat.choose (Fintype.card α) k : ℚ) :=
        -- a/b ≤ c/d を作る： b=Ck1>0, d=Ck>0, 交差形は a*Ck ≤ c*Ck1
        frac_le_of_cross_mul (hb := hb) (hd := hd) (h := cross)

      have cross' :
        (aCount F (k+1) : ℚ) * (Nat.choose (Fintype.card α) k : ℚ)
          ≤ (aCount F k : ℚ) * (Nat.choose (Fintype.card α) (k+1) : ℚ) := by
        -- `le_of_mul_le_mul_left` で左からの正の因子を消す
        -- まず step3 を `((k+1):ℚ) * … ≤ ((k+1):ℚ) * …` の形にしてから適用
        have := step3
        -- 左右の先頭を (k+1) * ( … ) にしておいたので、そのまま使える
        exact cross

      -- 5) 係数順を合わせて終了
      -- 目標は ↑a_{k+1} * C_k ≤ ↑a_k * C_{k+1}
      -- cross' はそのままの式なので、結合作用のみで一致します
      -- （この行でゴールが閉じます）
      exact frac_le_of_cross_mul hb hpos0 cross'


    -- s(k) ≥ s(k+1) へ翻訳
    -- sOf = a/choose
    have : sOf (α:=α) F k ≥ sOf (α:=α) F (k+1) := by
      -- ちょうど上の式の左右を入れ替えただけ
      -- （上は a_{k+1}/C ≤ a_k/C）
      simpa [sOf] using this
    exact this

-- 空集合だけがカード 0
omit [Fintype α] [DecidableEq α] in
private lemma aCount_zero_eq_one
  [Fintype α] [DecidableEq α]
  {F : Finset (Finset α)} (hI : IdealExceptTop F) :
  aCount F 0 = 1 := by
  classical
  -- フィルタが {∅} と一致することを示す
  have h₁ :
    (F.filter (fun A : Finset α => A.card = 0)) ⊆ ({∅} : Finset (Finset α)) := by
    intro A hA
    rcases Finset.mem_filter.1 hA with ⟨hAF, hA0⟩
    have hAeq : A = (∅ : Finset α) :=
      by
        -- card A = 0 → A = ∅
        exact Finset.card_eq_zero.1 (by simpa using hA0)
    simp [hAeq, Finset.mem_singleton]
  have h₂ :
    ({∅} : Finset (Finset α)) ⊆ (F.filter (fun A : Finset α => A.card = 0)) := by
    intro A hA
    rcases Finset.mem_singleton.1 hA with rfl
    exact Finset.mem_filter.2 ⟨hI.mem_empty, by simp⟩
  have hEq :
    F.filter (fun A : Finset α => A.card = 0) = ({∅} : Finset (Finset α)) :=
    Finset.Subset.antisymm h₁ h₂
  -- 個数は 1
  have : (F.filter (fun A : Finset α => A.card = 0)).card = 1 := by
    -- 単集合のカードは 1
    have : ({∅} : Finset (Finset α)).card = 1 := by simp
    -- 両辺の card を等号で書き換え
    -- （`congrArg` を使っても良い）
    simp_all only [card_eq_zero, subset_singleton_iff, filter_eq_empty_iff, forall_mem_not_eq', singleton_subset_iff,
      mem_filter, and_true, card_singleton]
  -- aCount の定義に戻す
  simpa [aCount] using this

-- 台集合が空のとき、カード 1 は存在しない
omit [Fintype α] [DecidableEq α] in
private lemma aCount_one_eq_zero_of_empty_univ
  [Fintype α] [DecidableEq α]
  (h0 : Fintype.card α = 0)
  (F : Finset (Finset α)) :
  aCount F 1 = 0 := by
  classical
  -- |α|=0 ⇒ 任意の A ⊆ α は A = ∅，よって card=1 の A は存在しない
  -- つまりフィルタは空
  have : (F.filter (fun A : Finset α => A.card = 1)) = ∅ := by

    refine filter_eq_empty_iff.mpr ?_
    intro A _
    -- univ = ∅ から A = ∅，したがって card A ≠ 1
    have huniv : (Finset.univ : Finset α) = ∅ := by
      -- `Fintype.card α = 0` なら `univ` は空（`Fintype.card_univ` で落とせます）
      -- `Finset.univ.card = Fintype.card α` を使い、card=0 は univ=∅
      -- mathlib に `univ_eq_empty_iff` があればそれを使ってください
      -- ここではカード議論で：
      have : (Finset.univ : Finset α).card = 0 := by
        simp_all only [card_univ]
      -- card univ = 0 → univ = ∅
      exact Finset.card_eq_zero.mp this
    have : A ⊆ (Finset.univ : Finset α) := by intro x hx; exact Finset.mem_univ _
    have : A ⊆ (∅ : Finset α) := by simpa [huniv] using this
    -- A ⊆ ∅ ⇒ A = ∅
    have : A = (∅ : Finset α) := by exact Finset.subset_empty.mp this
    -- よって card A = 0 ≠ 1
    simp [this]
  -- 個数 0
  simp [aCount, this]

omit [DecidableEq α] in
lemma filter_card_zero_eq_singleton_empty
  [DecidableEq α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F) :
  F.filter (fun A : Finset α => A.card = 0) = ({∅} : Finset (Finset α)) := by
  classical
  -- ⊆ 方向
  have h₁ :
      F.filter (fun A : Finset α => A.card = 0) ⊆ ({∅} : Finset (Finset α)) := by
    intro A hA
    -- A ∈ F ∧ A.card = 0
    have hA0 : A.card = 0 := by
      -- mem_filter の後件
      have := (Finset.mem_filter.mp hA).2
      exact this
    -- card=0 → A=∅
    have hAeq : A = (∅ : Finset α) :=
      (Finset.card_eq_zero.mp hA0)
    -- よって A ∈ {∅}
    exact Finset.mem_singleton.mpr hAeq
  -- ⊇ 方向
  have h₂ :
      ({∅} : Finset (Finset α)) ⊆ F.filter (fun A : Finset α => A.card = 0) := by
    intro A hA
    -- {∅} の元は A=∅ のみ
    have hAeq : A = (∅ : Finset α) := (Finset.mem_singleton.mp hA)
    -- A=∅ は F に属し，かつ |A|=0
    have hAF : A ∈ F := by
      -- hI.mem_empty : ∅ ∈ F
      -- hAeq で書き換え
      -- （`by` で手続き的に）
      have : (∅ : Finset α) ∈ F := hI.mem_empty
      -- A=∅ で置換
      exact by
        -- `A = ∅` を左辺に入れる
        -- `rw [hAeq]` と同じ効果
        cases hAeq
        exact this
    have hA0 : A.card = 0 := by
      -- A=∅ なので card=0
      -- 手続き的に書き換えます
      cases hAeq
      exact rfl
    -- フィルタの条件に合致
    exact Finset.mem_filter.mpr ⟨hAF, hA0⟩
  -- 反対称で等号
  exact Finset.Subset.antisymm h₁ h₂

omit [DecidableEq α] in
/-- したがって `# { A ∈ F | |A| = 0 } = 1`。-/
lemma card_filter_card_zero_eq_one
  [DecidableEq α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F) :
  (F.filter (fun A : Finset α => A.card = 0)).card = 1 := by
  classical
  -- 上の等式をカードにかけるだけ
  have h := filter_card_zero_eq_singleton_empty F hI
  -- `congrArg` で `card` を両辺に適用
  have hcard : (F.filter (fun A : Finset α => A.card = 0)).card
               = (({∅} : Finset (Finset α))).card :=
    congrArg Finset.card h
  -- 右辺は単集合のカード
  -- `rw` を避けるなら、手で等式をつなぎます
  -- まず右辺を評価
  have : (({∅} : Finset (Finset α))).card = 1 := by
    -- 単集合のカードは 1
    -- `simp` なしで：
    -- `Finset.card_singleton` と同等の事実を使います
    -- mathlib には `card_singleton` があるのでそれを呼びます
    exact Finset.card_singleton (∅ : Finset α)
  -- 連結
  -- 左辺 = 右辺.card = 1
  exact Eq.trans hcard this

omit [Fintype α] [DecidableEq α] in
lemma aCount_one_eq_one_of_card_one
  [Fintype α] [DecidableEq α]
  (h1 : Fintype.card α = 1)
  (F : Finset (Finset α)) (hI : IdealExceptTop F) :
  aCount F 1 = 1 := by
  classical
  -- `Subsingleton α` を得る
  haveI : Subsingleton α := (Fintype.card_le_one_iff_subsingleton).1
    (by simp [h1] : Fintype.card α ≤ 1)
  -- `univ` が唯一の 1 元集合
  -- （`A.card = 1` → `A = univ`）
  have singleton_is_univ :
      ∀ {A : Finset α}, A.card = 1 → A = (Finset.univ : Finset α) := by
    intro A hA
    -- `Subsingleton α` なので `univ = {x}` for any `x ∈ univ`
    have ⟨x, hx⟩ : ∃ x, x ∈ (Finset.univ : Finset α) := by

      refine ⟨Classical.choice ?_, by simp⟩
      contrapose! hA
      simp_all only [not_nonempty_iff, ne_eq, Fintype.card_eq_zero, zero_ne_one]

    have : (Finset.univ : Finset α) = {x} := by
      ext y; constructor <;> intro _ <;> simp [Subsingleton.elim y x]
    -- `A.card = 1` なので `A = {y}` for some `y`、よって `A = univ`
    rcases Finset.card_eq_one.mp hA with ⟨y, rfl⟩
    simp [this]
    simp_all only [mem_singleton, card_singleton]
    exact Subsingleton.elim _ _

  -- フィルタが `{univ}` と一致
  have h₁ :
    F.filter (fun A : Finset α => A.card = 1)
      ⊆ ({(Finset.univ : Finset α)} : Finset (Finset α)) := by
    intro A hA
    have hA1 : A.card = 1 := (Finset.mem_filter.mp hA).2
    have hAu : A = (Finset.univ : Finset α) := singleton_is_univ hA1
    exact Finset.mem_singleton.mpr hAu
  have h₂ :
    ({(Finset.univ : Finset α)} : Finset (Finset α))
      ⊆ F.filter (fun A : Finset α => A.card = 1) := by
    intro A hA; rcases Finset.mem_singleton.mp hA with rfl
    exact Finset.mem_filter.mpr ⟨hI.mem_univ, by simp [h1]⟩
  have hEq := Finset.Subset.antisymm h₁ h₂
  -- 個数は 1
  have : (({(Finset.univ : Finset α)} : Finset (Finset α))).card = 1 :=
    Finset.card_singleton (Finset.univ : Finset α)
  -- aCount に戻す
  change (F.filter (fun A : Finset α => A.card = 1)).card = 1
  exact Eq.trans (congrArg Finset.card hEq) this

omit [Fintype α] in
/-- 単調性： 1 ≤ k ≤ n-1 で  s(k) ≥ s(k+1)（≡ s_{k} ≥ s_{k+1}）
    二重計数により k+1 層と k 層の比較を行う（標準形）。 -/
lemma sOf_monotone_on_init [Fintype α]
  (F : Finset (Finset α)) (hI : IdealExceptTop F) (n : ℕ) (h_n : n = Fintype.card α) :
  ∀ k, k ≤ n - 2 → sOf F k ≥ sOf F (k+1) := by
classical
  by_cases h2 : 2 ≤ n
  · -- 大きい n の枝は本体をそのまま使う
    exact sOf_monotone_on_init_ge2 F hI n h_n h2
  · -- 小さい n の枝：n ≤ 1
    intro k hk
    have hn_le1 : n ≤ 1 := Nat.lt_of_not_ge h2 |> Nat.lt_succ_iff.mp
    -- 場合分け n = 0 or 1
    cases Nat.le.dest hn_le1 with
    | intro m hm =>
      -- hm : n = m with m = 0 or 1 を読むのは面倒なので素直に by_cases
      by_cases hn0 : n = 0
      · -- n = 0 の場合
        -- hk : k ≤ 0 なので k = 0
        have hk0 : k = 0 := Nat.le_zero.mp (by simpa [hn0] using hk)
        -- ここで sOf F 1 に分母 0 が出る可能性があるので、
        -- この枝に来ない設計（呼び出し側で n≥2 確保）にするのが無難。
        -- どうしても閉じるなら、sOf の定義が「分母=0 ⇒ 0」といった安全版である必要があります。
        -- もし `sOf` をそう定義しているなら、以下のように具体計算で 1 ≥ 0 を返せます。
        -- 例（安全版 sOf 想定）：
        -- have : sOf F 0 = (1 : ℚ) := by
        --   ...  -- aCount F 0 = 1, choose 0 0 = 1
        -- have : sOf F 1 = (0 : ℚ) := by
        --   ...  -- aCount F 1 = 0 または choose 0 1 = 0 の規約
        -- exact by simpa [hk0]  -- 1 ≥ 0
        -- ここでは、到達しない設計を前提に自明化：
        have a0 : aCount F 0 = 1 := aCount_zero_eq_one hI

        have a1 : aCount F 1 = 0 := by
          apply aCount_one_eq_zero_of_empty_univ (by rw [←h_n];exact hn0) F
        -- choose 値
        have c00 : (Nat.choose 0 0 : ℚ) = 1 := by norm_num
        have c01 : (Nat.choose 0 1 : ℚ) = 0 := by norm_num
        -- sOf（定義に合わせて）：
        have s0 : sOf F 0 = 1 := by
          -- sOf F 0 = aCount F 0 / choose 0 0 = 1/1
          -- あなたの sOf の定義に合わせて rw してください
          dsimp [sOf]
          subst h_n hk0
          simp_all only [Nat.choose_self, Nat.cast_one, Nat.choose_succ_self, CharP.cast_eq_zero, nonpos_iff_eq_zero,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_le, zero_add, zero_tsub, le_refl, ne_eq, one_ne_zero, div_self]

        have s1 : sOf F 1 = 0 := by
          -- sOf F 1 = aCount F 1 / choose 0 1 = 0 / 0 = 0 （Rat の規約）
          dsimp [sOf]
          subst h_n hk0
          simp_all only [Nat.choose_self, Nat.cast_one, Nat.choose_succ_self, CharP.cast_eq_zero, nonpos_iff_eq_zero,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_le, zero_add, zero_tsub, le_refl, div_zero]

        -- 1 ≥ 0
        have : sOf F 0 ≥ sOf F 1 := by
          -- `rw [s0, s1]` して `simp` でもよいですが、ここでは等号から
          rw [s0, s1]
          exact rfl

        -- k = 0 に戻す
        exact by
          have hk0 : k = 0 := Nat.le_zero.mp (by
            subst h_n hk0
            simp_all only [Nat.choose_self, Nat.cast_one, Nat.choose_succ_self, CharP.cast_eq_zero, ge_iff_le, zero_le_one,
              nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, zero_le, zero_add, zero_tsub, le_refl]
          )

          simpa [hk0] using this

      · -- n = 1 の場合
        have hn1 : n = 1 := by
          -- n ≤ 1 かつ n ≠ 0 ⇒ n = 1
          have : n = 0 ∨ n = 1 := by
            -- 標準補題 Nat.le_one_iff でもよい
            exact Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le1
          cases this with
          | inl h => exact (False.elim (by cases h; exact hn0 rfl))
          | inr h => exact h
        -- k ≤ n - 2 = 0 ⇒ k = 0
        have hk0 : k = 0 := Nat.le_zero.mp (by simpa [hn1] using hk)
        -- ideal 条件より ∅, univ ∈ F。|α|=1 なので
        -- aCount F 0 = 1, aCount F 1 = 1。
        -- choose も両方 1。
        -- よって sOf F 0 = 1, sOf F 1 = 1。
        -- 以下、分母正を使わず直接展開する（あなたの sOf/aCount の定義に合わせて調整）
        have hEmpty : (∅ : Finset α) ∈ F := hI.mem_empty
        have hUniv  : (Finset.univ : Finset α) ∈ F := hI.mem_univ
        -- aCount F 0 = 1
        have a0 : aCount F 0 = 1 := by
          -- filter で card=0 は空集合だけ
          -- 実装：`aCount` の定義を展開 → フィルタが {∅} になることを示す
          -- 既に用意している補題を呼んで構いません
          -- （長くなるので省略せずに書くなら、単集合同値を作って card=1）
          dsimp [aCount]
          exact card_filter_card_zero_eq_one F hI

        -- aCount F 1 = 1（|α|=1 では大きさ1は univ だけ）
        have a1 : aCount F 1 = 1 := by
          exact aCount_one_eq_one_of_card_one (h_n.symm.trans hn1) F hI

        -- choose 1 0 = 1, choose 1 1 = 1
        have c10 : (Nat.choose 1 0 : ℚ) = 1 := by norm_num
        have c11 : (Nat.choose 1 1 : ℚ) = 1 := by norm_num
        -- sOf の定義にそって評価
        have s0 : sOf F 0 = 1 := by
          -- sOf F 0 = aCount F 0 / choose 1 0
          -- = 1 / 1 = 1

          subst hn1 hk0
          simp_all only [Nat.choose_self]
          dsimp [sOf]
          rw [a0]
          rw [c11]
          rw [←h_n]
          simp

        have s1 : sOf F 1 = 1 := by
          dsimp [sOf]
          rw [a1]
          rw [←h_n]
          rw [hn1]
          simp

        -- 仕上げ
        -- k=0 なので sOf F 0 ≥ sOf F 1 は 1 ≥ 1
        exact by
          have : sOf F 0 ≥ sOf F 1 := by
            -- 1 ≥ 1
            -- `by exact le_of_eq (by ...)` でもよい
            subst hn1 hk0
            simp_all only [Nat.choose_zero_right, Rat.natCast_eq_one, Nat.choose_self, not_le,
              le_refl, Nat.add_eq_left, zero_le]

          simpa [hk0] using this



/-- まとめ：ideal except top から、TheoremA の仮定（単調性＆端点一致）を得る -/
lemma sOf_meets_TheoremA_hyps
  (F : Finset (Finset α)) (hI : IdealExceptTop F) :
  let n := Fintype.card α
  let s := sOf (α:=α) F
  (∀ k, k ≤ n-2 → s k ≥ s (k+1)) ∧ s 0 = s n := by
  classical
  intro n s
  have hmono : ∀ k, k ≤ n-2 → s k ≥ s (k+1) := by
    intro k hk;
    simp [s]
    let smo := sOf_monotone_on_init (α:=α) F hI k
    apply sOf_monotone_on_init F hI (Fintype.card α) rfl k
    exact hk
  have hend : s 0 = s n := by
    rcases sOf_endpoints (α:=α) F hI with ⟨h0, hn⟩
    simpa [s, n] using (by rw [h0, hn])
  exact ⟨hmono, hend⟩
