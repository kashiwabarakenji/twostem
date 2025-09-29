import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot

namespace Twostem

open scoped BigOperators

/-- Horn ルール：prem は前提の有限集合，head は結論の頂点 -/
structure Rule (α : Type _) where
  prem : Finset α
  head : α
deriving DecidableEq

/-- Horn 系 -/
structure Sys (α : Type _) where
  R : Finset (Rule α)
deriving DecidableEq

variable {α : Type _} [DecidableEq α]

--使ってないかも。
/-- Two-Stem: 前提サイズ ≤ 2 -/
def TwoStem (t : Rule α) : Prop := t.prem.card ≤ 2

--使ってないし、空前提なしの仮定は別のところにある。
/-- NoEmpty Premise: 空前提なし -/
def NoEmpty (t : Rule α) : Prop := t.prem.Nonempty

--UniqueChildという同値な仮定がBridge.leanにある。
/-- UniqueChild (UC): 各 head ごとに規則は高々1本 -/
def UC (R : Finset (Rule α)) : Prop :=
  ∀ a : α, (R.filter (fun t => t.head = a)).card ≤ 1

--下のmem_support_iffで使っているだけ。
/-- サポート：前提か head に出現する点の集合 -/
def support (R : Finset (Rule α)) : Finset α :=
  (R.biUnion (fun t => t.prem ∪ {t.head}))

lemma mem_support_iff {R : Finset (Rule α)} {x : α} :
    x ∈ support R ↔ ∃ t ∈ R, x ∈ t.prem ∪ {t.head} := by
  classical
  unfold support
  simp [Finset.mem_biUnion]

/-- 閉集合判定：I が R-閉である -/
def IsClosed (R : Finset (Rule α)) (I : Finset α) : Prop :=
  ∀ ⦃t : Rule α⦄, t ∈ R → t.prem ⊆ I → t.head ∈ I

/-- 与えられた集合 X を入力としたときに「発火する」ルールの結論の集合 -/
def fires (R : Finset (Rule α)) (X : Finset α) : Finset α :=
  (R.filter (fun t => t.prem ⊆ X)).image (fun t => t.head)

--step2という似たものがあるが、中身が違う。
/-- closure の“定義論的”候補：I を含む最小の R-閉集合（交わり定義） -/
def step (R : Finset (Rule α)) (X : Finset α) : Finset α :=
  X ∪ fires R X

/-- 反復 (高々 `Fintype.card α` 回で安定)。 -/
def definitionalClosureIter
   [Fintype α]  [DecidableEq α]
    (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  Nat.iterate (step R) (Fintype.card α) I

-- 補題: step R X は X を含む
lemma step_subset {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (X : Finset α) :
  step R X ⊇ X := by
  simp [step]

lemma fires_mono {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
    Monotone (fires R) := by
  intro X Y h x hx
  dsimp [fires]
  dsimp [fires] at hx
  simp_all
  rcases hx with ⟨t, htR, htprem, rfl⟩
  use t
  constructor
  · constructor
    · exact htR.1
    · obtain ⟨left, right⟩ := htR
      exact right.trans h
  · exact rfl

lemma step_mono {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
  Monotone (step R) := by
  intro X Y hXY
  simp [step, fires]
  apply Finset.union_subset_union
  · exact hXY
  · exact fires_mono R hXY

lemma step_mono_n {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (n : ℕ) :
  Monotone (Nat.iterate (step R) n) := by
  induction n with
  | zero =>
    simp [Nat.iterate]
    exact fun X Y hXY => hXY
  | succ n ih =>
    intro X Y hXY
    calc
      (step R)^[n.succ] X = (step R) ((step R)^[n] X) := by
        exact Function.iterate_succ_apply' (step R) n X
      _ ⊆ (step R) ((step R)^[n] Y) := step_mono R (ih hXY)
      _ = (step R)^[n.succ] Y := by exact Eq.symm (Function.iterate_succ_apply' (step R) n Y)

-- 補題: step の n 回反復は I を含む
lemma iterate_subset {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) (n : ℕ) :
  Nat.iterate (step R) n I ⊇ I := by
  induction n generalizing I with
  | zero =>
    simp [Nat.iterate]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply Finset.Subset.trans
    exact ih I
    have : I ⊆ step R I := by exact step_subset R I
    exact step_mono_n R n this

-- 補題: step で拡張されると集合のサイズが増加する
lemma lt_neq_subset {α : Type*} [DecidableEq α] (X Z : Finset α) (h_subset : X ⊆ Z) (h_neq : ¬(Z = X)) :
  Z.card > X.card := by
  have h_nonempty : (Z \ X).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have : Z = X := by
      ext x
      constructor
      · intro hx
        simp_all only [Finset.sdiff_eq_empty_iff_subset]
        exact h_empty hx
      · intro hx
        exact h_subset hx
    contradiction
  have h_sdiff_card : (Z \ X).card = Z.card - X.card := by
    rw [Finset.card_sdiff h_subset]
  have h_pos : (Z \ X).card > 0 := by
    exact Finset.card_pos.mpr h_nonempty
  rw [h_sdiff_card] at h_pos
  apply Nat.lt_of_sub_pos
  exact h_pos

lemma card_lt_of_step {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (X : Finset α)
  (h_neq : step R X ≠ X) :
  (step R X).card > X.card := by
  exact (@lt_neq_subset α _ X (step R X) (step_subset R X) h_neq)

lemma stable_iterate {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) (k : ℕ)
    (h_stable : step R (Nat.iterate (step R) k I) = Nat.iterate (step R) k I) :
    ∀ n ≥ k, Nat.iterate (step R) n I = Nat.iterate (step R) k I := by
  intro n hn
  refine Nat.le_induction (by rfl) (fun m hm h => ?_) n hn
  rw [Function.iterate_succ_apply]
  rw [←h_stable]
  rw [←h]
  rw [←Nat.iterate]
  exact Function.iterate_succ_apply' (step R) m I


omit [DecidableEq α] in
/-- s ⊊ t なら濃度は厳密に増える（有限型の上で） -/
lemma Set.ncard_lt_of_ssubset [Fintype α] [DecidableEq α]
    {s t : Set α} (h : s ⊂ t) : s.ncard < t.ncard := by
  classical
  -- `t` は有限（有限宇宙の部分集合）なので `ncard_lt_ncard` が使える
  have ht : t.Finite := (Set.finite_univ : (Set.univ : Set α).Finite).subset (by
    intro x hx
    exact trivial
  )
  -- `Set.ncard_lt_ncard` は `s ⊂ t` と `t.Finite` から結論を返す
  simpa using Set.ncard_lt_ncard h ht

/-- 自然数列が `0..n` で連続して厳密増加なら，`n+1` ステップで少なくとも `n+1` だけ増える -/
lemma Nat.strictChain_gain {a : ℕ → ℕ} :
    ∀ n, (∀ k ≤ n, a k < a (k+1)) → a (n+1) ≥ a 0 + (n+1) := by
  intro n
  induction' n with n ih
  · intro h
    have h0 : a 0 < a 1 := h 0 (Nat.le_refl 0)
    exact Nat.succ_le_of_lt h0
  · intro h
    have hstep : a (n+1) < a (n+2) := h (n+1) (Nat.le_refl _)
    have hprev : ∀ k ≤ n, a k < a (k+1) := by
      intro k hk
      exact h k (Nat.le_trans hk (Nat.le_succ _))
    have ih' := ih hprev
    -- a (n+2) ≥ a (n+1) + 1 ≥ (a 0 + (n+1)) + 1
    have : a (n+2) ≥ a (n+1) + 1 := Nat.succ_le_of_lt hstep
    simp_all only [implies_true, ge_iff_le, le_refl]
    linarith

/- Abstract.leanに移した。
/- 有限集合上では，長さ `card α + 1` の厳密包含列は存在しない -/
omit [DecidableEq α] in
lemma no_strict_chain_up_to_card [Fintype α] [DecidableEq α]
    (A : ℕ → Set α) :
    ¬ (∀ k ≤ Fintype.card α, A k ⊂ A (k+1)) := by
  classical
  intro h
  -- 濃度が各段で 1 以上増える
  have hlt : ∀ k ≤ Fintype.card α, (A k).ncard < (A (k+1)).ncard := by
    intro k hk
    exact Set.ncard_lt_of_ssubset (h k hk)
  -- よって `(card α + 1)` 段後の濃度は少なくとも `a 0 + (card α + 1)`
  have grow := Nat.strictChain_gain (a := fun k => (A k).ncard) (Fintype.card α) hlt
  -- しかし任意の部分集合の濃度は `card α` を超えない
  have upper : (A (Fintype.card α + 1)).ncard ≤ Fintype.card α := by
    classical
    have hfin :
        (A (Fintype.card α + 1)).toFinset.card
          ≤ (Finset.univ : Finset α).card := by
      -- `toFinset ⊆ univ`
      simp_all only [ge_iff_le, Set.toFinset_card, Fintype.card_ofFinset, Finset.card_univ]
      exact Finset.card_filter_le _ _

    -- `ncard = toFinset.card` と `card_univ = Fintype.card α`
    simp
    convert hfin
    exact Set.ncard_eq_toFinset_card' (A (Fintype.card α + 1))
  -- `a 0 ≥ 0` なので `a 0 + (card α + 1) ≤ card α` は不可能
  have : (A 0).ncard + (Fintype.card α + 1) ≤ Fintype.card α :=
    le_trans grow upper
  apply Nat.lt_irrefl _ (lt_of_le_of_lt this ?_)
  simp_all only [ge_iff_le]
  linarith
-/
/- abstract.leanに移した。
omit [DecidableEq α] in
lemma impossible_all_strict_iterate [Fintype α] [DecidableEq α]
    (f : Set α → Set α) (s : Set α) :
    ¬ (∀ k ≤ Fintype.card α, (Nat.iterate f k) s ⊂ (Nat.iterate f (k+1)) s) :=
  no_strict_chain_up_to_card (A := fun k => (Nat.iterate f k) s)
-/

--Closure.leanと内容がかぶっている部分があるかも。
/-- 拡大的（inflationary）性：すべての `s` について `s ⊆ f s`. -/
def Inflationary (f : Set α → Set α) : Prop :=
  ∀ s : Set α, s ⊆ f s

--FinsetのF
def InflationaryF (f : Finset α → Finset α) : Prop :=
  ∀ s : Finset α, s ⊆ f s

--使っている。
lemma step_infl {α : Type*} [DecidableEq α] (R : Finset (Rule α)) :
  InflationaryF (step R) := by
  intro s
  simp [step]

/-abstract.leanに移した。
omit [DecidableEq α] in
/-- 単調かつ拡大的な作用素は、`|V|` 回の反復で必ず停止する（点ごと） -/
private lemma iterate_stops_in_card [DecidableEq α] [Fintype α]
    (f : Set α → Set α)
    (_ : Monotone f)
    (infl : Inflationary f)
    (s : Set α)
    : (Nat.iterate f (Fintype.card α)) s = (Nat.iterate f (Fintype.card α + 1)) s := by
  classical
  -- 反復列 S k := f^[k] s は包含増加列
  have step : ∀ k : ℕ, (Nat.iterate f k) s ⊆ (Nat.iterate f (k+1)) s := by
    intro k
    -- `inflate` を `f^[k] s` に適用してから `iterate_succ` で書き換え

    rw [Function.iterate_succ']
    exact infl (f^[k] s)

  -- もし `f^[n] s ⊊ f^[n+1] s` なら，0..n のすべてで真包含が起きてしまい，濃度が n+1 回増えるはず
  -- だが `|V|=n` なので不可能．よって等号でなければならない．
  -- この論法を反映するために，真包含が連続して起こることはないと示す。
  have impossible_all_strict :=
    impossible_all_strict_iterate (f := f) (s := s)

  -- よって 0..n のどこかで真包含が破れる＝等号になる
  have exists_eq :
      ∃ k ≤ Fintype.card α, (Nat.iterate f k) s = (Nat.iterate f (k+1)) s := by
    by_contra h
    -- 「どこにも等号がない」⇔「すべて真包含」の反対を使って矛盾
    -- （detail：`not_exists` と `not_and_or` 展開で `impossible_all_strict` に反する）
    exact impossible_all_strict (by
      intro k hk
      have hk' : (Nat.iterate f k) s ⊆ (Nat.iterate f (k+1)) s := step k
      have hne : (Nat.iterate f k) s ≠ (Nat.iterate f (k+1)) s := by
        have : ¬ (Nat.iterate f k s = Nat.iterate f (k+1) s) := by
          exact by
            -- 仮定 `h` から等号の存在を否定しているので，この k でも等号ではない
            -- 展開詳細は省略
            simp_all only [Function.iterate_succ, Function.comp_apply, not_forall, not_exists,
              not_and, not_false_eq_true]

        exact this
      exact Set.ssubset_iff_subset_ne.mpr ⟨hk', hne⟩
    )

  -- 一度等号になれば以後ずっと等号（`step` と単調性から）
  obtain ⟨k, hk, heq⟩ := exists_eq
  -- k ≤ n なので，とくに n の段でも等号になる
  -- `f^[k] s = f^[k+1] s` から，`f^[n] s = f^[n+1] s` を導く（増加列なので伝播）
  -- 伝播は `iterate` の連鎖で帰納
  have propagate : ∀ m, k ≤ m → (Nat.iterate f m) s = (Nat.iterate f (m+1)) s := by
    intro m hm
    -- `m = k + t` として単純な帰納法。詳細は省略（`Nat.rec` で書けます）
    -- 実装メモ：`iterate_succ` と `heq` を繰り返し使うだけです。
    --refine Nat.le_induction ?_ (fun n hn h => ?_) m hm
    let t := m - k
    have hm' : m = k + t := by omega
    induction t generalizing m with
    | zero =>
      rw [hm']
      rw [add_comm]
      rw [add_assoc]
      --rw [add_comm (t+k) 1]
      --rw [←add_assoc]
      rw [@Function.iterate_add_apply]
      rw [@Function.iterate_add_apply]
      rw [heq]
    | succ m ih =>
    · rw [hm']
      rw [add_comm]
      rw [add_assoc]
      rw [@Function.iterate_add_apply]
      rw [@Function.iterate_add_apply]
      rw [heq]

  have : (Nat.iterate f (Fintype.card α)) s = (Nat.iterate f (Fintype.card α + 1)) s :=
    propagate (Fintype.card α) hk

  exact this
-/

private lemma iterate_eq_propagate {β : Type*} (f : β → β) (s : β)
    {k m : ℕ} (hkm : k ≤ m)
    (heq : (Nat.iterate f k) s = (Nat.iterate f (k+1)) s) :
    (Nat.iterate f m) s = (Nat.iterate f (m+1)) s := by
  classical
  -- 差 `t := m - k` に帰着
  have hk : m = k + (m - k) := by exact Eq.symm (Nat.add_sub_of_le hkm)
  -- `k` から `k + t` まで等式が伝播することを示す補題を `t` で帰納
  have prop : ∀ t, (Nat.iterate f (k + t)) s = (Nat.iterate f (k + t + 1)) s := by
    intro t
    induction t
    case zero => -- t = 0
      simpa [Nat.add_zero, Nat.add_comm] using heq
    case succ t ih => -- t → t+1
      calc
        (Nat.iterate f (k + (t+1))) s
            = (Nat.iterate f (k + t + 1)) s := by simp [Nat.add_assoc]
        _   = f ((Nat.iterate f (k + t)) s) := by
              -- (f^[n+1]) s = f ((f^[n]) s)
              rw [Function.iterate_succ']
              exact rfl
        _   = f ((Nat.iterate f (k + t + 1)) s) := by
              -- 帰納法の仮定を f で像に
              simpa [Nat.add_assoc] using congrArg f ih
        _   = (Nat.iterate f (k + t + 2)) s := by
              -- 逆向きに (iterate_succ') を使って戻す
              have : (Nat.iterate f (k + t + 2)) s
                       = f ((Nat.iterate f (k + t + 1)) s) := by
                let fi := Function.iterate_succ_apply' f (k + t + 1) s
                exact fi

              simpa [Nat.add_assoc] using this.symm
  -- 目的の `m` について結論
  rw [hk]
  rw [Nat.add_comm]
  let pp := prop (m - k)
  ring_nf at pp
  rw [add_assoc]
  rw [add_comm]
  rw [pp]
  rw [add_comm]
  rw [add_comm 1 k]

/- Abstract.leanに移した。
lemma fixed_point_at_card {α : Type*} [Fintype α] [DecidableEq α] (R : Finset (Rule α)) (I : Finset α) :
    step R (Nat.iterate (step R) (Fintype.card α) I) = Nat.iterate (step R) (Fintype.card α) I := by
--lemma fixed_point_at_card {α : Type*} [Fintype α] [DecidableEq α]
--    (R : Finset (Rule α)) (I : Finset α) :
--    step R (Nat.iterate (step R) (Fintype.card α) I)
--      = Nat.iterate (step R) (Fintype.card α + 1) I := by
  classical
  -- 単調＆拡大的
  have mono : Monotone (step R) := step_mono (R := R)
  have infl : ∀ s : Finset α, s ⊆ step R s := step_infl (R := R)
  -- 反復列は包含増加
  have step_subset :
      ∀ k, (Nat.iterate (step R) k) I ⊆ (Nat.iterate (step R) (k+1)) I := by
    intro k x hx
    -- infl : ∀ s, s ⊆ step R s  を s := (step R)^[k] I に適用
    have hx' : x ∈ step R ((Nat.iterate (step R) k) I) :=
      infl ((Nat.iterate (step R) k) I) hx
    -- 右辺を iterate_succ' で書き換えて目標に一致させる
    simp at hx'
    simp
    rw [←Function.iterate_succ_apply (step R) k I]
    rw [←Function.iterate_succ_apply' (step R) k I] at hx'
    exact hx'

  -- 「全ての k ≤ |α| で真包含」は不可能
  have not_all_strict :
      ¬ (∀ k ≤ Fintype.card α,
            (Nat.iterate (step R) k) I ⊂ (Nat.iterate (step R) (k+1)) I) := by
    exact no_strict_chain_up_to_card fun k => Membership.mem ((step R)^[k] I).val

  -- よってある k ≤ |α| で等号
  have exists_eq :
      ∃ k ≤ Fintype.card α,
        (Nat.iterate (step R) k) I = (Nat.iterate (step R) (k+1)) I := by
    classical
    by_contra h
    -- すべて≠ なら，包含と合わせて真包含
    have all_strict :
        ∀ k ≤ Fintype.card α,
          (Nat.iterate (step R) k) I ⊂ (Nat.iterate (step R) (k+1)) I := by
      intro k hk
      have hsub : (Nat.iterate (step R) k) I
                  ⊆ (Nat.iterate (step R) (k+1)) I := step_subset k
      have hne : (Nat.iterate (step R) k) I
                  ≠ (Nat.iterate (step R) (k+1)) I := by
        -- 「等号が存在しない」仮定から `k` でも ≠
        have : ¬ ((Nat.iterate (step R) k) I
                  = (Nat.iterate (step R) (k+1)) I) := by
          -- `h : ¬ ∃ k ≤ n, eq` を `forall` に展開
          have h' : ∀ k ≤ Fintype.card α,
              (Nat.iterate (step R) k) I
              ≠ (Nat.iterate (step R) (k+1)) I := by
            intro k hk; exact by
              have := not_exists.mp h k
              -- 上の行は `not_exists` を二重に解く必要があるので，
              -- 直接書き下すのが煩雑なら次の 2 行の形にしてもOKです：
              -- have := (not_exists.mp h) k
              -- exact (not_exists.mp this) hk
              -- ここでは簡略化のために `by` ブロックで丁寧に展開する方が安全です。
              simp_all only [Function.iterate_succ, Function.comp_apply, not_forall, not_exists,
                not_and, and_false, not_false_eq_true, ne_eq]

          exact h' k hk
        exact this
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    exact not_all_strict all_strict

  obtain ⟨k, hk, heq⟩ := exists_eq

  -- 等号の伝播で n 段でも等号に
  have propagate :=
    iterate_eq_propagate (step R) I (k := k) (m := Fintype.card α) hk heq
  -- ゴールは `f^[n+1] I` の形なので `iterate_succ'` を使って左辺を書き換え
  -- 左辺はすでに `step R (f^[n] I)` の形

  have propagate' :
      (step R)^[Fintype.card α] I
        = step R ((step R)^[Fintype.card α] I) := by
    rw [←Function.iterate_succ_apply' (step R) (Fintype.card α) I]
    exact propagate
  simpa using propagate'.symm
-/

/- Abstract.leanに移した。
omit [DecidableEq α] in
lemma iterate_stable [Fintype α] [DecidableEq α] {R : Finset (Rule α)} {I : Finset α}
   (C : Finset α) (h_C : C = Nat.iterate (step R) (Fintype.card α) I):
    --(_ : step R (Nat.iterate (step R) k I) = Nat.iterate (step R) k I) :
    step R C = C := by
  rw [h_C]

  let fpc := fixed_point_at_card R I
  rw [fpc]
  exact step R (Nat.iterate (step R) (Fintype.card α) I) = Nat.iterate (step R) (Fintype.card α) I
-/
/-
omit [DecidableEq α] in
-- 補題: step が C で安定しないなら、k と k+1 の反復は異なる
lemma iterate_neq [Fintype α] [DecidableEq α] {R : Finset (Rule α)} {I : Finset α}
  (k : ℕ) (h_step_neq : step R (Nat.iterate (step R) (Fintype.card α) I) ≠ Nat.iterate (step R) (Fintype.card α) I) :
  Nat.iterate (step R) (k + 1) I ≠ Nat.iterate (step R) k I := by
  intro eq
  have h_stable : step R (Nat.iterate (step R) k I) = Nat.iterate (step R) k I := by
    rw [←Function.iterate_succ_apply' (step R) k I]
    exact eq
  have h_C_stable : step R (Nat.iterate (step R) (Fintype.card α) I) = Nat.iterate (step R) (Fintype.card α) I := by
    apply iterate_stable _ rfl
  exact h_step_neq h_C_stable
-/
/-
omit [DecidableEq α] in
-- 補題: step が安定しない場合、k 回の反復のサイズは k 以上
lemma iterates_card_increasing [Fintype α] [DecidableEq α] {R : Finset (Rule α)} {I : Finset α}
  (k : ℕ) (h_step_neq : step R (Nat.iterate (step R) (Fintype.card α) I) ≠ Nat.iterate (step R) (Fintype.card α) I) :
  (Nat.iterate (step R) k I).card ≥ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_k : (Nat.iterate (step R) k I).card ≥ k := by
      simp_all only [ne_eq, ge_iff_le]
    have h_step_k : step R (Nat.iterate (step R) k I) ⊇ Nat.iterate (step R) k I := step_subset R _
    have h_neq : Nat.iterate (step R) (k + 1) I ≠ Nat.iterate (step R) k I := by
      apply iterate_neq k h_step_neq
    have h_size : (Nat.iterate (step R) (k + 1) I).card > (Nat.iterate (step R) k I).card := by
    -- 包含： (step R)^[k] I ⊆ (step R)^[k+1] I
      have hsubset :
          (Nat.iterate (step R) k I) ⊆ (Nat.iterate (step R) (k + 1) I) := by
        -- step_infl : ∀ s, s ⊆ step R s
        -- RHS を iterate_succ' で `step R ((step R)^[k] I)` にそろえる
        rw [Function.iterate_succ']
        exact h_step_k
           -- 不等号を ssubset 用に左 ≠ 右 の向きに
      have hne :
          (Nat.iterate (step R) k I) ≠ (Nat.iterate (step R) (k + 1) I) := by
        -- もし等しければ、与えられた h_neq と矛盾
        intro h; exact h_neq h.symm
      -- 真包含
      have hss :
          (Nat.iterate (step R) k I) ⊂ (Nat.iterate (step R) (k + 1) I) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
      -- 濃度の厳密増加
      exact Finset.card_lt_card hss
    linarith
-/
/-Step.leanに移した。
-- 補題: 閉集合 J が I を含むなら、すべての反復は J に含まれる
lemma closed_subset_iterate {α : Type*} [DecidableEq α]
  {R : Finset (Rule α)} {I J : Finset α}
  (hI : I ⊆ J) (hJ : IsClosed R J) (k : ℕ) :
  Nat.iterate (step R) k I ⊆ J := by
  classical
  induction k with
  | zero =>
    simpa using hI
  | succ k ih =>
    -- 目標：(step R)^[k+1] I ⊆ J
    -- iterate を 1 回ほどいて `step R ((step R)^[k] I) ⊆ J` を示せばよい
    have hsubset : step R ((Nat.iterate (step R) k) I) ⊆ J := by
      intro a ha
      -- `ha : a ∈ (step R) ( (step R)^[k] I )` を分解
      have : a ∈ (Nat.iterate (step R) k I) ∨
              a ∈ fires R ((Nat.iterate (step R) k I)) := by
        -- step = X ∪ fires R X
        simpa [step] using ha
      cases this with
      | inl hx =>
        -- もともと X にいたなら、帰納法の仮定で J に入る
        exact ih hx
      | inr hfire =>
        -- fires にいたなら、対応する規則 t を取り出して IsClosed を適用
        rcases Finset.mem_image.mp hfire with ⟨t, ht, rfl⟩
        rcases Finset.mem_filter.mp ht with ⟨hR, hprem⟩
        have hpremJ : t.prem ⊆ J := hprem.trans ih
        exact hJ hR hpremJ
    -- もとの目標に戻す

    intro a ha
    -- 等式 `iterate_succ'` を集合メンバーシップに持ち上げる
    have e :=
      congrArg (fun S => a ∈ S) (Function.iterate_succ_apply' (step R) k I)
      -- e : (a ∈ (step R)^[k+1] I) = (a ∈ step R ((step R)^[k] I))
    -- `ha : a ∈ (step R)^[k+1] I` を右辺の形に変換
    have ha' : a ∈ step R ((Nat.iterate (step R) k) I) := Eq.mp e ha
    -- 先に示した包含に流し込む
    exact hsubset ha'
-/

/-
-- 本命の証明: 定義論的閉包の性質
omit [DecidableEq α] in
lemma definitionalClosure_spec [Fintype α] [DecidableEq α] {R : Finset (Rule α)} {I : Finset α} :
  I ⊆ definitionalClosureIter R I ∧
  IsClosed R (definitionalClosureIter R I) ∧
  ∀ J, I ⊆ J → IsClosed R J → definitionalClosureIter R I ⊆ J := by
  let C := definitionalClosureIter R I
  refine ⟨?_, ?_, ?_⟩
  · -- 第一部分: I ⊆ C
    exact iterate_subset R I (Fintype.card α)
  · -- 第二部分: IsClosed R C
    intro t ht h_prem
    have : t.head ∈ step R C := by
      simp [step, fires]
      simp_all only [C]
      exact Or.inr ⟨t, ⟨ht, h_prem⟩, rfl⟩

    by_contra h_not_closed
    have h_step_neq : step R C ≠ C := by
      intro eq
      simp_all only [C]
    have h_step_C : step R C ⊇ C := step_subset R C
    have h_size_bound : C.card ≤ Fintype.card α := Finset.card_le_univ C
    have h_ind : ∀ k ≤ Fintype.card α + 1, (Nat.iterate (step R) k I).card ≥ k := by
      intro k hk
      induction k with
      | zero =>
        simp
      | succ k ih =>
        exact iterates_card_increasing (k + 1) h_step_neq
    have h_size2 : (Nat.iterate (step R) (Fintype.card α + 1) I).card ≤ Fintype.card α := Finset.card_le_univ _
    have h_le : Fintype.card α + 1 ≤ Fintype.card α := le_trans (h_ind (Fintype.card α + 1) le_rfl) h_size2
    linarith
  · -- 第三部分: 最小性
    intro J hI hJ
    exact closed_subset_iterate hI hJ (Fintype.card α)
-/

end Twostem
