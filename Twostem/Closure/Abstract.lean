import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import LeanCopilot

namespace Closure

open scoped BigOperators
open Function

variable {α : Type*}[DecidableEq α] [Fintype α]
variable {β : Type*}[DecidableEq β] [Fintype β]

/-- Horn ルール：prem は前提の有限集合，head は結論の頂点 -/
structure Rule (α : Type*) where
  prem : Finset α
  head : α
deriving DecidableEq

/-- A generic closure-like operator on finite sets: monotone and inflationary. -/
structure Operator (α : Type*) [DecidableEq α] [Fintype α] where
  f    : Finset α → Finset α
  mono : Monotone f
  infl : ∀ s, s ⊆ f s

namespace Operator

/-- n-times iterate of the operator. -/
def iterate (O : Operator α) (n : ℕ) : Finset α → Finset α := (O.f)^[n]

lemma iterate_mono (O : Operator α) (n : ℕ) : Monotone (O.iterate n) := by
  induction n with
  | zero =>
    simp [iterate]
    exact fun ⦃a b⦄ a => a
  | succ n ih =>
  · intro X Y h;
    simpa [iterate, Function.iterate_succ_apply'] using O.mono (ih h)

/-- The canonical limit after `|α|` iterations. -/
def lfpInCard (O : Operator α) (I : Finset α) : Finset α :=
  O.iterate (Fintype.card α) I

/-- Each iterate includes the previous one (inflationary). -/
lemma step_subset (O : Operator α) :
  ∀ k (I : Finset α), O.iterate k I ⊆ O.iterate (k+1) I := by
  intro k I x hx
  have := O.infl (O.iterate k I) hx
  simpa [iterate, Function.iterate_succ_apply'] using this

omit [Fintype α][DecidableEq α] in
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

/-- No strictly increasing chain of subsets of length `|α|+1` on a finite ground set. -/
lemma no_strict_chain_up_to_card (A : ℕ → Set α) :
  ¬ (∀ k ≤ Fintype.card α, A k ⊂ A (k+1)) := by
  -- You already have this in your second group as `no_strict_chain_up_to_card`.
  -- Import and reuse, or port the proof here.
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

/-- There exists `k ≤ |α|` where the iterate stabilizes. -/
lemma exists_eq_at_le_card (O : Operator α) (I : Finset α) :
  ∃ k ≤ Fintype.card α, O.iterate k I = O.iterate (k+1) I := by
  -- Reuse your `impossible_all_strict_iterate` + `step_subset`.
  by_contra h
  have hchain : ∀ k ≤ Fintype.card α, O.iterate k I ⊂ O.iterate (k+1) I := by
    intro k hk
    -- subset part (inflationary step)
    have hsub : (O.iterate k I : Set α) ⊆ (O.iterate (k+1) I : Set α) := by
      intro x hx
      -- hx : x ∈ (O.iterate k I : Set α)
      have hx' : x ∈ O.iterate k I := by simpa using hx
      have hx'' : x ∈ O.iterate (k+1) I := (O.step_subset k I) hx'
      simpa using hx''
    -- inequality part (no equality at any k ≤ |α|)
    have hne_fin : O.iterate k I ≠ O.iterate (k+1) I := by
      intro heq
      exact h ⟨k, hk, heq⟩
    -- lift to set-inequality
    have hne_set :
        (O.iterate k I : Set α) ≠ (O.iterate (k+1) I : Set α) := by
      intro heq
      apply hne_fin
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hx_set : x ∈ (O.iterate k I : Set α) := by simpa using hx
        have : x ∈ (O.iterate (k+1) I : Set α) := by simpa [heq] using hx_set
        simpa using this
      · intro hx
        have hx_set : x ∈ (O.iterate (k+1) I : Set α) := by simpa using hx
        have : x ∈ (O.iterate k I : Set α) := by simpa [heq] using hx_set
        simpa using this
    -- conclude strict inclusion on sets
    exact HasSubset.Subset.ssubset_of_ne hsub hne_fin
  exact no_strict_chain_up_to_card (fun k => (O.iterate k I : Set α)) hchain

omit [DecidableEq β] [Fintype β] in
/-- Once equal at `k`, equal for all `m ≥ k`. -/
lemma iterate_eq_propagate  (f : β → β) (s : β)
    {k m : ℕ} (hkm : k ≤ m)
    (heq : (f^[k]) s = (f^[k+1]) s) :
    (f^[m]) s = (f^[m+1]) s := by
  -- You already have this as `iterate_eq_propagate`; keep single source here.
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
              have :k + t + 1 = (k + t).succ := by simp [Nat.add_assoc]
              rw [this]
              let fi := Function.iterate_succ' f (k + t)
              exact congrFun fi s
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

/-- Fixed point at `|α|` steps. -/
lemma fixed_point_at_card (O : Operator α) (I : Finset α) :
  O.f (O.lfpInCard I) = O.lfpInCard I := by
  rcases exists_eq_at_le_card (O := O) (I := I) with ⟨k, hk, heq⟩
  -- propagate to `|α|`
  have := iterate_eq_propagate (O.f) I (k := k) (m := Fintype.card α) hk heq
  simpa [lfpInCard, iterate, Function.iterate_succ_apply'] using this.symm

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
end Operator
