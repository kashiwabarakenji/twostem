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

/-- seed is contained in every iterate (by simple induction). -/
lemma iterate_extensive (O : Operator α) : ∀ n (s : Finset α), s ⊆ O.iterate n s := by
  intro n; induction' n with n ih
  · intro s x hx; exact hx
  · intro s x hx
    have hx' : x ∈ (O.f^[n]) s := ih s hx
    exact (O.step_subset n s) hx'

/-- closure is extensive: `s ⊆ cl s`. -/
lemma closure_extensive (O : Operator α) (s : Finset α) : s ⊆ O.lfpInCard s := by
  intro x hx
  change x ∈ (O.f^[Fintype.card α]) s
  exact (O.iterate_extensive (Fintype.card α) s) hx

/-- closure is monotone w.r.t. inclusion of seeds. -/
lemma closure_monotone (O : Operator α) {s t : Finset α} (h : s ⊆ t) :
  O.lfpInCard s ⊆ O.lfpInCard t := by
  intro x hx
  change x ∈ (O.f^[Fintype.card α]) t
  have monoN := O.iterate_mono (Fintype.card α)
  exact monoN h hx

/-- if `S` is a fixed point, all iterates stay at `S`. -/
lemma iterate_fixed_of_fixed (O : Operator α) {S : Finset α}
  (hfix : O.f S = S) : ∀ n, O.iterate n S = S := by
  intro n; induction' n with n ih
  · rfl
  · calc
      (O.f^[n+1]) S = O.f ((O.f^[n]) S) := by rw [Function.iterate_succ_apply']
      _             = O.f S             := by exact congrArg O.f ih
      _             = S                 := hfix

/-- idempotence of the closure: `cl (cl s) = cl s`. -/
lemma closure_idem (O : Operator α) (s : Finset α) :
  O.lfpInCard (O.lfpInCard s) = O.lfpInCard s := by
  -- first, `cl s` is a fixed point
  have hfix : O.f (O.lfpInCard s) = O.lfpInCard s := fixed_point_at_card (O := O) (I := s)
  -- iterating from a fixed point stays there
  have hstay := iterate_fixed_of_fixed (O := O) (S := O.lfpInCard s) hfix (Fintype.card α)
  -- expand lfpInCard on the LHS
  change (O.f^[Fintype.card α]) (O.lfpInCard s) = O.lfpInCard s
  exact hstay

/-- cardinality bounds for closure. -/
lemma closure_card_bounds (O : Operator α) (s : Finset α) :
  s.card ≤ (O.lfpInCard s).card ∧ (O.lfpInCard s).card ≤ Fintype.card α := by
  have hsubset : s ⊆ O.lfpInCard s := O.closure_extensive s
  have hle_left : s.card ≤ (O.lfpInCard s).card := by
    exact Finset.card_le_card hsubset
    --Finset.card_le_of_subset hsubset
  have hle_right : (O.lfpInCard s).card ≤ Fintype.card α := Finset.card_le_univ _
  exact And.intro hle_left hle_right

/-- minimality: any fixed point `J` with `s ⊆ J` contains the closure of `s`. -/
lemma closure_minimal (O : Operator α) {s J : Finset α}
  (hsJ : s ⊆ J) (hJfix : O.f J = J) :
  O.lfpInCard s ⊆ J := by
  -- show (f^[k]) s ⊆ J for all k by induction
  have stepInc : ∀ k, (O.f^[k]) s ⊆ J := by
    intro k; induction' k with k ih
    · exact hsJ
    · intro x hx
      -- (f^[k+1]) s = f ((f^[k]) s) ⊆ f J = J
      have e := Function.iterate_succ_apply' O.f k s
      have hx' : x ∈ O.f ((O.f^[k]) s) := Eq.mp (congrArg (fun t => x ∈ t) e) hx
      have hmono : O.f ((O.f^[k]) s) ⊆ O.f J := O.mono ih
      have hx'' : x ∈ O.f J := hmono hx'
      exact Eq.mp (congrArg (fun t => x ∈ t) hJfix) hx''
  intro x hx
  -- rewrite lfpInCard and use k = |α|
  have : O.lfpInCard s = (O.f^[Fintype.card α]) s := rfl
  have hx' : x ∈ (O.f^[Fintype.card α]) s := by
    -- cast along rfl (explicit)
    exact hx
  exact stepInc (Fintype.card α) hx'

--/***********************
-- * 0. TwoStem / UC / NoEmpty
-- ***********************/
--こちらは、Rに対する条件。TwoStemという個別のルールに対する条件もある。
def TwoStemR (R : Finset (Rule α)) : Prop :=
  ∀ t ∈ R, (t.prem.card ≤ 2)



--非空前提。Ruleを一般のステムとして定義しているので、自動的には満たされない。
def NoEmptyPremise (R : Finset (Rule α)) : Prop :=
  ∀ t ∈ R, t.prem ≠ ∅




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
