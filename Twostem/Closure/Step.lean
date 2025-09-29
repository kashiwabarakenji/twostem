import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import Twostem.Closure.Core

namespace Twostem

open Closure

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Register `step R` as a generic `Operator`. -/
def Step.op (R : Finset (Rule α)) : Closure.Operator α where
  f    := step R
  mono := step_mono R
  infl := step_infl R

/-- Canonical closure via `step` (reaches a fixed point within `|α|`). -/
@[simp] def Step.cl (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  (Step.op R).lfpInCard I

lemma Step.cl_fixed (R : Finset (Rule α)) (I : Finset α) :
  step R (Step.cl R I) = Step.cl R I :=
  Closure.Operator.fixed_point_at_card (O := Step.op R) I

/-- 特殊化：`(step R)` は `|α|` 回で不動点に到達する。 -/
lemma step_fixed_at_card (R : Finset (Rule α)) (I : Finset α) :
  step R ((step R)^[Fintype.card α] I) = ((step R)^[Fintype.card α] I) := by
  simp
  have h := Closure.Operator.fixed_point_at_card (O := Step.op R) I
  -- h : (Step.op R).f ((Step.op R).lfpInCard I) = (Step.op R).lfpInCard I
  -- 定義を展開して、そのまま返す（simpa を使わず dsimp で書き換え）
  dsimp [Step.op, Closure.Operator.lfpInCard, Closure.Operator.iterate] at h
  exact Finset.left_eq_union.mp (id (Eq.symm h))



/-- 既存の `Nat.iterate` 形に合わせたコロラリ。 -/
private lemma iterate_stable
   (R : Finset (Rule α)) (I : Finset α)
   (C : Finset α) (hC : C = Nat.iterate (step R) (Fintype.card α) I) :
   step R C = C := by
  -- 目標を `(f^[n])` 形に書き換えてから `step_fixed_at_card` を適用
  subst hC
  simpa using step_fixed_at_card (R := R) (I := I)

private lemma closed_subset_iterate {α : Type*} [DecidableEq α]
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

/-- Minimality: any closed `J` with `I ⊆ J` contains `cl R I`. -/
lemma Step.cl_minimal (R : Finset (Rule α)) {I J : Finset α}
  (hIJ : I ⊆ J) (hJ : IsClosed R J) :
  Step.cl R I ⊆ J := by
  -- Reuse your previous `closed_subset_iterate` specialized to `|α|`.
  -- Alternatively, induct on k using Operator.step_subset.
  -- This is a thin shim to keep the API stable.
  classical
    -- まず、与えられた一般補題を k = |α| に適用して
  -- Nat.iterate 形の包含を得る
  have hIter :
      Nat.iterate (step R) (Fintype.card α) I ⊆ J :=
    closed_subset_iterate (R := R) (I := I) (J := J)
      (hI := hIJ) (hJ := hJ) (k := Fintype.card α)

  -- 目標は Step.cl 形：定義を順に展開して Nat.iterate 形に揃える
  -- Step.cl R I = (Step.op R).lfpInCard I
  --              = ((Step.op R).f)^[|α|] I
  --              = (step R)^[|α|] I
  --              = Nat.iterate (step R) |α| I
  change Closure.Operator.iterate (Step.op R) (Fintype.card α) I ⊆ J
  change ((Step.op R).f)^[Fintype.card α] I ⊆ J
  dsimp [Step.op]  -- ((Step.op R).f) = step R
  -- ((step R)^[n] I) は定義的に `Nat.iterate (step R) n I`
  exact hIter


private lemma step_mono_n {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (n : ℕ) :
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

-- 補題: step R X は X を含む
lemma step_subset {α : Type*} [DecidableEq α] (R : Finset (Rule α)) (X : Finset α) :
  step R X ⊇ X := by
  simp [step]

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
