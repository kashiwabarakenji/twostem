import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF
import Twostem.Basic
import Twostem.General
import Twostem.ProblemA
import Twostem.ProblemC
import Twostem.SCC
import LeanCopilot
open scoped Rat
--import Mathlib.Tactic.NormCast

open scoped BigOperators
open Classical

universe u
variable {α : Type u} [DecidableEq α]

noncomputable instance {α : Type u}  [DecidableEq α] {V : Finset α} {R : Finset (α × α × α)} (t : α × α × α) : Decidable (ThreadA.BarrierHyp V R t) :=
  Classical.dec _

/-- 仕上げ（マスタ定理）：
非空なら必ず peel か safe shrink が見つかる、という存在を仮定すれば TwoStem。 -/

theorem TwoStem_from_peel_or_shrink
  (V : Finset α)
  (Exist :
    ∀ R, supportedOn V R → R ≠ ∅ → PeelOrShrink V R)
  : ∀ R, supportedOn V R → NDS2 V (family V R) ≤ 0 := by
  classical
  intro R hV
  -- |R| に関する強い帰納（motive を明示し、n := R.card を与える）
  refine
    (Nat.strongRecOn
      (motive :=
        fun n =>
          ∀ R', R'.card = n → supportedOn V R' → NDS2 V (family V R') ≤ 0)
      (n := R.card)
      (fun n IH => ?step)) R rfl hV
  -- ここから、固定された n に対して示すべき一般形
  --   ∀ R', R'.card = n → supportedOn V R' → ...
  -- を証明する
  · intro R hcard hV
    by_cases hE : R = (∅ : Finset (Rule α))
    · -- 基底：空族
      have h0 := NDS2_family_empty_zero (V := V)
      simp_all only [ne_eq, Finset.card_empty, le_refl]
    · -- 非空：peel か shrink
      have hExist := Exist R hV hE
      cases hExist with
      | inl hPeel =>
          rcases hPeel with ⟨t0, hw⟩
          -- 一歩の非減
          have step_nondec := hw.nondec
          -- カード減少
          have hlt : (R.erase t0).card < R.card :=
            Finset.card_erase_lt_of_mem hw.mem
          -- 右辺の R.card を n に書き換え（simpa を使わずに rw）
          have hlt' : (R.erase t0).card < n := by
            have htmp := hlt
            -- htmp : (R.erase t0).card < R.card
            -- hcard : R.card = n
            -- 右辺を書き換える
            rw [hcard] at htmp
            exact htmp
          -- 帰納法の適用（m := (R.erase t0).card）
          have hIH :
              NDS2 V (family V (R.erase t0)) ≤ 0 := by
            apply IH (R.erase t0).card hlt'
            exact rfl
            (expose_names; exact @supportedOn_erase α inst V R t0 hV)
          exact le_trans step_nondec hIH

      | inr hShrink =>
          rcases hShrink with ⟨R1, hs⟩
          -- 一歩の非減
          have step_nondec := hs.nds_nondec
          -- カード減少 hs.smaller : R1.card < R.card
          have hlt' : R1.card < n := by
            have htmp := hs.smaller
            rw [hcard] at htmp
            exact htmp
          -- 帰納法の適用（m := R1.card）
          have hIH :
              NDS2 V (family V R1) ≤ 0 := by
            apply IH R1.card hlt'
            exact rfl
            exact @SafeShrink.supported α V R R1 hs
          exact le_trans step_nondec hIH

noncomputable def pickPeelOrShrink
  (V : Finset α) :
  ∀ R, supportedOn V R → R ≠ ∅ → PeelOrShrink V R
| R, hV, hne => by
  classical
  -- 1) Peel 探し：Barrier が立つ t0 を探す
  by_cases h : ∃ t0 ∈ R, ThreadA.BarrierHyp V R t0
  · rcases h with ⟨t0, ht0, hB⟩
    -- PeelWitness を作って左分岐
    have pw : PeelWitness V R t0 :=
      ThreadA.PeelWitness_from_Barrier (V := V) (R := R) (t0 := t0) ht0 hB
    exact Or.inl ⟨t0, pw⟩
  · -- 2) Shrink：SCC 縮約（C 側で構成する Q と noninj を使う）
    -- ここはあなたの SCC 構成に合わせて埋める
    let Q := (buildSCCQuot (V := V) (R := R) (hneR := hne)) hV

    have hnoninj :
      ∃ t₁ ∈ R, ∃ t₂ ∈ R, t₁ ≠ t₂ ∧
        (Q.σ (Q.π t₁.1), Q.σ (Q.π t₁.2.1), Q.σ (Q.π t₁.2.2))
          = (Q.σ (Q.π t₂.1), Q.σ (Q.π t₂.2.1), Q.σ (Q.π t₂.2.2)) := by
      -- TODO: Q の性質から導出
      sorry
    have ss :
      SafeShrink V R (contractRules (π := Q.π) (σ := Q.σ) R) :=
      ThreadC.SCC_is_SafeShrink (V := V) (R := R) (hV := hV) (Q := Q) (noninj := hnoninj)

    exact Or.inr ⟨_, ss⟩

/-- axiom を実装に差し替え -/
theorem Exist_ConjA_impl
  (V : Finset α) :
  ∀ R, supportedOn V R → R ≠ ∅ → PeelOrShrink V R :=
  pickPeelOrShrink (V := V)

axiom Exist_ConjA
  (V : Finset α) :
  ∀ R, supportedOn V R → R ≠ ∅ → PeelOrShrink V R

/-- TwoStem を export（Exist_ConjA を差し込む） -/
theorem TwoStem (V : Finset α) :
  ∀ R, supportedOn V R → NDS2 V (family V R) ≤ 0 :=
  TwoStem_from_peel_or_shrink (V := V) (Exist := Exist_ConjA V)
