import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF
import Twostem.Basic
import Twostem.General
import LeanCopilot
open scoped Rat
--import Mathlib.Tactic.NormCast

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]


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
