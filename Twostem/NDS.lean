import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.Closure.Sync
import LeanCopilot

namespace Twostem

open scoped BigOperators
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α][Fintype (Rule α)] [DecidableEq (Rule α)]

/-- 全体 α 上の閉集合族（powerset を `IsClosed` でフィルタ） -/
def Family (R : Finset (Rule α)) [DecidablePred (fun I => IsClosed R I)] : Finset (Finset α) :=
  (univ : Finset α).powerset.filter (fun I => (IsClosed R I))

omit [DecidableEq α] [LinearOrder α] in
/-- `I ∈ Family R` の同値条件（`I ⊆ univ` は自明なので `IsClosed` が実質） -/
lemma mem_Family {R : Finset (Rule α)} [DecidablePred (IsClosed R)] {I : Finset α} :
  I ∈ Family (α:=α) R ↔ IsClosed R I := by
  classical
  unfold Family
  have : I ⊆ (univ : Finset α) := fun _ _ => by simp
  constructor
  · intro h; simpa [mem_filter, mem_powerset, this] using h
  · intro h;
    simp_all only [subset_univ, powerset_univ, mem_filter, mem_univ, and_self]

/-- ポテンシャル `NDS`（全体 α を台として定義） -/
def NDS (R : Finset (Rule α)) [DecidablePred (fun I => IsClosed R I)] : ℤ :=
  ∑ I ∈ Family R, (2 * (I.card : ℤ) - (Fintype.card α : ℤ))

omit [LinearOrder α] in
/-- 任意の `I` に対し `syncCl R I` は閉集合族 `Family R` に属する -/
lemma syncCl_mem_Family {R : Finset (Rule α)} {I : Finset α} [DecidablePred (fun I => IsClosed R I)] :
  syncCl (α:=α) R I ∈ Family R := by
  classical
  have hclosed : IsClosed R (syncCl R I) := syncCl_closed (α:=α) (R:=R) (I:=I)
  simpa [mem_Family] using hclosed



variable (AF :
  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
variable (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
variable (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Free    : RuleOrder α → Finset (Rule α) → Finset α)
variable (TwoStem : Finset (Rule α) → Prop)
variable (ρ : RuleOrder α)
variable (R : Finset (Rule α))


noncomputable instance decidablePred_isClosed (R : Finset (Rule α)) : DecidablePred (fun I : Finset α => IsClosed R I) :=
  fun I => Classical.dec (IsClosed R I)

/- Bridge I: Barrier 右辺の等式分解 -/
/-
variable (bridgeI_exact:
  (∑ B ∈ Rep ρ R, Excess ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B)
  =
  (∑ I ∈ Family R, (2 * (Finset.card I : ℤ) - (Fintype.card α : ℤ)))
  + (∑ t ∈ R, ((AF ρ R t).card : ℤ)))
-/

/-! ## Glue：下界から NDS ≤ 0 を即導出 -/
/-- Bridge II の総和下界を仮定して、NDS ≤ 0 を結論するメイン補題 -/
lemma NDS_le_zero_of_addedFamily_lower_bound
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (bridgeI_exact:
  (∑ B ∈ Rep ρ R, Excess ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B)
  =
  (∑ I ∈ Family R, (2 * (Finset.card I : ℤ) - (Fintype.card α : ℤ)))
  + (∑ t ∈ R, ((AF ρ R t).card : ℤ)))
  (hLB :
     (∑ t ∈ R, ((AF ρ R t).card : ℤ))
       ≥ ∑ B ∈ Rep ρ R, Excess ρ R B
         - (Finset.card (Free ρ R) : ℤ) * ∑ B ∈ Rep ρ R, Missing ρ R B)
         [DecidablePred (IsClosed R)]:
  NDS R ≤ 0 := by
  -- 記号の短縮（Barrier 右辺 / Δ 総和）
  set RHS : ℤ :=
    (∑ B ∈ Rep ρ R, Excess ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B)
  set LHS : ℤ :=
    (∑ t ∈ R, ((AF   ρ R t).card : ℤ))
  -- NDS = RHS - LHS
  have hNDS_def : NDS R = RHS - LHS := by
    dsimp [RHS, LHS]
    unfold NDS
    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, ge_iff_le, add_le_iff_nonpos_left, tsub_le_iff_right,
      zero_add, add_sub_cancel_right, RHS, LHS]
    congr

  -- hLB : LHS ≥ RHS から RHS - LHS ≤ 0
  have hRHSleLHS : RHS ≤ LHS := by
    simpa [RHS, LHS, ge_iff_le] using hLB
  have hsign : RHS - LHS ≤ 0 := sub_nonpos.mpr hRHSleLHS
  -- したがって NDS ≤ 0
  simp [hNDS_def]
  exact hLB


lemma NDS_le_zero_main
  (ρ : RuleOrder α) (R : Finset (Rule α))
  --(hUC : UniqueChild α R) (hTwoStem : TwoStem R)
  (hLB :
     (∑ t ∈ R, ((AF ρ R t).card : ℤ))
       ≥ ∑ B ∈ Rep ρ R, Excess ρ R B
         - (Finset.card (Free ρ R) : ℤ) * ∑ B ∈ Rep ρ R, Missing ρ R B)
  (bridgeI_exact:
  (∑ B ∈ Rep ρ R, Excess ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B)
  =
  (∑ I ∈ Family R, (2 * (Finset.card I : ℤ) - (Fintype.card α : ℤ)))
  + (∑ t ∈ R, ((AF ρ R t).card : ℤ)))
          [DecidablePred (IsClosed R)] :
  NDS R ≤ 0 := by
  -- 現段階では hUC / hTwoStem は使用しない（Bridge I/II 由来の hLB だけで閉じる）
  apply NDS_le_zero_of_addedFamily_lower_bound
  exact bridgeI_exact
  exact hLB


/- `syncCl` は最小閉包：任意の閉集合 `J` で `I ⊆ J` なら `syncCl R I ⊆ J` -/
--lemma syncCl_le_of_closed {R : Finset (Rule α)} {I J : Finset α}
--  (hIJ : I ⊆ J) (hJ : IsClosed R J) :
--  syncCl R I ⊆ J := by
--    exact syncCl_min R hIJ hJ

/-
lemma NDS_le_zero_main_ARoute
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hUC  : UniqueChild α R)
  (hNTF : ∀ t : Rule α, NoTwoFreshHeads (R.erase t))
  (hNS  : ∀ t : Rule α, NoSwap (R.erase t))
  (hA   : ∀ t : Rule α, OnlyTLastDiff ρ R t) :
  NDS R ≤ 0 := by
  -- 「任意の B,S₁,S₂,t で一意」を供給すれば完了
  refine NDS_le_zero_of_unique_S (ρ:=ρ) (R:=R) ?uniq
  intro B S₁ S₂ t hD1 hD2 hW1 hW2 hEq
  -- Aルートの3条件をその t に適用
  have hNTF_t : NoTwoFreshHeads (R.erase t) := hNTF t
  have hNS_t  : NoSwap (R.erase t)          := hNS t
  have hA_t   : OnlyTLastDiff ρ R t         := hA  t
  -- 既存の主力補題で S₁=S₂
  exact
    multiplicity_le_one_addedFamily_noA
      (ρ:=ρ) (R:=R) (t:=t)
      hUC hNTF_t hNS_t hA_t
      hD1 hD2 hW1 hW2 hEq
-/

end Twostem
