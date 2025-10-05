
import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.SymmDiff
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.bridge
import Twostem.NDS
import Twostem.Fiber --FreeOfなどで必要。
--import Twostem.Synchronous
--import Twostem.Derivation --mem_closure_iff_derivなど。

namespace Twostem

open scoped BigOperators
open scoped symmDiff
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)]


----

--使ってないもので使っているだけ。
omit [DecidableEq (Rule α)] in
/-- **スリム版**：閉包が等しければ，直前段は片側単元差 `{f}`。
    さらにその `{f}` は (UC なしでも) 原因規則 `r ∈ R'` を持つ。 -/
private lemma lastDiff_unique_cause_of_syncEq_slim
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α}
  (hSync : syncCl R' U = syncCl R' V) :
  U = V ∨ ∃ (k : ℕ) (f : α) (r : Rule α),
    k + 1 ≤ Fintype.card α ∧
    parIter R' U (k+1) = parIter R' V (k+1) ∧
    ( ((parIter R' U k \ parIter R' V k) = ∅ ∧ parIter R' V k \ parIter R' U k = {f}
        ∧ r ∈ R' ∧ r.prem ⊆ parIter R' U k ∧ r.head = f)  -- 右差分のみ：左側 fires 由来
      ∨ ((parIter R' V k \ parIter R' U k) = ∅ ∧ parIter R' U k \ parIter R' V k = {f}
        ∧ r ∈ R' ∧ r.prem ⊆ parIter R' V k ∧ r.head = f) ) := by
  classical
  -- 強化版：直前段の単元差＋次段一致を取得
  have hED := exists_singleton_lastDiff_of_syncEq_strong (R':=R') hNTF hNS (U:=U) (V:=V) hSync
  cases hED with
  | inl hUV =>
      exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩
      -- 記号
      set X := parIter R' U k
      set Y := parIter R' V k
      -- k+1 段一致 ⇒ step 等式
      have hstep : stepPar R' X = stepPar R' Y := by
        -- parIter … (k+1) = stepPar R' X, stepPar R' Y
        have hx : parIter R' U (k+1) = stepPar R' X := rfl
        have hy : parIter R' V (k+1) = stepPar R' Y := rfl
        -- 書換して終了
        have t := hEqNext
        rw [hx, hy] at t
        exact t
      -- 側の決定
      have hΔ : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        -- 定義置換
        simpa [X, Y]
          using (hSingle :
            (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k) = {f})
      have hcases := union_singleton_cases (X:=(X \ Y)) (Y:=(Y \ X)) (f:=f) hΔ
      -- NoSwap による “両方 {f}” の排除
      have hnoswap_side : (X \ Y = ∅) ∨ (Y \ X = ∅) := hNS X Y hstep
      cases hcases with
      | inl hXY =>
          -- (X\Y)=∅, (Y\X)={f} ：右差分のみ
          rcases hXY with ⟨hXemp, hYone⟩
          -- f ∈ Y\X を作る
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          -- 原因規則（存在）
          rcases cause_exists_on_left_of_step_eq (R:=R') hstep hfYX with ⟨r, hrR, hrPr, hrHd⟩
          -- まとめて返す
          exact Or.inr ⟨k, f, r, hkBound, hEqNext, Or.inl ⟨hXemp, hYone, hrR, hrPr, hrHd⟩⟩
      | inr hRest =>
          cases hRest with
          | inl hYX =>
              -- (Y\X)=∅, (X\Y)={f} ：左差分のみ
              rcases hYX with ⟨hYemp, hXone⟩
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := mem_singleton_self f
                have t := this;
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]

              rcases cause_exists_on_right_of_step_eq (R:=R') hstep hfXY with ⟨r, hrR, hrPr, hrHd⟩
              right
              refine ⟨k, f, r, hkBound, hEqNext, Or.inr ⟨?_, ?_, hrR, hrPr, hrHd⟩⟩
              · exact hXone
              · exact hYemp

          | inr hBoth =>
              -- 両方 {f} は NoSwap に反するので矛盾で潰す
              cases hnoswap_side with
              | inl hXYempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (X \ Y) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hBoth.left.symm] at t; exact t
                    have t := hf; rw [hXYempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))
              | inr hYXempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (Y \ X) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hBoth.right.symm] at t; exact t
                    have t := hf; rw [hYXempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))

--使ってない
omit [DecidableEq (Rule α)] in
lemma lastDiff_unique_cause_of_syncEq_unique
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  (hUC' : UniqueChild α R')   -- ★ R' 側（= R.erase t 側）で UC
  {U V : Finset α}
  (hSync : syncCl R' U = syncCl R' V) :
  U = V ∨ ∃ (k : ℕ) (f : α),
    k + 1 ≤ Fintype.card α ∧ parIter R' U (k+1) = parIter R' V (k+1) ∧
    ( ((parIter R' U k \ parIter R' V k) = ∅ ∧ ∃! r, r ∈ R' ∧ r.prem ⊆ parIter R' U k ∧ r.head = f)
    ∨ ((parIter R' V k \ parIter R' U k) = ∅ ∧ ∃! r, r ∈ R' ∧ r.prem ⊆ parIter R' V k ∧ r.head = f) ) := by
  classical
  -- まず存在版を取得
  have hslim :=
  lastDiff_unique_cause_of_syncEq_slim (R':=R') hNTF hNS (U:=U) (V:=V) hSync
 -- 以降は分岐
  cases hslim with
  | inl hUV => exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, r, hkBound, hEqNext, hside⟩
      -- 記号
      set X := parIter R' U k
      set Y := parIter R' V k
      have hstep : stepPar R' X = stepPar R' Y := by
        have hx : parIter R' U (k+1) = stepPar R' X := rfl
        have hy : parIter R' V (k+1) = stepPar R' Y := rfl
        have t := hEqNext; rw [hx, hy] at t; exact t
      -- 側ごとに一意化を付与
      cases hside with
      | inl hR =>
          rcases hR with ⟨hXemp, hYone, hrR, hrPr, hrHd⟩
          -- 右差分：Y\X={f} → f∈Y\X
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          -- 一意化
          -- 既存の r は witness；その一意性集合を作る
          have hex : ∃! s, s ∈ R' ∧ s.prem ⊆ X ∧ s.head = f := by
            -- 存在は cause_exists_on_left_of_step_eq
            rcases cause_exists_on_left_of_step_eq (R:=R') hstep hfYX with ⟨s, hsR, hsPr, hsHd⟩
            refine ⟨s, ?ex, ?uniq⟩
            · exact ⟨hsR, hsPr, hsHd⟩
            · intro s' hs'

              apply hUC'
              · exact hs'.1
              · exact hsR
              ·
                have : s.head = f := hsHd
                have : s'.head = f := hs'.2.2
                subst hsHd
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, and_true, X, Y]
          exact Or.inr ⟨k, f, hkBound, hEqNext, Or.inl ⟨hXemp, hex⟩⟩
      | inr hL =>
          rcases hL with ⟨hYemp, hXone, hrR, hrPr, hrHd⟩
          have hfXY : f ∈ X \ Y := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hXone.symm] at t; exact t
          have hex : ∃! s, s ∈ R' ∧ s.prem ⊆ Y ∧ s.head = f := by
            rcases cause_exists_on_right_of_step_eq (R:=R') hstep hfXY with ⟨s, hsR, hsPr, hsHd⟩
            refine ⟨s, ?ex0, ?uniq0⟩
            · exact ⟨hsR, hsPr, hsHd⟩
            · intro s' hs'
              subst hrHd
              simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]
              obtain ⟨left, right⟩ := hs'
              obtain ⟨left_1, right⟩ := right
              apply hUC'
              · simp_all only
              · simp_all only
              · simp_all only
          exact Or.inr ⟨k, f, hkBound, hEqNext, Or.inr ⟨hYemp, hex⟩⟩

lemma eq_or_unique_cause_for_erased
  {R : Finset (Rule α)} {t : Rule α}
  (hNTF' : NoTwoFreshHeads (R.erase t)) (hNS' : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hEqCl : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  (B ∪ S₁ = B ∪ S₂) ∨
  ∃ (k : ℕ) (f : α) (r : Rule α),
    k + 1 ≤ Fintype.card α ∧
    parIter (R.erase t) (B ∪ S₁) (k+1) = parIter (R.erase t) (B ∪ S₂) (k+1) ∧
    ( ((parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k) = ∅ ∧
        parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = {f}
        ∧ r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₁) k ∧ r.head = f)
    ∨ ((parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k) = ∅ ∧
        parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k = {f}
        ∧ r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k ∧ r.head = f) ) := by
  classical
  -- 強化版（あなたが通したもの）を R' := R.erase t に適用
  have hED :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R':=R.erase t) hNTF' hNS' (U:=B ∪ S₁) (V:=B ∪ S₂) hEqCl
  cases hED with
  | inl hUV =>
      exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩
      set X := parIter (R.erase t) (B ∪ S₁) k
      set Y := parIter (R.erase t) (B ∪ S₂) k
      have hstep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
        have hx : parIter (R.erase t) (B ∪ S₁) (k+1) = stepPar (R.erase t) X := rfl
        have hy : parIter (R.erase t) (B ∪ S₂) (k+1) = stepPar (R.erase t) Y := rfl
        have t := hEqNext; rw [hx, hy] at t; exact t
      have hΔ : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        simpa [X, Y] using hSingle
      have hcases := union_singleton_cases (X:=(X \ Y)) (Y:=(Y \ X)) (f:=f) hΔ
      have hnoswap_side : (X \ Y = ∅) ∨ (Y \ X = ∅) := hNS' X Y hstep
      cases hcases with
      | inl hXY =>
          rcases hXY with ⟨hXemp, hYone⟩
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          rcases cause_exists_on_left_of_step_eq (R:=R.erase t) hstep hfYX with ⟨r, hrR, hrPr, hrHd⟩
          exact Or.inr ⟨k, f, r, hkBound, hEqNext,
            Or.inl ⟨hXemp, hYone, hrR, hrPr, hrHd⟩⟩
      | inr hRest =>
          cases hRest with
          | inl hYX =>
              rcases hYX with ⟨hYemp, hXone⟩
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := mem_singleton_self f
                have t := this;
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]
              rcases cause_exists_on_right_of_step_eq (R:=R.erase t) hstep hfXY with ⟨r, hrR, hrPr, hrHd⟩
              right
              constructor
              · simp
                refine And.intro hkBound ?_
                refine And.intro hEqNext ?_
                -- 分岐は左差分 = {f} の側（Or.inr）を選ぶ
                subst hrHd
                simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, mem_singleton, singleton_inj, true_and, or_true,
                  singleton_union, X, Y]
                obtain ⟨left, right⟩ := hrR
                apply Exists.intro
                · apply Exists.intro
                  · tauto

          | inr hboth =>
              -- 両側 {f} は NoSwap と矛盾
              cases hnoswap_side with
              | inl hXYempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (X \ Y) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hboth.left.symm] at t; exact t
                    have t := hf; rw [hXYempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))
              | inr hYXempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (Y \ X) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hboth.right.symm] at t; exact t
                    have t := hf; rw [hYXempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
@[simp] lemma onlyTLastDiff_core_case_split
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t)) (hNS : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t)-- (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂))
  -- 枝ごとの等式化（既存のあなたの補題を渡す）
  (head_eq_right :
    ∀ {k f}
      (hEqNext :
        parIter (R.erase t) (B ∪ S₁) (k+1)
          = parIter (R.erase t) (B ∪ S₂) (k+1))
      (hXYempty :
        parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k = ∅)
      (hExu :
        ∃! r : Rule α,
          r ∈ R.erase t
          ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₁) k
          ∧ r.head = f), f = t.head)
  (head_eq_left :
    ∀ {k f}
      (hEqNext :
        parIter (R.erase t) (B ∪ S₁) (k+1)
          = parIter (R.erase t) (B ∪ S₂) (k+1))
      (hYXempty :
        parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = ∅)
      (hExuY :
        ∃! r : Rule α,
          r ∈ R.erase t
          ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k
          ∧ r.head = f), f = t.head)
  -- NoSwap からの決定版（あなたの環境の既存補題名で差し替えてOK）
  (noSwap_step_forces_empty :
    ∀ {X Y}, stepPar (R.erase t) X = stepPar (R.erase t) Y →
      X \ Y = ∅ ∨ Y \ X = ∅)
  : S₁ = S₂ := by
  classical
  -- U=V → S₁=S₂
  have finish_eq :
      (B ∪ S₁) = (B ∪ S₂) → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- 強い版：k,f
  obtain hUV | ⟨k, f, hk, hEqNext, hSingle⟩ :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R' := R.erase t) hNTF hNS
      (U := B ∪ S₁) (V := B ∪ S₂) hEq
  · exact finish_eq hUV
  ·
    set X := parIter (R.erase t) (B ∪ S₁) k
    set Y := parIter (R.erase t) (B ∪ S₂) k
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₁) k)
          = stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₂) k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差 = {f} の3分岐
    have hcases :=
      union_singleton_cases
        (X := X \ Y) (Y := Y \ X) (f := f)
        (h := hSingle)

    -- UC (erase) を一度用意（原因一意補題で使う場合があるなら）
    have hUC_erase : UC (R.erase t) := by
      intro a
      -- ((R.erase t).filter …) ⊆ (R.filter …)
      have hsubset :
          ((R.erase t).filter (fun r : Rule α => r.head = a))
            ⊆ (R.filter (fun r : Rule α => r.head = a)) := by
        intro r hr
        -- r ∈ (erase t).filter ↔ r ∈ erase t ∧ r.head = a
        -- r ∈ erase t → r ∈ R
        rcases Finset.mem_filter.mp hr with ⟨hr_erase, hhead⟩
        rcases Finset.mem_erase.mp hr_erase with ⟨_, hrR⟩
        exact Finset.mem_filter.mpr ⟨hrR, hhead⟩
      -- card_monotone + UC R
      apply le_trans
      exact Nat.le_refl #({t ∈ R.erase t | t.head = a})
      have hcard_le :
        #({r ∈ R.erase t | r.head = a})
          ≤ #({r ∈ R | r.head = a}) := by exact card_le_card hsubset

      have hcard_R_le_one :
        #({r ∈ R | r.head = a}) ≤ 1 :=
        hUC a

      exact le_trans hcard_le hcard_R_le_one

    have hUCh' : UniqueChild α (R.erase t) :=
      (UniqueChild_iff_UC (R.erase t)).mpr hUC_erase

    cases hcases with
    | inl hR =>
      rcases hR with ⟨hXempty, hYsingle⟩
      -- f ∈ Y \ X
      have hfY : f ∈ Y ∧ f ∉ X :=
        mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f) hYsingle
      -- 原因一意（左側版：hg : f ∈ Y\X）
      have hExu :
        ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f :=
        cause_unique_on_left_of_step_eq
          (R := R.erase t) (hUC := hUCh')
          (hstep := hStep)
          (hg := by exact Finset.mem_sdiff.mpr ⟨hfY.left, hfY.right⟩)

      have hXYempty: X \ Y = ∅ := by
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      -- f = t.head（右枝用の外部補題）
      have hf_head : f = t.head :=
        head_eq_right (hEqNext := hEqNext) (hXYempty := hXYempty) (hExu := hExu)


      -- 右枝は不可能
      have contra :=
        (result_right_impossible ρ R t
          (hUC := hUC) (ht := ht)
          (hW1 := hW1)
          (B := B) (S₁ := S₁)
          (k := k) (f := f)
          (U := B ∪ S₁) (V := B ∪ S₂)
          (hU := rfl)
          (hEqNext := hEqNext)
          (X := X) (Y := Y)
          (hX := rfl) (hY := rfl)
          (hXYempty := hXYempty)
          (hExu := hExu)
          (hf_head := hf_head)
          (hkBound := hk))


      exact contra.elim

    | inr hrest =>
      cases hrest with
      | inl hL =>
        rcases hL with ⟨hXsingle, hYempty⟩
        -- f ∈ X \ Y
        have hfX : f ∈ X ∧ f ∉ Y :=
          -- X\Y = {f} から f∈X∧f∉Y を得るには、補題を左右反転で使えばよい
          by
            -- 「{f} = X\Y」は「Y\X = {f}」に置き換えづらいので、
            -- 直接この用途の補題を持っているならそれを使ってOK。
            -- 今回は「左右反転して使う」ために対称形に書き直す：
            have := mem_and_not_mem_of_sdiff_singleton_right
              (X:=Y) (Y:=X) (f:=f) hXsingle

            -- ただし上の rfl はダミーなので、素直に作る：
            exact
            ⟨ by
                -- f ∈ X
                have : f ∈ X \ Y := by
                  -- hXsingle : X\Y = {f}
                  have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  exact by
                    -- 置換
                    have := congrArg (fun (s : Finset α) => f ∈ s) hXsingle
                    (expose_names; exact mem_sdiff.mpr this_1)
                exact (Finset.mem_sdiff.mp this).left
              , by
                -- f ∉ Y
                have : f ∈ X \ Y := by
                  have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  have := congrArg (fun (s : Finset α) => f ∈ s) hXsingle
                  (expose_names; exact mem_sdiff.mpr this_1)
                exact (Finset.mem_sdiff.mp this).right ⟩

        -- 原因一意（右側版：hf : f ∈ X\Y）
        have hExuY :
          ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f :=
          cause_unique_on_right_of_step_eq
            (R := R.erase t) (hUC := hUCh')
            (hstep := hStep)
            (hf := by exact Finset.mem_sdiff.mpr ⟨hfX.left, hfX.right⟩)

        -- f = t.head（左枝用の外部補題）
        have hYXempty: Y \ X = ∅ := by
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

        have hf_head : f = t.head :=
          head_eq_left (hEqNext := hEqNext) (hYXempty := hYXempty) (hExuY := hExuY)

        -- 左枝は不可能
        have contra :=
          result_left_impossible ρ R t
            (hUC := hUC)
            (B := B) (S₁ := S₁) (hW1 := hW1)
            (k := k) (f := f)
            (U := B ∪ S₁) (V := B ∪ S₂) (hU := rfl)
            (hEqNext := hEqNext)
            (X := X) (Y := Y) (hX := rfl) (hY := rfl)
            (hYXempty := hYXempty) (hExuY := hExuY)
            (hf_head := hf_head) (hkBound := hk)
        exact contra.elim

      | inr hdup =>
        -- 両側 {f} は NoSwap + step 一致に反する
        have : X \ Y = ∅ ∨ Y \ X = ∅ := noSwap_step_forces_empty (X:=X) (Y:=Y) hStep
        -- しかし hdup は (X={f} ∧ Y={f}) 型（union_singleton_cases の第3枝）なので空でない
        -- → 矛盾
        -- 形式上は「{f} = ∅」は成り立たないので OK
        cases this with
        | inl hxe =>
          have : ({f} : Finset α) = (∅ : Finset α) := by
            -- hdup から X\Y = {f}
            have hx : X \ Y = ({f} : Finset α) := by
              simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, union_idempotent, X, Y]
            exact Eq.trans hx.symm hxe
          exact (by
            -- {f} ≠ ∅
            have : (¬ ({f} : Finset α) = ∅) := by
              exact Finset.singleton_ne_empty f
            exact (this ‹{f} = ∅›).elim)
        | inr hye =>
          have : ({f} : Finset α) = (∅ : Finset α) := by
            -- hdup から Y\X = {f}
            have hy : Y \ X = ({f} : Finset α) := by
              simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, union_idempotent, X, Y]
            exact Eq.trans hy.symm hye
          exact (by
            have : (¬ ({f} : Finset α) = ∅) := by
              exact Finset.singleton_ne_empty f
            exact (this ‹{f} = ∅›).elim)


omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma sdiff_union_singleton_cases
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (h : (X \ Y) ∪ (Y \ X) = ({f} : Finset α)) :
  (X \ Y = ∅ ∧ Y \ X = {f})
  ∨ (X \ Y = {f} ∧ Y \ X = ∅)
  ∨ (X \ Y = {f} ∧ Y \ X = {f}) := by
  classical
  -- まず両者が {f} に包含されることを示す
  have hXY_sub : X \ Y ⊆ ({f} : Finset α) := by
    intro x hx
    -- x ∈ X\Y ⊆ (X\Y) ∪ (Y\X) = {f}
    have : x ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inl hx)
    have : x ∈ ({f} : Finset α) := by simpa [h] using this
    exact this
  have hYX_sub : Y \ X ⊆ ({f} : Finset α) := by
    intro y hy
    have : y ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inr hy)
    have : y ∈ ({f} : Finset α) := by simpa [h] using this
    exact this

  -- 場合分け：どちらかが空か、両方非空か
  by_cases hXYempty : X \ Y = ∅
  · -- X\Y = ∅ なら、(X\Y) ∪ (Y\X) = {f} から Y\X = {f}
    left
    have : Y \ X = ({f} : Finset α) := by
      -- ∅ ∪ (Y\X) = {f}
      have : (X \ Y) ∪ (Y \ X) = Y \ X := by simp [hXYempty, Finset.empty_union]
      exact sdiff_singleton_right_of_symmdiff_singleton_left_empty hXYempty h
    exact ⟨hXYempty, this⟩
  · by_cases hYXempty : Y \ X = ∅
    · -- Y\X = ∅ の場合は対称
      right; left
      have : X \ Y = ({f} : Finset α) := by
        have : (X \ Y) ∪ (Y \ X) = X \ Y := by simp [hYXempty, Finset.union_empty]
        simp_all only [union_empty, subset_refl, subset_singleton_iff, true_or, singleton_ne_empty, not_false_eq_true,
           sdiff_eq_empty_iff_subset, singleton_union]
      exact ⟨this, hYXempty⟩
    · -- 両方非空の場合：どちらも {f} に等しい
      right; right
      have hne1 : (X \ Y).Nonempty := Finset.nonempty_iff_ne_empty.mpr hXYempty
      have hne2 : (Y \ X).Nonempty := Finset.nonempty_iff_ne_empty.mpr hYXempty
      -- 非空 & ⊆ {f} から X\Y = {f}
      have h1 : X \ Y = ({f} : Finset α) := by
        apply Finset.Subset.antisymm_iff.mpr
        constructor
        · exact hXY_sub
        · -- {f} ⊆ X\Y：非空元を取り、その元が f と一致することを使う
          intro z hz
          have hz_eq : z = f := Finset.mem_singleton.mp hz
          rcases hne1 with ⟨x, hx⟩
          have : x = f := by
            have : x ∈ ({f} : Finset α) := hXY_sub hx
            exact Finset.mem_singleton.mp this
          simpa [hz_eq, this] using hx
      -- 同様に Y\X = {f}
      have h2 : Y \ X = ({f} : Finset α) := by
        apply Finset.Subset.antisymm_iff.mpr
        constructor
        · exact hYX_sub
        · intro z hz
          have hz_eq : z = f := Finset.mem_singleton.mp hz
          rcases hne2 with ⟨y, hy⟩
          have : y = f := by
            have : y ∈ ({f} : Finset α) := hYX_sub hy
            exact Finset.mem_singleton.mp this
          simpa [hz_eq, this] using hy
      exact ⟨h1, h2⟩



/-
lemma OnlyTLastDiff.head_eq_right_subset
  (hA : OnlyTLastDiff ρ R t)
  {U V : Finset α} {k : ℕ} {f : α}
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (hsubset :
    parIter (R.erase t) U k ⊆ parIter (R.erase t) V k)
  (hExu :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) U k ∧
      r.head = f) :
  f = t.head :=
  sorry
-/

/-
lemma head_eq_right_from_A
  (hA : OnlyTLastDiff ρ R t)
  {U V : Finset α} {k : ℕ} {f : α}
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (hXYempty :
    parIter (R.erase t) U k \ parIter (R.erase t) V k = ∅)
  (hExu :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) U k ∧
      r.head = f) :
  f = t.head :=
by
  -- sdiff=∅ → ⊆ （`sdiff_eq_empty_iff_subset` を ←向きに使う）
  have hsubset :
    parIter (R.erase t) U k ⊆ parIter (R.erase t) V k :=
  by
    -- `Finset.sdiff_eq_empty_iff_subset` の「→」向きを明示的に使う
    exact (Finset.sdiff_eq_empty_iff_subset).1 hXYempty
  exact OnlyTLastDiff.head_eq_right_subset hA hEqNext hsubset hExu
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma OnlyTLastDiff.head_eq_of_symmDiff_singleton
  [DecidableEq α] [Fintype α] [LinearOrder α]
  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α}
  (hA : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α} {k : ℕ} {f : α}
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEqNext :
    parIter (R.erase t) (B ∪ S₁) (k+1)
      = parIter (R.erase t) (B ∪ S₂) (k+1))
  (hSingle :
    (parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k) ∪
    (parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k)
      = ({f} : Finset α)) :
  f = t.head := by
  -- `OnlyTLastDiff` はまさにこの4引数を取る形なので、そのまま適用で終わり
  exact hA (B:=B) (S₁:=S₁) (S₂:=S₂) (k:=k) (f:=f) hW1 hW2 hEqNext hSingle

--これも使われないけど分岐用
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma left_branch_Xdiff_singleton_of_symmDiff
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α))
  (hYXempty : Y \ X = ∅) :
  X \ Y = ({f} : Finset α) := by
  -- 片方が空なので対称差＝左差分。等式を書き換えるだけ。
  -- 以降は ext/包含で閉じるだけです（お手元の補題で短くしてOK）
  -- left ⊆ right
  have hsubset : X \ Y ⊆ ({f} : Finset α) := by
    intro x hx
    have : x ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inl hx)
    -- hSingle で右へ移す
    -- `mem_singleton.mp` で x=f と取り、`mem_singleton.mpr` で戻す
    have hx_single : x ∈ ({f} : Finset α) := by
      -- 置換： (X\Y) ∪ (Y\X) = {f}
      -- `rw [hSingle]` を避けるなら `congrArg (fun s => x ∈ s) hSingle` を使う
      have := congrArg (fun s => x ∈ s) hSingle
      -- now cast
      apply Eq.mp this
      (expose_names; exact this_1)
    exact hx_single
  -- right ⊆ left
  have hsuperset : ({f} : Finset α) ⊆ X \ Y := by
    intro x hx
    have hx_eq : x = f := Finset.mem_singleton.mp hx
    -- 対称差が {f} で Y\X=∅ だから f ∈ X\Y
    -- お手元の `mem_and_not_mem_of_sdiff_singleton_right` を使うと速い：
    -- 適用のために {f} = X\Y を先に主張する流れでも良いです。
    -- ここは簡潔化のため略。実装では ext で両包含を出してもOK。
    have hunion : (X \ Y) ∪ (Y \ X) = X \ Y := by
  -- rewrite the right union operand using hYXempty, then use union with empty
      have := congrArg (fun s => (X \ Y) ∪ s) hYXempty
      -- this : (X \ Y) ∪ (Y \ X) = (X \ Y) ∪ ∅
      exact Eq.trans this (Finset.union_empty _)

    -- From the two equalities, derive X \ Y = {f}.
    have hXYeq : X \ Y = ({f} : Finset α) :=
      Eq.trans hunion.symm hSingle

    -- Now rewrite membership using hXYeq.
    have : x ∈ X \ Y := by
      -- (x ∈ {f}) = (x ∈ X \ Y)
      have hmem := congrArg (fun s => x ∈ s) hXYeq.symm
      exact Eq.mp hmem hx

    exact this
  apply Finset.Subset.antisymm_iff.mpr
  exact ⟨hsubset, hsuperset⟩

--使われてない。
lemma f_mem_XdiffY_of_left_singleton
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α))
  (hYXempty : Y \ X = ∅) :
  f ∈ X \ Y := by
  -- まず f ∈ {(f)} から左辺（対称差）に移す
  have hf_in_symm : f ∈ (X \ Y) ∪ (Y \ X) := by
    -- 会員命題に等式 hSingle を作用
    have := congrArg (fun (s : Finset α) => f ∈ s) hSingle
    -- （f ∈ ((X\Y) ∪ (Y\X))) = (f ∈ {f})
    -- 右辺は自明
    have : (f ∈ (X \ Y) ∪ (Y \ X)) = True := by
      -- f ∈ {f}
      have : f ∈ ({f} : Finset α) := by
        exact Finset.mem_singleton_self f
      -- 等式を使って左辺に運ぶ
      simp_all only [union_empty, sdiff_eq_empty_iff_subset, singleton_union, mem_insert, mem_sdiff, true_or, mem_singleton]

    -- True を命題へ戻す
    exact by
      -- (f ∈ symmDiff) = True なら f ∈ symmDiff
      simp_all only [union_empty, sdiff_eq_empty_iff_subset, singleton_union, mem_insert, mem_sdiff, true_or, mem_singleton]

  -- 右側の枝には入れない（Y\X=∅）
  have hf_not_right : f ∉ (Y \ X) := by
    -- hYXempty : Y \ X = ∅
    -- したがって要素は存在しない
    have : (Y \ X) = (∅ : Finset α) := hYXempty
    -- 変形してゴールへ
    -- `simp [this]` は使わず、直接「空集合には何も入らない」を使う
    intro contra
    -- contra : f ∈ Y\X = ∅ のはず → 矛盾
    have : f ∈ (∅ : Finset α) := by
      -- 等式で置換
      rw [this] at contra
      exact contra

    cases this
  -- 和集合の帰属から左成分へ
  -- hf_in_symm : f ∈ (X\Y) ∪ (Y\X)
  -- hf_not_right : f ∉ (Y\X)
  -- なので f ∈ X\Y
  exact
    (Finset.mem_union.mp hf_in_symm).elim
      (fun h => h)
      (fun h => False.elim (hf_not_right h))

lemma head_notin_of_head_eq_and_mem_sdiff
  [DecidableEq α]
  {X Y : Finset α} {r : Rule α} {f : α}
  (hr_head : r.head = f)
  (hf_in_XdiffY : f ∈ X \ Y) :
  r.head ∉ Y := by
  -- sdiff の定義から f ∉ Y
  have hf_notinY : f ∉ Y := (Finset.mem_sdiff.mp hf_in_XdiffY).right
  -- r.head = f で置換
  -- `cases hr_head` で十分（rw/simp なし）
  cases hr_head
  exact hf_notinY

/-- Left branch localization: 成り立たない。
    左枝 (Y \ X = ∅) かつ (k+1) 段が一致し、Y 側で head=f の原因が一意に存在するとき、
    f はちょうど X\Y にいる。-/
lemma f_mem_XdiffY_from_left_branch
  [DecidableEq α] [Fintype α]
  {R : Finset (Rule α)} {t : Rule α}
  (hNS : NoSwap (R.erase t)) (hUC' : UniqueChild α (R.erase t))
  {U V : Finset α} {k : ℕ} {f : α}
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (hYXempty :
    parIter (R.erase t) V k \ parIter (R.erase t) U k = ∅)
  (hExuY :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) V k ∧
      r.head = f) :
  f ∈ parIter (R.erase t) U k \ parIter (R.erase t) V k :=
by
  -- スケッチ：
  -- 1) hEqNext を step 形へ：stepPar X = stepPar Y
  -- 2) NoSwap から、Y\X=∅ なら「対称差の新規は X 側のみ」になる
  -- 3) 左右の cause-uniqueness 補題（あなたの `cause_unique_on_left/right_of_step_eq`）
  --    と hExuY を突き合わせると、新規 head は同じ f に一本化される
  -- 4) 以上から f ∈ X\Y を得る
  -- ここはあなたの環境の既存補題名に差し替えて埋めてください
  admit


lemma OnlyTLastDiff.head_eq_left_sdiff
  [DecidableEq α] [Fintype α] [LinearOrder α]
  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α}
  (hA : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α} {k : ℕ} {f : α}
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hNTF : NoTwoFreshHeads (R.erase t)) (hNS : NoSwap (R.erase t))
  (hUC' : UniqueChild α (R.erase t))
  (hEqNext :
    parIter (R.erase t) (B ∪ S₁) (k+1)
      = parIter (R.erase t) (B ∪ S₂) (k+1))
  (hYXempty :
    parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = ∅)
  (hExuY :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k ∧
      r.head = f) :
  f = t.head := by
  -- 記号
  set X := parIter (R.erase t) (B ∪ S₁) k
  set Y := parIter (R.erase t) (B ∪ S₂) k

  -- (1) (k+1) 段の一致を step 形に
  have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
    change stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₁) k)
        = stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₂) k) at hEqNext
    exact hEqNext

  -- (2) 左枝から f ∈ X\Y を作る（★ 追加補題を使用）
  have hf_XdiffY :
      f ∈ X \ Y :=
    f_mem_XdiffY_from_left_branch
      (hNS := hNS) (hUC' := hUC') (hEqNext := hEqNext)
      (hYXempty := by
        -- hYXempty を X,Y の定義に合わせてそのまま使う
        exact hYXempty)
      (hExuY := hExuY)

  -- (3) hExuY の唯一原因 r を取り出す
  obtain ⟨r, hr_pack, huniq⟩ := hExuY
  have hr_in   : r ∈ R.erase t := hr_pack.left
  have hr_prem : r.prem ⊆ Y    := (hr_pack.right).left
  have hr_head : r.head = f     := (hr_pack.right).right

  -- (4) f ∈ X\Y と r.head=f から r.head ∉ Y（★ あなたの補題2）
  have h_head_notinY : r.head ∉ Y :=
    head_notin_of_head_eq_and_mem_sdiff (hr_head) (hf_XdiffY)

  -- (5) これで r は Y で適用可能 → fires(Y) に f
  have hr_app : r ∈ applicable (R.erase t) Y :=
    mem_applicable_of_prem_subset_and_head_notin
      (hrR := hr_in) (hprem := hr_prem) (hnot := h_head_notinY)

  have hf_in_firesY : f ∈ fires (R.erase t) Y := by
    have : r.head ∈ fires (R.erase t) Y :=
      mem_fires_of_applicable (hr := hr_app)
    -- r.head = f で置換（`cases` で対応）
    cases hr_head
    exact this

  -- (6) hStep から左枝版の包含：X\Y ⊆ fires(Y)
  have hXdiff_sub : X \ Y ⊆ fires (R.erase t) Y := by
    -- （あなたの左右版補題に差し替えてください）
    -- 例：`diff_subset_fires_left (id (Eq.symm hEqNext))`
    exact diff_subset_fires_left (id (Eq.symm hEqNext))

  -- (7) NoTwoFreshHeads → fires(Y).card ≤ 1
  have hF_card_le : (fires (R.erase t) Y).card ≤ 1 := hNTF Y

  -- (8) 以上から X\Y ⊆ {f}
  have hXdiff_sub_singleton : X \ Y ⊆ ({f} : Finset α) := by
    intro x hx
    have hxF : x ∈ fires (R.erase t) Y := hXdiff_sub hx
    have : x = f :=
      eq_of_two_mem_of_card_le_one
        (ha := hxF) (hb := hf_in_firesY) (hcard := hF_card_le)
    exact Finset.mem_singleton.mpr this

  -- (9) Y\X=∅ なので対称差は (X\Y) のみ。ここから {f} ＝ 対称差 を出す。
  --     まず左⊆右は (8) で OK。右⊆左 は（★ あなたの補題1）で f∈X\Y を使って {f}⊆X\Y。
  have hYXempty' : Y \ X = ∅ := hYXempty
  have hsub : (X \ Y) ∪ (Y \ X) ⊆ ({f} : Finset α) := by
    intro z hz
    cases Finset.mem_union.mp hz with
    | inl hzX => exact hXdiff_sub_singleton hzX
    | inr hzY =>
        -- Y\X=∅ なので到達不可
        have : z ∈ (∅ : Finset α) := by
          -- 等式で置換して矛盾に落とすだけ
          have : (Y \ X) = (∅ : Finset α) := hYXempty'
          rw [this] at hzY
          exact hzY

        cases this

  -- {f} ⊆ X\Y は、f ∈ X\Y を使えば良い
  have hsup : ({f} : Finset α) ⊆ (X \ Y) ∪ (Y \ X) := by
    intro z hz
    -- z = f
    have hz_eq : z = f := Finset.mem_singleton.mp hz
    -- ★ f ∈ X\Y は上で確保済み
    have hf_in : f ∈ X \ Y := hf_XdiffY
    -- これで union に包む
    -- 置換を `cases hz_eq` で
    cases hz_eq
    exact Finset.mem_union.mpr (Or.inl hf_in)

  have hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
    exact Finset.Subset.antisymm_iff.mpr ⟨hsub, hsup⟩

  -- (10) いよいよ OnlyTLastDiff を適用して f = t.head
  exact
    OnlyTLastDiff.head_eq_of_symmDiff_singleton
      (hA := hA) (hW1 := hW1) (hW2 := hW2)
      (hEqNext := hEqNext)
      (hSingle := by
        -- X,Y の定義を戻す必要があれば戻す（ここではそのままでも型が合います）
        exact hSingle)
