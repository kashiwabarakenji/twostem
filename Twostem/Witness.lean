-- Twostem/Witness.lean
import Mathlib.Data.Finset.Basic
import Twostem.Rules
import Twostem.Closure
--import Twostem.Bridge

namespace Twostem

open Finset

variable {α : Type _} [DecidableEq α] [Fintype α]
variable [LinearOrder α]  -- 辞書式最小などに使う

/-
/-- ルール順序：先行関係 `ρ.lt s t` -/
structure RuleOrder (α : Type _) where
  lt : Rule α → Rule α → Prop
  lt_irrefl : ∀ t, ¬ lt t t
  lt_trans  : ∀ {a b c}, lt a b → lt b c → lt a c
  lt_total  : ∀ a b, a ≠ b → lt a b ∨ lt b a

attribute [simp] RuleOrder.lt_irrefl
-/

/-
--BridgeのところでisWitnessを定めているので重複定義になっている。
/-- witness：B∪S で「t が最初の違反」 -/
structure IsWitness (ρ : RuleOrder α)
    (R : Finset (Rule α)) (B S : Finset α) (t : Rule α) : Prop :=
  (t_mem : t ∈ R)                                 -- t ∈ R
  (prem_subset : t.prem ⊆ B ∪ S)                  -- A_t ⊆ B∪S
  (head_notin : t.head ∉ B ∪ S)                   -- r_t ∉ B∪S
  (first_min :
     ∀ {s : Rule α}, s ∈ R → ρ.lt s t →
       ¬ (s.prem ⊆ B ∪ S ∧ s.head ∉ B ∪ S))       -- 先行 s は違反でない
-/

/- bridgeに同名の補題がある。
lemma head_not_in_closure_of_erase
  {ρ : RuleOrder α} {R : Finset (Rule α)} {B S : Finset α} {t : Rule α}
  (hW : IsWitness (α:=α) ρ R B S t)
  (hUC : UC (α:=α) R) :
  t.head ∉ syncCl (R.erase t) (B ∪ S) := by
  classical
  -- UC: head へ到達する唯一のルールは t 自身。t を消せば head t は出ない。
  -- 形式化：もし head 出現なら、クロージャの閉性から「head を導くルール」が必要だが、
  -- r_t のヘッドを持つルールは t のみ（UC）。その t は消しているので矛盾。
  intro hIn
  -- closure が R\{t} で閉：head が出るには rule u∈R\{t} with u.head=t.head が必要
  -- UC: u=t しかない → u∈R\{t} は偽
  have : ∀ u ∈ R.erase t, u.head = t.head → False := by
    intro u hu hhead
    rcases mem_erase.mp hu with ⟨hu_ne, huR⟩
    have := hUC t.head
    -- UniqueChild: head→ルールは高々1本。t∈R で head t のルールは t のみ。
    have : u = t := by
      sorry
      -- 「u と t がともに head を t.head に持つ」→ UC から等しい
      -- exact (uniqueChild_head_eq (R:=R) (hUC:=hUC) (h1:=hW.t_mem) (h2:=huR) (hh:=hhead)).symm
    exact hu_ne this
  -- closure から head を出すためのルールが存在しない（R\{t} には head=t.head を持つルールが無い）
  -- よって head∈closure は成り立たない。
  -- 形式的には closure の「導出存在」を使わずとも、UC の排中に依存して矛盾とする。
  -- ここでは contradiction として閉じる。
  sorry
  /-
  exact False.elim (by
    -- 通常は closure の定義・導出列による「head が出るなら相応のルールがある」を使う。
    -- 基礎ライブラリに "head_in_closure_implies_exists_rule" 相当があればそれを使う。
    -- いまは UC と erase の事実から直観的矛盾として完了。
    -- 実運用では Twostem/Closure の補題として提供しておくと綺麗：
    --   head_in_closure_implies_exists_rule ...

    exact False.intro
  )
  -/
  -/

omit [Fintype α] [LinearOrder α] in
/-- S は Free 側、B は Rep 側とし、差分は常に Free 側に現れる（B は固定） -/
lemma symmDiff_in_Free
  {B S₁ S₂ : Finset α} {Free : Finset α}
  (hS1 : S₁ ⊆ Free) (hS2 : S₂ ⊆ Free) :
  ((B ∪ S₁) \ (B ∪ S₂)) ⊆ Free ∧ ((B ∪ S₂) \ (B ∪ S₁)) ⊆ Free := by
  constructor <;> intro x hx
  · rcases mem_sdiff.mp hx with ⟨hxU, hxN⟩
    rcases mem_union.mp hxU with hxB | hxS1
    · -- x∈B なら LHS に入れない（B は両側に入る）ので到達しない
      exact (False.elim (by
        have : x ∈ B ∪ S₂ := mem_union.mpr (Or.inl hxB)
        exact hxN this))
    · exact hS1 hxS1
  · rcases mem_sdiff.mp hx with ⟨hxU, hxN⟩
    rcases mem_union.mp hxU with hxB | hxS2'
    · exact (False.elim (by
        have : x ∈ B ∪ S₁ := mem_union.mpr (Or.inl hxB)
        exact hxN this))
    · exact hS2 hxS2'

/- bridgeに同名の補題がある。
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hTS : TwoStemR (α:=α) R) (hUC : UC R)
  {B : Finset α} {t : Rule α} {S₁ S₂ : Finset α}
  (hW1 : IsWitness (α:=α) ρ R B S₁ t)
  (hW2 : IsWitness (α:=α) ρ R B S₂ t)
  (hEq :
    syncCl (R.erase t) (B ∪ S₁) =
    syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 差分が空なら即 S₁=S₂。空でないと仮定して矛盾を作る。
  let D : Finset α :=
    ((B ∪ S₁) \ (B ∪ S₂)) ∪ ((B ∪ S₂) \ (B ∪ S₁))
  by_cases hD : D = ∅
  · -- D=∅ → B∪S₁ = B∪S₂ → S₁=S₂
    -- 短く：ext で示す
    apply Finset.ext; intro x; constructor <;> intro hx
    · have : x ∈ B ∪ S₂ := by
        have hxU : x ∈ B ∪ S₁ := by exact mem_union.mpr (Or.inr hx)
        -- D=∅ より (B∪S₁)\(B∪S₂) も空 → x∈(B∪S₂)
        by_contra hnx
        have : x ∈ ((B ∪ S₁) \ (B ∪ S₂)) := mem_sdiff.mpr ⟨hxU, hnx⟩
        exact by
          have : x ∈ D := mem_union.mpr (Or.inl this)
          simpa [hD] using this
      -- 上の x∈B∨x∈S₂ を x∈S₂ に落とす（B∩S₁=∅ である設計：S は Free 側）
      rcases mem_union.mp this with hxB | hxS2
      · exact False.elim (by sorry) --cases hxB)   -- ここは設計仮定：S ∩ B = ∅
      · exact hxS2
    · have : x ∈ B ∪ S₁ := by
        have hxU : x ∈ B ∪ S₂ := by exact mem_union.mpr (Or.inr hx)
        by_contra hnx
        have : x ∈ ((B ∪ S₂) \ (B ∪ S₁)) := mem_sdiff.mpr ⟨hxU, hnx⟩
        exact by
          have : x ∈ D := mem_union.mpr (Or.inr this)
          simpa [hD] using this
      rcases mem_union.mp this with hxB | hxS1
      · exact False.elim (by sorry) --cases hxB)
      · exact hxS1
  · -- D≠∅：局在補題で唯一の差分 f を取る
    sorry
    /-
    obtain ⟨f, hfPred, huniq⟩ :=
      firstDiff_localizes_one_coordinate (α:=α) ρ (R:=R) hTS
        (t:=t) (B:=B) (S₁:=S₁) (S₂:=S₂) hW1 hW2
    rcases hfPred with hL | hR
    · rcases hL with ⟨hfU1, hfN2⟩
      -- f は (R\{t}, B∪S₁) の closure に確実に入る（基底からの単調性）
      have hfCl1 : f ∈ closure (R.erase t) (B ∪ S₁) :=
        subset_closure (R:=R.erase t) (I:=B ∪ S₁) hfU1
      -- 閉包等式から (R\{t},B∪S₂) にも入る
      have hfCl2 : f ∈ closure (R.erase t) (B ∪ S₂) := by simpa [hEq] using hfCl1
      -- しかし f ∉ B∪S₂。導出存在補題で「u∈R\{t} かつ u.head=f」のルールが要る
      rcases (head_in_closure_iff_exists_rule
              (R:=R.erase t) (X:=(B∪S₂)) (a:=f)).1 hfCl2 with
      | .inl hinX   => exact hfN2 hinX
      | .inr ⟨u, huRE, hhead, hprem⟩ =>
          rcases mem_erase.mp huRE with ⟨hu_ne_t, huR⟩
          -- UC：R 中で head=f のルールは u と t のいずれか一意。hhead と hUC により u=t
          have : u = t := uniqueChild_head_eq (R:=R) (hUC:=hUC)
                                (h1:=by exact hW1.t_mem) (h2:=huR) (hh:=hhead)
          exact hu_ne_t this
    · rcases hR with ⟨hfN1, hfU2⟩
      have hfCl2 : f ∈ closure (R.erase t) (B ∪ S₂) :=
        subset_closure (R:=R.erase t) (I:=B ∪ S₂) hfU2
      have hfCl1 : f ∈ closure (R.erase t) (B ∪ S₁) := by simpa [hEq] using hfCl2
      rcases (head_in_closure_iff_exists_rule
              (R:=R.erase t) (X:=(B∪S₁)) (a:=f)).1 hfCl1 with
      | .inl hinX   => exact hfN1 hinX
      | .inr ⟨u, huRE, hhead, hprem⟩ =>
          rcases mem_erase.mp huRE with ⟨hu_ne_t, huR⟩
          have : u = t := uniqueChild_head_eq (R:=R) (hUC:=hUC)
                                (h1:=by exact hW2.t_mem) (h2:=huR) (hh:=hhead)
          exact hu_ne_t this
    -/
    -/


end Twostem
