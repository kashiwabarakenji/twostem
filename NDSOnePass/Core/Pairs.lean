-- NDSOnePass/Core/Pairs.lean
import NDSOnePass.Core.System
import Mathlib.Data.Finset.Image
--import Mathlib.Data.Finset.Bind
--import Mathlib.Data.Finset.LocallyFinite

set_option autoImplicit false
open scoped BigOperators

namespace NDSOnePass
namespace System
variable {α} [DecidableEq α] [Fintype α]
--variable (S : System α)
--classical

/-! # 閉集合ペアと (興味/初期) ペア -/

/-- 記法の補助：ペア `q` の左成分（閉集合）と右成分（要素）。 -/
@[simp] def qH  (q : Finset α × α) : Finset α := q.1
@[simp] def qv  (q : Finset α × α) : α        := q.2

/-- 閉集合 `H` とその中の要素 `v` を全列挙した有限集合。 -/
def allClosedPairs (S : System α): Finset (Finset α × α) :=
  S.ClosedFamilyFinset.biUnion (fun H => (H.image (fun v => (H, v))))

/-- `q ∈ allClosedPairs` の同値条件。 -/
lemma mem_allClosedPairs_iff {q : Finset α × α} (S : System α):
  q ∈ S.allClosedPairs ↔ q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 := by
  unfold allClosedPairs
  constructor
  · intro h
    -- `bind` のメンバ同値（存在する H と v で q=(H,v)）
    -- 機械的に埋められる補題。あとで充填。
    simp_all only [Finset.mem_biUnion, Finset.mem_image]
    obtain ⟨fst, snd⟩ := q
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    simp_all only [Prod.mk.injEq, and_self]

  · intro h
    -- h.1 : H∈ClosedFamily, h.2 : v∈H から画像に入ることを示す
    simp_all only [Finset.mem_biUnion, Finset.mem_image]
    obtain ⟨fst, snd⟩ := q
    obtain ⟨left, right⟩ := h
    simp_all only [Prod.mk.injEq, exists_eq_right_right, and_self]


/-- 興味ペア：`v ∈ H` かつ `v ∈ cl₁(H.erase v)`。 -/
def O_int (S : System α): Finset (Finset α × α) :=
  S.allClosedPairs.filter (fun q => q.2 ∈ S.cl₁ (q.1.erase q.2))

/-- 初期ペア：`v ∈ H` かつ `v ∉ cl₁(H.erase v)`。 -/
def O_ini (S : System α): Finset (Finset α × α) :=
  S.allClosedPairs.filter (fun q => q.2 ∉ S.cl₁ (q.1.erase q.2))

/-- 本プロジェクトでの「興味側のペア」インデックス。後続 B 層はこれを参照する。 -/
abbrev IntPairs (S : System α): Finset (Finset α × α) := S.O_int

/-- `q ∈ O_int` の同値条件。 -/
lemma mem_Oint_iff {q : Finset α × α} (S : System α):
  q ∈ S.O_int ↔
    q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 ∧ q.2 ∈ S.cl₁ (q.1.erase q.2) := by
  unfold O_int
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hpair : q ∈ S.allClosedPairs := h'.1
    have hHv : q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 :=
      (S.mem_allClosedPairs_iff).1 hpair
    have hcl : q.2 ∈ S.cl₁ (q.1.erase q.2) := h'.2
    exact And.intro hHv.1 (And.intro hHv.2 hcl)
  · intro h
    have hpair : q ∈ S.allClosedPairs := by
      -- 逆方向：`allClosedPairs` への包含（`H∈CF` と `v∈H`）
      have : q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 :=
        And.intro h.1 h.2.1
      exact (S.mem_allClosedPairs_iff).2 this
    exact Finset.mem_filter.mpr ⟨hpair, h.2.2⟩

/-- `q ∈ O_ini` の同値条件。 -/
lemma mem_Oini_iff {q : Finset α × α} (S : System α):
  q ∈ S.O_ini ↔
    q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 ∧ q.2 ∉ S.cl₁ (q.1.erase q.2) := by
  unfold O_ini
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hHv : q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 :=
      (S.mem_allClosedPairs_iff).1 h'.1
    exact And.intro hHv.1 (And.intro hHv.2 h'.2)
  · intro h
    have hpair : q ∈ S.allClosedPairs :=
      (S.mem_allClosedPairs_iff).2 ⟨h.1, h.2.1⟩
    exact Finset.mem_filter.mpr ⟨hpair, h.2.2⟩

/-- 分割：`O_int` と `O_ini` は互いに素で，和は `allClosedPairs`。 -/
lemma Oint_disjoint_Oini (S : System α) :
  Disjoint S.O_int S.O_ini := by
  -- `filter p` と `filter (¬p)` は互いに素（Finset 標準補題に帰着）
  -- 機械的な証明。あとで充填。
  dsimp [O_int, O_ini]
  exact
    Finset.disjoint_filter_filter_neg S.allClosedPairs S.allClosedPairs fun q ↦
      q.2 ∈ S.pref S.rules.length (q.1.erase q.2)

lemma Oint_union_Oini (S : System α):
  S.O_int ∪ S.O_ini = S.allClosedPairs := by
  -- `filter p ∪ filter (¬p) = s`（Finset の分割）に帰着
  dsimp [O_int, O_ini]
  exact
    Finset.filter_union_filter_neg_eq (fun q ↦ q.2 ∈ S.pref S.rules.length (q.1.erase q.2))
      S.allClosedPairs

omit [Fintype α] in
private lemma disjoint_image_pairs_of_ne
    {H₁ H₂ : Finset α} (hne : H₁ ≠ H₂) :
    Disjoint (H₁.image (fun v : α => (H₁, v)))
             (H₂.image (fun v : α => (H₂, v))) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hp₁ hp₂
  -- p ∈ image (H₁, ·) H₁ かつ p ∈ image (H₂, ·) H₂ なら矛盾
  rcases Finset.mem_image.mp hp₁ with ⟨v₁, hv₁, rfl⟩
  rcases Finset.mem_image.mp hp₂ with ⟨v₂, hv₂, hEq⟩
  -- (H₂, v₂) = (H₁, v₁) から fst が等しいので H₂ = H₁
  have : H₁ = H₂ := by
    simpa using congrArg Prod.fst hEq.symm
  exact hne this

/--
`S` の one-pass 閉集合全体（`x ⊆ S.U ∧ foldl (step) x S.rules = x`）に対して，
各 `H` を `image (fun v ↦ (H,v)) H` に対応付けると，これらは `Pairwise` に素に交わる。
つまり，`H₁ ≠ H₂` なら対応する像は `Disjoint`。
-/
private lemma pairwise_disjoint_images_on_closed (S : System α) :
  {x : Finset α |
    x ⊆ S.U ∧ List.foldl (fun acc r => S.step r acc) x S.rules = x}.Pairwise
    (Function.onFun Disjoint fun H : Finset α => H.image (fun v : α => (H, v))) := by
  classical
  -- `Set.Pairwise` の導出規則：任意の H₁,H₂ と `H₁ ≠ H₂` に対して示せばよい
  intro H₁ hH₁ H₂ hH₂ hne
  exact disjoint_image_pairs_of_ne (α := α) hne


/-- カウント：`allClosedPairs` の大きさは `∑_{H∈ClosedFamily} |H|`。 -/
lemma card_allClosedPairs (S : System α) :
  S.allClosedPairs.card = ∑ H ∈ S.ClosedFamilyFinset, (H.card) := by
  -- `bind` と `image` のカード計算（標準補題）で機械的に証明。あとで充填。
  dsimp [allClosedPairs]
  rw [Finset.card_biUnion]
  dsimp [ClosedFamilyFinset]
  congr
  ext x : 1
  simp [Finset.card_image_of_injOn]
  dsimp [Set.PairwiseDisjoint]
  dsimp [ClosedFamilyFinset]
  simp
  dsimp [System.pref]
  simp
  exact pairwise_disjoint_images_on_closed S

lemma card_Oint_add_Oini (S : System α) :
  S.O_int.card + S.O_ini.card = ∑ H ∈ S.ClosedFamilyFinset, H.card := by
  classical
  -- 左辺は filter 分割の個数恒等で allClosedPairs.card に一致
  have hsplit :
      S.O_int.card + S.O_ini.card = S.allClosedPairs.card := by
    dsimp [O_int, O_ini]
    simpa using
      Finset.filter_card_add_filter_neg_card_eq_card
        (s := S.allClosedPairs)
        (p := fun q : Finset α × α => q.2 ∈ S.cl₁ (q.1.erase q.2))
  -- 右辺は card_allClosedPairs で展開
  simpa using hsplit.trans (S.card_allClosedPairs)

/-- `IntPairs` のメンバシップ（= 興味ペア）を書き換え形で提供。 -/
lemma mem_IntPairs_iff {q : Finset α × α} (S : System α):
  q ∈ S.IntPairs ↔
    q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ q.1 ∧ q.2 ∈ S.cl₁ (q.1.erase q.2) := by
  unfold IntPairs
  exact S.mem_Oint_iff

end System
end NDSOnePass
