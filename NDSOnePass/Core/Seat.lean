-- NDSOnePass/Core/Seat.lean
import NDSOnePass.Core.System
import NDSOnePass.Core.Pairs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card

set_option autoImplicit false
open scoped BigOperators

namespace NDSOnePass
namespace System
variable {α} [DecidableEq α] [Fintype α]
variable (S : System α)
--classical

/-! # 座席（Seat）と初期座席（initialSeat）
`SeatFinset = { (K,x) | K は閉集合, x ∈ U \ K }`
`initialSeat K x : Prop` は `cl₁ (insert x K) = insert x K`
-/

/-- `(K,x)` 形式の座席の全体。 -/
def SeatFinset : Finset (Finset α × α) :=
  S.ClosedFamilyFinset.biUnion (fun K => ((S.U \ K).image (fun x => (K, x))))

/-- `q ∈ SeatFinset` の同値（外から使う基本API）。 -/
lemma mem_SeatFinset_iff {q : Finset α × α} :
  q ∈ S.SeatFinset ↔ (q.1 ∈ S.ClosedFamilyFinset ∧ q.2 ∈ (S.U \ q.1)) := by
  unfold SeatFinset
  constructor
  · intro h
    -- `bind` の要素は存在する K と x により q=(K,x) の像に属する
    -- 機械的変形：Finset.bind / Finset.mem_bind / Finset.mem_image / Finset.mem_sdiff
    -- （細部はあとで充填：短手）
    simp_all only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff]
    obtain ⟨fst, snd⟩ := q
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    obtain ⟨left_1, right_1⟩ := left_1
    simp_all only [Prod.mk.injEq, not_false_eq_true, and_self, and_true]
  · intro h
    -- K ∈ CF, x ∈ U\K から (K,x) が像に載ることを示す
    -- `Finset.mem_bind` と `Finset.mem_image` を使う機械的証明（短手）
    simp_all only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_image]
    obtain ⟨fst, snd⟩ := q
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    simp_all only [Prod.mk.injEq, exists_eq_right_right, true_and, not_false_eq_true, and_self]

/-- 「初期座席」：`K ∪ {x}` が one-pass で閉じている。 -/
def initialSeat (K : Finset α) (x : α) : Prop :=
  S.cl₁ (insert x K) = insert x K

/-- 定義展開（使い勝手のため）。 -/
lemma initialSeat_def (K : Finset α) (x : α) :
  S.initialSeat K x ↔ S.cl₁ (insert x K) = insert x K := by
  unfold initialSeat
  constructor <;> intro h <;> exact h

/-- 初期座席のとき `cl₁ (insert x K)` はそのまま `insert x K`。 -/
lemma initialSeat_closure_eq {K : Finset α} {x : α}
  (h : S.initialSeat K x) :
  S.cl₁ (insert x K) = insert x K := by
  -- 定義の直展開
  unfold initialSeat at h
  exact h

/-- （補助）座席のうち、`K` を固定して x だけ動かす列挙。 -/
def SeatOver (K : Finset α) : Finset (Finset α × α) :=
  if K ∈ S.ClosedFamilyFinset then (S.U \ K).image (fun x => (K, x)) else ∅

/-- `SeatOver K` のメンバー条件。 -/
lemma mem_SeatOver_iff {K : Finset α} {q : Finset α × α} :
  q ∈ S.SeatOver K ↔ (K ∈ S.ClosedFamilyFinset ∧ q = (K, q.2) ∧ q.2 ∈ (S.U \ K)) := by
  unfold SeatOver
  by_cases hK : K ∈ S.ClosedFamilyFinset
  · simp [hK]   -- `image` の会員条件に展開（機械的）
    obtain ⟨fst, snd⟩ := q
    simp_all only [Prod.mk.injEq, exists_eq_right_right, and_true]
    apply Iff.intro
    · intro a
      simp_all only [true_and]
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      subst right
      simp_all only [not_false_eq_true]
    · intro a
      simp_all only [not_false_eq_true, and_self]
  · simp [hK]

/-- `SeatFinset` は `SeatOver K` たちの合併になっている。 -/
lemma SeatFinset_as_bind :
  S.SeatFinset = S.ClosedFamilyFinset.biUnion (fun K => S.SeatOver K) := by
  -- 定義の揃え直し（`if hK then image else ∅` に寄せる）
  -- 機械的な整形（短手）
  dsimp [SeatFinset, SeatOver]
  apply Finset.ext
  intro q
  constructor
  · intro h
    dsimp only [Finset.mem_biUnion]
    dsimp [System.ClosedFamilyFinset]
    dsimp [System.ClosedFamilyFinset] at h
    simp_all
    obtain ⟨K, hK⟩ := h
    obtain ⟨left, right⟩ := hK
    obtain ⟨left_1, right_1⟩ := left
    obtain ⟨fst, snd⟩ := q
    obtain ⟨w, h⟩ := right
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_2⟩ := left
    simp_all only [Prod.mk.injEq]
    obtain ⟨left_2, right⟩ := right
    subst right left_2
    apply Exists.intro
    · split
      rename_i h
      simp_all only [and_self, Finset.mem_image, Finset.mem_sdiff, Prod.mk.injEq, exists_eq_right_right, true_and]
      apply And.intro
      on_goal 3 => rename_i h
      on_goal 2 => { exact right_1
      }
      · simp_all only [and_self, not_false_eq_true]
      simp_all only [and_self, not_true_eq_false]
  · intro h
    dsimp only [Finset.mem_biUnion]
    simp_all only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff]
    obtain ⟨fst, snd⟩ := q
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    simp_all only [↓reduceIte, Finset.mem_image, Finset.mem_sdiff, Prod.mk.injEq, exists_eq_right_right, true_and]
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_1, right_1⟩ := left_1
    subst right
    simp_all only [not_false_eq_true]

/-- 便宜上：座席の個数を `K` ごとに数え上げる形に書き換え。 -/
lemma card_SeatFinset :
  S.SeatFinset.card
    = ∑ K ∈ S.ClosedFamilyFinset, ((S.U \ K).card) := by
  -- `bind` のカード計算＋ `image` のカード保存（射影が単射）を使う機械的証明。
  -- ここでは型付けだけ置いておく（短手）
  dsimp [System.SeatFinset, System.SeatOver]
  rw [Finset.card_biUnion]
  apply Finset.sum_congr rfl
  · intro K hK
    dsimp [System.SeatOver]
    dsimp [System.ClosedFamilyFinset] at hK
    simp at hK
    obtain ⟨left, right⟩ := hK
    apply Finset.card_image_of_injOn
    simp_all only [Finset.coe_sdiff, Prod.mk.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq]
  · dsimp [System.ClosedFamilyFinset]
    intro K hK1 hK2
    simp at hK1
    obtain ⟨left, right⟩ := hK1
    obtain ⟨left_1, right_1⟩ := hK2
    simp_all
    intro _hHsubset _hHfix hne

    -- Function.onFun Disjoint f K H ＝ Disjoint (f K) (f H)
    change Disjoint
      ((S.U \ K).image (fun x => (K, x)))
      ((S.U \ ({ val := left_1, nodup := right_1 } : Finset α)).image
        (fun x => (({ val := left_1, nodup := right_1 } : Finset α), x)))
    -- 2つの像が素に交わることを直接示す
    refine Finset.disjoint_left.mpr ?_
    intro p hpK hpH
    -- p が両方の像にいるなら、それぞれの元で表せる
    rcases Finset.mem_image.mp hpK with ⟨xK, hxK, rfl⟩
    rcases Finset.mem_image.mp hpH with ⟨xH, hxH, hEq⟩
    -- (H, xH) = (K, xK) の第1成分比較から H = K を得る
    have hKH : K = ({ val := left_1, nodup := right_1 } : Finset α) := by
      have : ({ val := left_1, nodup := right_1 } : Finset α) = K := by
        simpa using congrArg Prod.fst hEq
      simpa using this.symm
    exact hne hKH

end System
end NDSOnePass
