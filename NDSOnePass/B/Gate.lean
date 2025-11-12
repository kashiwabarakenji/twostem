-- NDSOnePass/B/Gate.lean
import NDSOnePass.Core.System
import NDSOnePass.Core.Pairs
import NDSOnePass.Core.Seat
import Mathlib.Data.Finset.Card
--import Mathlib.Algebra.BigOperators.Rat
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Rat.Defs
--import Mathlib.Data.Rat.Basic

set_option autoImplicit false
open scoped BigOperators

namespace NDSOnePass
namespace System
variable {α} [DecidableEq α] [Fintype α]

open Classical

/-! # Gate 層：landing / Rset / LBC とトリガ補題

このファイルでは，IntPairs の各 `q = (H,v)` に対し
* `G0 q := H \ {v}`
* `landing q := cl₁ (G0 q \ Smin q)`  （最小遮断 `Smin q` を抽象化）
* `Rset q := Smin q ∩ (U \ landing q)`
を与えます。

最小遮断の**存在や極小性の性質は補題として述べ**，証明は後送り（`sorry`）にしています。
これにより循環無しで LBC の if-sum 定義まで進められます。
-/

/-! ## 基本の補助：G0・head 用のヘルパ -/

/-- `q=(H,v)` から `G0 = H \\ {v}`。 -/
@[simp] def G0 (S : System α)(q : Finset α × α) : Finset α :=
  q.1.erase q.2

/-- 規則列から「head が v の規則」を探す Option。UC を満たす系では高々 1 つ。 -/
noncomputable def headRule? (S : System α) (v : α) : Option (Rule α) :=
  S.rules.find? (fun r => decide (r.head = v))

/-- `PremOf v`：`head=v` の規則があればその前提，なければ空集合。 -/
noncomputable def PremOf (S : System α) (v : α) : Finset α :=
  match S.headRule? v with
  | some r => r.prem
  | none   => ∅

/-! ## 最小遮断（抽象化）と landing / Rset -/

/-- 最小遮断の性質を表す述語（最小限版）.
まずは「遮断集合は `G0 q` から選ぶ（＝ head そのものは入れない）」だけを採用する。
これで `Smin ⊆ G0` が取れ，`Rset` に head が入らないことが示せる。 -/
/- 最小遮断：G0 内、head を止め、真に弱めると head が出る。 -/
def IsMinCut (S : System α) (q : Finset α × α) (X : Finset α) : Prop :=
  X ⊆ S.G0 q
  ∧ q.2 ∉ S.cl₁ (S.G0 q \ X)
  ∧ ∀ ⦃Y : Finset α⦄, Y ⊂ X → q.2 ∈ S.cl₁ (S.G0 q \ Y)

/-- 候補：G0 内で head を止める X。 -/
def cutCandidates (S : System α) (q : Finset α × α) : Finset (Finset α) :=
  (S.G0 q).powerset.filter (fun X => q.2 ∉ S.cl₁ (S.G0 q \ X))


/-- `cutCandidates` が空でないこと。
    ※ `cl₁ ∅ = ∅` が言えれば、`X = G0 q` が候補に入る。 -/
lemma candidates_nonempty
  (S : System α) (q : Finset α × α)
  (hEmpty : S.cl₁ (∅ : Finset α) = ∅) :
  (S.cutCandidates q).Nonempty
  := by
    classical
    have hmemP : S.G0 q ∈ (S.G0 q).powerset :=
      Finset.mem_powerset.mpr (by exact Finset.Subset.rfl)
    have hstop : q.2 ∉ S.cl₁ (S.G0 q \ S.G0 q) := by
      -- cl₁ ∅ = ∅ を仮定で使用
      simp
      simp_all only [cl₁_def, G0, Finset.mem_powerset, subset_refl, Finset.notMem_empty, not_false_eq_true]
    exact ⟨S.G0 q, by
    simp_all only [cl₁_def, G0, Finset.mem_powerset, subset_refl, sdiff_self, Finset.bot_eq_empty,
      Finset.notMem_empty, not_false_eq_true]
    obtain ⟨fst, snd⟩ := q
    simp_all only
    unfold cutCandidates
    simp_all only [G0, cl₁_def, Finset.mem_filter, Finset.mem_powerset, subset_refl, sdiff_self, Finset.bot_eq_empty,
      Finset.notMem_empty, not_false_eq_true, and_self]
    ⟩



/-- 最小遮断の存在（`cl₁ ∅ = ∅` を仮定）。 -/
lemma exists_minCut_of_mem
  (S : System α) {q : Finset α × α} (hq : q ∈ S.IntPairs)
  (hEmpty : S.cl₁ (∅ : Finset α) = ∅) :
  ∃ X : Finset α, S.IsMinCut q X
  := by
    classical
    set C := S.cutCandidates q
    have hCne : C.Nonempty := S.candidates_nonempty q hEmpty
    -- `card` 最小の要素 X を取る
    obtain ⟨X, hXmem, hXmin⟩ :=
      Finset.exists_min_image (s := C) (f := fun X : Finset α => X.card) hCne
    -- X の性質
    have hXsub : X ⊆ S.G0 q := by
      have : X ∈ (S.G0 q).powerset := (Finset.mem_filter.mp hXmem).1
      exact (Finset.mem_powerset.mp this)
    have hXstop : q.2 ∉ S.cl₁ (S.G0 q \ X) := (Finset.mem_filter.mp hXmem).2
    -- 極小性：Y ⊂ X ⇒ head が出る（出なければ C に入り最小性に矛盾）
    have hXminCut :
        ∀ ⦃Y : Finset α⦄, Y ⊂ X → q.2 ∈ S.cl₁ (S.G0 q \ Y) := by
      intro Y hYss
      have hYsub : Y ⊆ S.G0 q := by
        intro x hx
        have : x ∈ X := by
          rw [Finset.ssubset_iff_subset_ne] at hYss
          simp_all only [cl₁_def, G0, ne_eq, C]
          obtain ⟨fst, snd⟩ := q
          obtain ⟨left, right⟩ := hYss
          simp_all only
          apply left
          simp_all only
        exact hXsub this

        --Finset.Subset.trans (Finset.ssubset_iff_subset.mp hYss).1 hXsub
      have hYmemP : Y ∈ (S.G0 q).powerset := Finset.mem_powerset.mpr hYsub
      by_contra h
      have : Y ∈ C := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨hYmemP, h⟩
      -- `card Y < card X`（真部分集合）
      have hlt : Y.card < X.card := by
        simp_all only [cl₁_def, G0, Finset.mem_powerset, C]
        obtain ⟨fst, snd⟩ := q
        simp_all only
        exact Finset.card_lt_card hYss
      exact (Nat.lt_of_lt_of_le hlt (hXmin _ this)).false
    exact ⟨X, ⟨hXsub, hXstop, hXminCut⟩⟩

/-- `Smin`：IntPairs のとき最小遮断 witness を選ぶ（`cl₁ ∅ = ∅` を使う）。 -/
noncomputable def Smin (S : System α) (q : Finset α × α) : Finset α :=
  if hq : q ∈ S.IntPairs then
    Classical.choose (S.exists_minCut_of_mem (q := q) hq (by
      -- NEP から `cl₁ ∅ = ∅`
      dsimp [cl₁_def]
      dsimp [System.pref]

      apply S.cl₁_empty_of_NEP
      intro r hr
      --exact S.cl₁_empty_of_NEP (by simpa using S.NEP)
      let sn := S.NEP r hr
      exact sn
            ) )

  else ∅

/-- `Smin` の仕様。 -/
lemma Smin_spec (S : System α) {q : Finset α × α} (hq : q ∈ S.IntPairs) :
  S.IsMinCut q (S.Smin q) := by
  classical
  --have h := Classical.choose_spec (S.exists_minCut_of_mem (q := q) hq (by
    -- NEP から `cl₁ ∅ = ∅`
  have h := Classical.choose_spec
    (S.exists_minCut_of_mem (q := q) hq (by exact S.cl₁_empty_of_NEP (by exact fun r a ↦ S.NEP r a)))
  simpa [Smin, hq] using h

/-- **着地**：遮断後に one-pass 閉包を取り直した集合。 -/
noncomputable def landing (S : System α) (q : Finset α × α) : Finset α :=
  S.cl₁ (S.G0 q \ S.Smin q)

/-- **残差**：遮断集合のうち，着地に戻ってこない要素。 -/
noncomputable def Rset (S : System α) (q : Finset α × α) : Finset α :=
  S.Smin q ∩ (S.U \ S.landing q)

/-- `Smin ⊆ G0`。 -/
lemma Smin_subset_G0 (S : System α) {q : Finset α × α} (hq : q ∈ S.IntPairs) :
  S.Smin q ⊆ S.G0 q := (S.Smin_spec (q := q) hq).1

/-- 着地は head を含まない。 -/
lemma landing_in_CF (S : System α) {q : Finset α × α}
  (hq : q ∈ S.IntPairs) :
  q.2 ∉ S.landing q := by
  classical
  rcases S.Smin_spec (q := q) hq with ⟨_, hSafe, _⟩
  dsimp [System.landing] at *
  simpa using hSafe

/-- Rset に x があれば、x を足すと head が出る。 -/
lemma firstGate_of_R_single (S : System α) {q : Finset α × α} {x : α}
  (hq : q ∈ S.IntPairs) (hxR : x ∈ S.Rset q) :
  q.2 ∈ S.cl₁ (insert x (S.landing q)) := by
  classical
  rcases S.Smin_spec (q := q) hq with ⟨hSub, hSafe, hMin⟩
  have hxSmin : x ∈ S.Smin q := (Finset.mem_inter.mp hxR).1
  have hYss : (S.Smin q \ {x}) ⊂ S.Smin q := by
    have hsubset : S.Smin q \ {x} ⊆ S.Smin q := by simp_all only [G0, cl₁_def, Finset.sdiff_subset]
    have hne : S.Smin q \ {x} ≠ S.Smin q := by
      intro hEq
      have hxIn' : x ∈ S.Smin q \ {x} := by simpa [hEq] using hxSmin
      have : x ∉ S.Smin q \ {x} := by
        simp [Finset.mem_sdiff, hxSmin]
      exact this.elim hxIn'
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
  have hvY : q.2 ∈ S.cl₁ (S.G0 q \ (S.Smin q \ {x})) := hMin hYss
  have hIncl :
    S.G0 q \ (S.Smin q \ {x}) ⊆ insert x (S.G0 q \ S.Smin q) :=
      sdiff_subset_insert_sdiff_of_mem (A := S.Smin q) (B := S.G0 q) (x := x) hxSmin
  have hvBase : q.2 ∈ S.cl₁ (insert x (S.G0 q \ S.Smin q)) :=
    (S.cl₁_monotone hIncl) hvY
  have hIncl2 :
    insert x (S.G0 q \ S.Smin q) ⊆ insert x (S.landing q) := by
      dsimp [System.landing]
      exact insert_subset_insert (x := x) (S.cl₁_extensive _)
  exact (S.cl₁_monotone hIncl2) hvBase

lemma firstGate_of_R_pair (S : System α) {q : Finset α × α} {x : α}
  (hq : q ∈ S.IntPairs) (hxR : x ∈ S.Rset q) :
  q.2 ∈ S.cl₁ (insert x (S.landing q)) :=
  S.firstGate_of_R_single (q := q) hq hxR

lemma Rset_triggers_head (S : System α) {q : Finset α × α} {x : α}
  (hq : q ∈ S.IntPairs) (hxR : x ∈ S.Rset q) :
  (q.2 ∉ S.landing q) ∧ (q.2 ∈ S.cl₁ (insert x (S.landing q))) :=
  And.intro (S.landing_in_CF (q := q) hq)
            (S.firstGate_of_R_single (q := q) hq hxR)





/-- `Rset q` は着地の外（`U \ landing q`）に含まれる。 -/
lemma Rset_subset_outside {q : Finset α × α} (S : System α) (hq : q ∈ S.IntPairs) :
  S.Rset q ⊆ (S.U \ S.landing q) := by
  -- 定義通り：R = Smin ∩ (U \ landing)。右側要素をそのまま取り出す。
  intro x hx
  exact (Finset.mem_inter.mp hx).2

/-- `Rset q` は head 自身と交わらない。 -/
lemma Rset_disjoint_head {q : Finset α × α} (S : System α) (hq : q ∈ S.IntPairs) :
  q.2 ∉ S.Rset q := by
  classical
  -- 反証法：もし head ∈ Rset なら
  intro hx
  -- Rset = Smin ∩ (U \ landing) なので head ∈ Smin
  have hxSmin : q.2 ∈ S.Smin q := (Finset.mem_inter.mp hx).1
  -- しかし Smin ⊆ G0 なので head ∈ G0 = erase head
  have hxG0 : q.2 ∈ S.G0 q := (S.Smin_subset_G0 (q := q) hq) hxSmin
  -- erase の定義から，head ∈ erase head は不可能
  have : q.2 ≠ q.2 := by
    -- `mem_erase` : x ∈ s.erase a ↔ x ∈ s ∧ x ≠ a
    have hx' := (Finset.mem_erase.mp (by exact hxG0)).2
    simp_all only [G0, Finset.mem_erase, ne_eq, not_true_eq_false, and_true]
  exact this rfl



/-! ## LBC（局所分岐負荷）の定義（if-sum 形）

`(K,x)` に対する LBC を，IntPairs 側での if-sum として定義する。
-/

/-- **LBC**：`(K,x)` に届く興味ペアからの負荷（if-sum 定義）。 -/
noncomputable def LBC (S : System α) (K : Finset α) (x : α) : ℚ :=
  ∑ q ∈ S.IntPairs,
    (if S.landing q = K ∧ x ∈ S.Rset q
     then (1 : ℚ) / ((S.Rset q).card : ℚ) else (0 : ℚ))

/-- `LBC K x` の if-sum を，`Contrib`（寄与集合）に引き直すための基本変形。 -/
lemma LBC_rewrite_if_sum
  (S : System α) (K : Finset α) (x : α) :
  S.LBC K x
    =
  ∑ q ∈ (S.IntPairs.filter (fun q => S.landing q = K ∧ x ∈ S.Rset q)),
      (1 : ℚ) / ((S.Rset q).card : ℚ) := by
  classical
  -- `∑ in s, ite p _ 0 = ∑ in s.filter p, _` をそのまま適用
  have h :=
    Finset.sum_filter
      (s := S.IntPairs)
      (p := fun q => S.landing q = K ∧ x ∈ S.Rset q)
      (f := fun q => (1 : ℚ) / ((S.Rset q).card : ℚ))
  simpa [LBC] using h.symm

/-! ## 発火トリガ：`x ∈ R(q)` ⇒ head が `insert x (landing q)` から発火 -/




  --rcases hmin with ⟨hSub, hSafe, hMin⟩
  --dsimp [System.landing] at *
  --simpa using hSafe

/-- `x ∈ R(q)` なら `(landing q, x)` は座席である。 -/
lemma Rset_goes_to_seat {q : Finset α × α} (S : System α) (hq : q ∈ S.IntPairs) :
  ∀ x ∈ S.Rset q, (S.landing q, x) ∈ S.SeatFinset := by
  intro x hx
  have hK := S.landing_in_CF (q := q) hq
  have hxOut : x ∈ (S.U \ S.landing q) := by
    exact (S.Rset_subset_outside (q := q) hq) hx
  -- `mem_SeatFinset_iff` で座席条件に翻訳
  have : (S.landing q, x) ∈ S.SeatFinset ↔
         (S.landing q ∈ S.ClosedFamilyFinset ∧ x ∈ (S.U \ S.landing q)) :=
    S.mem_SeatFinset_iff
  -- 仕上げ
  -- `exact (this.mpr ⟨hK.left, hxOut⟩)` だが `simpa using` は使わない方針

  have hpair : S.landing q ∈ S.ClosedFamilyFinset ∧ x ∈ (S.U \ S.landing q) := by
    constructor
    · -- 要求：`S.landing q` が one-pass 閉集合（かつ `⊆ U`）。
      -- これには `cl₁` の冪等性や、`IsMinCut` による不動点性が必要です。
      -- 例：`S.cl₁ (S.landing q) = S.landing q` と `S.landing q ⊆ S.U`。
      -- 現状の公理だけでは導出できないため、別補題で供給してください。
      admit
    · exact hxOut
  exact (this.mpr hpair)

/-- 初期座席 `(K,x)` に IntPairs から寄与は来ない。 -/
lemma no_IntPair_maps_to_initialSeat
  (S : System α) {K : Finset α} {x : α} (hInit : S.initialSeat K x) :
  ¬ (∃ q ∈ S.IntPairs, S.landing q = K ∧ x ∈ S.Rset q)
:= by
  classical
  rintro ⟨q, hq, hK, hxR⟩
  -- トリガ補題で「v=q.2 は insert x K から発火」かつ「v∉K」を得る
  have htrig := S.Rset_triggers_head (q := q) hq (x := x) --(hx := hxR)
  have hv_notK : q.2 ∉ K := by
    subst hK
    simp_all only [cl₁_def, forall_const, not_false_eq_true]
  have hv_in   : q.2 ∈ S.cl₁ (insert x K) := by
    simp
    subst hK
    simp_all only [not_false_eq_true, cl₁_def, true_and, forall_const]
  -- 初期座席の定義：cl₁ (insert x K) = insert x K
  have hcl : S.cl₁ (insert x K) = insert x K := S.initialSeat_closure_eq hInit
  -- これで q.2 ∈ insert x K
  have hv_in_ins : q.2 ∈ insert x K := by
    simp-- using hv_in
    subst hK
    simp_all only [not_false_eq_true, cl₁_def, true_and, or_false, Finset.mem_insert]
  -- q.2 = x ∨ q.2 ∈ K
  have hv_eq_or_in : q.2 = x ∨ q.2 ∈ K := by
    simpa [Finset.mem_insert] using hv_in_ins
  -- どちらでも矛盾
  cases hv_eq_or_in with
  | inr hv_inK =>
      exact hv_notK hv_inK
  | inl hv_eq =>
      -- `x ∈ Rset q` だが、Rset は head と素に交わる：矛盾
      have : q.2 ∈ S.Rset q := by simpa [hv_eq] using hxR
      exact (S.Rset_disjoint_head hq) this

end System
end NDSOnePass
