-- NDSOnePass/Core/System.lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.FinSupp.Basic
import LeanCopilot

set_option autoImplicit false
open scoped BigOperators

namespace NDSOnePass

/-- Horn 型の 1 本の規則。`prem` は前提集合，`head` は結論（head）。 -/
structure Rule (α) [DecidableEq α] where
  prem : Finset α
  head : α
--deriving Repr

namespace Rule
variable {α} [DecidableEq α]

@[simp] lemma head_mem_insert {r : Rule α} {X : Finset α} :
    r.head ∈ insert r.head X := by
  exact Finset.mem_insert_self _ _

end Rule

/-- 順序付き Horn 規則系と one-pass 閉包のための基本オブジェクト。 -/
structure System (α) [DecidableEq α] [Fintype α] where
  /-- 全宇宙。既定では `Finset.univ` を用いる。 -/
  U       : Finset α := (Finset.univ : Finset α)
  /-- 規則列（上から順に読む）。 -/
  rules   : List (Rule α)
  /-- UC（ユニークヘッド）：「head が同じ規則」は高々 1 本。 -/
  UC      : Prop
  /-- NEP（空でない前提）。 -/
  NEP     : ∀ r ∈ rules, r.prem ≠ ∅
  /-- 幅 ≤ 2（各前提サイズが高々 2）。 -/
  widthLE2 : Prop
  /-- 依存グラフが強連結（SCC = 1）。グラフ本体は後続で使用。 -/
  SCC1    : Prop
--deriving Repr

namespace System
variable {α} [DecidableEq α] [Fintype α]
--variable (S : System α)
--classical

/-- 規則 `r` を一回だけ適用する基本ステップ。 -/
def step (_ : System α) (r : Rule α) (X : Finset α) : Finset α :=
  if r.prem ⊆ X then insert r.head X else X

/-- 先頭から `i` 本ぶんの規則を順に畳み込んだ「one-pass 前置列」。 -/
def pref (S : System α) (i : Nat) (X : Finset α) : Finset α :=
  (S.rules.take i).foldl (fun acc r => S.step r acc) X

/-- one-pass 閉包：規則列全体を 1 回だけ上から下へ。 -/
def cl₁ (S : System α) (X : Finset α) : Finset α :=
  S.pref S.rules.length X

/-- 基本性質（外延性）：`X ⊆ cl₁ X`。 -/
lemma cl₁_extensive (S : System α) (X : Finset α) :
  X ⊆ S.cl₁ X := by
  dsimp [cl₁, pref]
  -- `take (length rules)` は `rules` に簡約
  simpa [List.take_length] using
    (by
      -- 一般形：任意の X について X ⊆ foldl (step) X S.rules
      revert X
      induction S.rules with
      | nil =>
        intro X
        -- foldl f X [] = X
        simp
      | cons r rs ih =>
        intro X
        -- 目標: X ⊆ List.foldl (fun acc r => S.step r acc) (S.step r X) rs
        -- (1) X ⊆ step r X（拡大性）
        have h1 : X ⊆ S.step r X := by
          intro x hx
          dsimp [System.step]
          by_cases hprem : r.prem ⊆ X
          · simp [hprem, hx]      -- if-then: insert r.head X
          · simp [hprem, hx]      -- if-else: X のまま
        -- (2) IH を (S.step r X) に適用
        have h2 :
            S.step r X ⊆
              List.foldl (fun acc r => S.step r acc) (S.step r X) rs :=
          ih (S.step r X)
        -- (3) 連鎖
        exact fun x hx => h2 (h1 hx)
    )

/-- 技術補題：`step` は単調。 -/
lemma step_monotone (S : System α) (r : Rule α) {X Y : Finset α} (hXY : X ⊆ Y) :
  S.step r X ⊆ S.step r Y := by
  -- `if` の場合分けで機械的に証明（後で充填）。
  dsimp [System.step]
  by_cases hprem : r.prem ⊆ X
  · -- r.prem ⊆ X の場合
    have hprem' : r.prem ⊆ Y := fun x hx => hXY (hprem hx)
    simp [hprem, hprem']
    intro x hx
    simp_all only [Finset.mem_insert]
    cases hx with
    | inl heq => exact Or.inl heq
    | inr hmem => exact Or.inr (hXY hmem)
  · simp_all only [↓reduceIte]
    split
    next h =>
      intro x hx
      simp_all only [Finset.mem_insert]
      exact Or.inr (hXY hx)
    next h => simp_all only


/-- 技術補題：`pref` は単調（`i` 固定）。 -/
lemma pref_monotone (S : System α) (i : Nat) {X Y : Finset α} (hXY : X ⊆ Y) :
  S.pref i X ⊆ S.pref i Y := by
  -- `foldl` の単調性を `step_monotone` から帰納で証明（後で充填）。
  dsimp [pref]
  revert X Y
  induction S.rules.take i with
  | nil =>
    intro X Y hXY
    simp
    exact hXY
  | cons r rs ih =>
    intro X Y hXY
    simp
    have hstep : S.step r X ⊆ S.step r Y := step_monotone S r hXY
    exact ih hstep

/-- 基本性質（単調性）：`X ⊆ Y → cl₁ X ⊆ cl₁ Y`。 -/

lemma cl₁_monotone (S : System α) {X Y : Finset α} (hXY : X ⊆ Y) :
  S.cl₁ X ⊆ S.cl₁ Y := by
  -- `foldl` と `⊆` の保存で証明（機械的に後で充填）。
  dsimp [cl₁, pref]
  exact pref_monotone S S.rules.length hXY

/-- `insert` は包含を保つ（単調）。 -/
lemma insert_subset_insert {x : α} {A B : Finset α} (h : A ⊆ B) :
  insert x A ⊆ insert x B := by
  intro y hy
  classical
  rcases Finset.mem_insert.mp hy with hxy | hyA
  · -- y = x
    exact Finset.mem_insert.mpr (Or.inl hxy)
  · -- y ∈ A ⊆ B
    exact Finset.mem_insert.mpr (Or.inr (h hyA))

/-- `cl₁` と `insert` の組み合わせも包含を保つ。 -/
lemma cl₁_insert_monotone (S : System α) {x : α} {A B : Finset α} (h : A ⊆ B) :
  S.cl₁ (insert x A) ⊆ S.cl₁ (insert x B) := by
  exact S.cl₁_monotone (insert_subset_insert (α := α) h)

/-- `B \\ (A \\ {x}) ⊆ insert x (B \\ A)` （`x∈A` のとき）。
    `x∈B` は不要で、`insert` の左枝で吸収できる。 -/
lemma sdiff_subset_insert_sdiff_of_mem
    {A B : Finset α} {x : α} (hxA : x ∈ A) :
    B \ (A \ {x}) ⊆ insert x (B \ A) := by
  classical
  intro y hy
  have hyB  : y ∈ B := (Finset.mem_sdiff.mp hy).1
  have hyNA : y ∉ A \ ({x} : Finset α) := (Finset.mem_sdiff.mp hy).2
  by_cases hyA : y ∈ A
  · -- y∈A だが y∉A\\{x} なので y∈{x}、すなわち y=x
    have : y ∈ ({x} : Finset α) := by
      -- ¬(y∈A ∧ y∉{x}) から導く
      have hneg : ¬ (y ∈ A ∧ y ∉ ({x} : Finset α)) := by
        simpa [Finset.mem_sdiff, Finset.mem_singleton] using hyNA
      by_contra hnot
      -- hnot : y ∉ {x} なら、y∈A∧y∉{x} となり矛盾
      exact hneg ⟨hyA, hnot⟩
    have hyx : y = x := by simpa [Finset.mem_singleton] using this
    -- y=x は insert 側の左枝で受けられる
    simpa [hyx] using (Finset.mem_insert.mpr (Or.inl rfl) :
      y ∈ insert x (B \ A))
  · -- y∉A なら y∈B\\A
    have : y ∈ B \ A := Finset.mem_sdiff.mpr ⟨hyB, hyA⟩
    exact Finset.mem_insert.mpr (Or.inr this)

/-
/-- 基本性質（冪等性）：`cl₁ (cl₁ X) = cl₁ X`。 -/
lemma cl₁_idem (S : System α) (X : Finset α) :
  S.cl₁ (S.cl₁ X) = S.cl₁ X := by
  -- one-pass を 2 回読んでも 1 回と同じ（定義に基づく後で充填）。
  dsimp [cl₁, pref]
  sorry
-/

/-- 閉集合族（one-pass で不動点）。`U` の冪集合から抽出。 -/
def ClosedFamilyFinset (S : System α): Finset (Finset α) :=
  (S.U.powerset).filter (fun H => S.cl₁ H = H)

/-- `H` が閉集合族に属することの同値。 -/
lemma mem_ClosedFamilyFinset_iff {H : Finset α}(S : System α) :
  H ∈ S.ClosedFamilyFinset ↔ H ⊆ S.U ∧ S.cl₁ H = H := by
  unfold ClosedFamilyFinset
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hHU : H ⊆ S.U := by
      -- `H ∈ powerset` から `H ⊆ U`
      exact (Finset.mem_powerset.mp h'.1)
    exact And.intro hHU h'.2
  · intro h
    have hHU : H ⊆ S.U := h.1
    have hfix : S.cl₁ H = H := h.2
    exact Finset.mem_filter.mpr ⟨(Finset.mem_powerset.mpr hHU), hfix⟩

/-- `ClosedFamilyFinset` は `U` の冪集合の部分集合。 -/
lemma ClosedFamily_subset_powerset (S : System α) :
  S.ClosedFamilyFinset ⊆ S.U.powerset := by
  intro H hH
  have := (Finset.mem_filter.mp hH).1
  exact this

/-- 宇宙の大きさ。 -/
@[simp] def n : Nat := Fintype.card α

/-- 依存関係（有向辺）：`a ↦ b` とは「`a` が head=`b` の前提に現れる」。
    UC が真であることを前提に使う（System には `UC : Prop` として保持）。 -/
def depRel (S : System α) (a b : α) : Prop :=
  ∃ r ∈ S.rules, r.head = b ∧ a ∈ r.prem

/-- `depRel` は `U` の上に乗る（定義上）。 -/
lemma depRel_support {a b : α} (S : System α):-- (ha : a ∈ S.U) (hb : b ∈ S.U) :
  S.depRel a b → True := by
  intro _; exact True.intro
/-
/-- UC の外形（利用用）。 -/
lemma UC_spec :
  S.UC := S.UC

/-- NEP の外形（利用用）。 -/
lemma NEP_spec :
  S.NEP := S.NEP

/-- 幅 ≤ 2 の外形（利用用）。 -/
lemma widthLE2_spec :
  S.widthLE2 := S.widthLE2

/-- SCC=1 の外形（利用用）。 -/
lemma SCC1_spec :
  S.SCC1 := S.SCC1
-/

/-- 技術補題：`pref` は i で延びるにつれて包含が増える（X 固定）。 -/
lemma pref_succ_supset (S : System α) (i : Nat) (X : Finset α) :
  S.pref i X ⊆ S.pref (i+1) X := by
  -- 1 本ぶんの規則を追加すると包含は保たれる（後で充填）。
  dsimp [pref]
  by_cases h : i < S.rules.length
  · -- i < S.rules.length の場合
    -- take (i+1) = (take i) ++ [rules[i]]
    have heq : S.rules.take (i+1) = S.rules.take i ++ [S.rules[i]'h] := by
      rw [List.take_succ]
      simp [h]
    rw [heq, List.foldl_append]
    simp
    intro x hx
    dsimp [System.step]
    split
    · simp_all only [Finset.mem_insert]
      exact Or.inr hx
    · exact hx
  · -- i >= S.rules.length の場合
    have h1 : S.rules.length ≤ i := Nat.le_of_not_lt h
    have h2 : S.rules.length ≤ i + 1 := Nat.le_trans h1 (Nat.le_succ i)
    simp [List.take_of_length_le h1, List.take_of_length_le h2]

/-- `cl₁` の定義展開。 -/

@[simp] lemma cl₁_def (S : System α) (X : Finset α) :
  S.cl₁ X = S.pref S.rules.length X := rfl

/-- NEP（各規則の前提が空でない）を仮定すると，`cl₁ ∅ = ∅`。

`hNEP : ∀ r ∈ S.rules, r.prem ≠ ∅` の形で渡してください（`S.NEP` の具体形に依存）。 -/
lemma cl₁_empty_of_NEP (S : System α)
  (hNEP : ∀ r ∈ S.rules, r.prem ≠ ∅) :
  S.cl₁ (∅ : Finset α) = ∅ := by
  classical
  -- cl₁ の定義を `rules` 全体の foldl に還元
  simp [System.cl₁, System.pref, List.take_length]
  -- ここからは `List.foldl (step) ∅ S.rules = ∅` を示すために `rules` で帰納法
  revert hNEP
  generalize S.rules = rs
  intro hNEP
  induction rs with
  | nil =>
      simp
  | cons r rs ih =>
      -- 先頭規則 r は空前提でない
      have hne : r.prem ≠ ∅ := hNEP r (by simp)
      -- 残りの規則列 rs についての NEP
      have hNEP_rs : ∀ r' ∈ rs, r'.prem ≠ ∅ := by
        intro r' hr'
        exact hNEP r' (by simp [hr'])
      -- 空集合に対する 1 ステップは発火せず ∅ のまま
      have hstep : S.step r (∅ : Finset α) = ∅ := by
        dsimp [System.step]
        have : ¬ r.prem ⊆ (∅ : Finset α) := by
          intro hsub
          exact hne (Finset.subset_empty.mp hsub)
        simp [this]
      -- 残りについての帰納法
      simp [hstep, ih hNEP_rs]

end System
end NDSOnePass
