import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.SymmDiff
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.NDS
import Twostem.MainCore
import Twostem.Bridge

--import Twostem.Fiber --FreeOfなどで必要。
--import Twostem.Synchronous
--import Twostem.Derivation --mem_closure_iff_derivなど。

namespace Twostem

open scoped BigOperators
open scoped symmDiff
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] [Fintype (Rule α)]

/- 速攻版の Δ 定義：`Δ ρ R t = (AddedFamily ρ R t).card` -/
--noncomputable def Δ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) : ℕ :=
--  (addedFamily R t).card

-- 3引数 addedFamily を衝突回避のため AF と呼ぶ
variable (AF :
  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))

/-- Δ は 3引数版 addedFamily に揃える（第1引数に AF を明示） -/
noncomputable def Δ
  (AF :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) : ℕ :=
  (AF ρ R t).card

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
@[simp] lemma Δ_def
  (AF :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) :
  Δ AF ρ R t = (AF ρ R t).card := rfl

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
@[simp] lemma Δ_cast
  (AF :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) :
  ((Δ AF ρ R t : ℕ) : ℤ) = ((AF ρ R t).card : ℤ) := rfl

/- このセクション内では `Δ ρ R t` と短く書けるようにする -/
--local notation "Δ" => Δ AF

/- 点wise 版（左 = 右 なので ≤ が成り立つ） -/
omit [Fintype α][DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma addedFamily_card_le_delta
  [DecidableEq α] [DecidableEq (Rule α)] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  ∀ ⦃t : Rule α⦄, t ∈ R → #(AF ρ R t) ≤ Δ AF ρ R t := by
  classical
  intro t ht
  -- Δ を展開して両辺一致
  change (AF ρ R t).card ≤ (AF ρ R t).card
  exact le_of_eq rfl

/- 総和版（各 t で上の点wise を流し込む） -/
omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma witness_sum_le_sum_delta
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  ∑ t ∈ R, #(AF ρ R t) ≤ ∑ t ∈ R, Δ AF ρ R t := by
  classical
  refine Finset.sum_le_sum ?termwise
  intro t ht
  exact addedFamily_card_le_delta (AF := AF) ρ R ht

--********** Bridge I 本体：総和版 **********
/- 代表系・欠損・超過・自由点（論文の Barrier/Charging 側の量） -/
--variable (addedFamily :
--  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
/- 各規則 t に対する「Witness で数えた個数」の局所恒等式で使う局所寄与 -/
--variable (Excess_t : RuleOrder α → Finset (Rule α) → Rule α → Finset α → ℤ)
--variable (Missing_t : RuleOrder α → Finset (Rule α) → Rule α → Finset α → ℤ)

/- Witness で (t,A) が B に課金される A の個数（ℤ に持ち上げ） -/
variable (isWitness :
  RuleOrder α → Finset (Rule α) → Finset α → Finset α → Rule α → Prop)

noncomputable def chargeCount
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α) : ℤ := by
  classical
  exact ↑(#({A ∈ AF ρ R t | ∃ S, A = B ∪ S ∧ isWitness ρ R B S t}))

--別ファイルで証明するかも。

/-- 速攻ルート定義：`Excess_t = chargeCount` -/
noncomputable def Excess_t
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (B : Finset α) : ℤ :=
  chargeCount  (AF:=AF) (isWitness:=isWitness) ρ R B t

/-- 速攻ルート定義：`Missing_t = 0` -/
noncomputable def Missing_t
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (B : Finset α) : ℤ := 0

/-- 大域 Excess：各 t の局所 Excess_t を合算 -/
noncomputable def Excess
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) : ℤ :=
  ∑ t ∈ R, Excess_t AF isWitness ρ R t B

/-- 大域 Missing：各 t の局所 Missing_t を合算 -/
noncomputable def Missing
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) : ℤ :=
  ∑ t ∈ R, Missing_t  ρ R t B


variable (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
--variable (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
--variable (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Free    : RuleOrder α → Finset (Rule α) → Finset α)

/-! ## Charging の骨組み（このスレで定義・証明していく） -/

lemma AF_mem_iff
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α) :
  A ∈ AF ρ R t ↔ ∃ (B S : Finset α), A = B ∪ S ∧ isWitness ρ R B S t := by
  sorry  -- 本タスクでは仕様仮定として与えられる（後で定義展開で証明予定）

lemma AF_witness_exists
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A : Finset α} (hA : A ∈ AF ρ R t)
  : ∃ B S, A = B ∪ S ∧ isWitness ρ R B S t := by
  -- AF の会員同値を取り出す
  have hiff := AF_mem_iff AF isWitness ρ R t A
  -- `hA : A ∈ AF ρ R t` から右向きで存在を得る（明示）
  have hex : ∃ (B S : Finset α), A = B ∪ S ∧ isWitness ρ R B S t :=
    hiff.mp hA
  exact hex

/-
-- 同じ A の分解に対する基底の一意性
lemma witness_base_unique
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (A B₁ S₁ B₂ S₂ : Finset α)
  (h1 : A = B₁ ∪ S₁) (h2 : A = B₂ ∪ S₂)
  (w1 : isWitness ρ R B₁ S₁ t) (w2 : isWitness ρ R B₂ S₂ t) :
  B₁ = B₂ := by
  sorry
-/

/-- B が witness の基底である、の最小述語（A3 でも使用） -/
def IsBaseOfWitness
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) : Prop :=
  ∃ (t : Rule α) (A S : Finset α),
      A ∈ AF ρ R t ∧ A = B ∪ S ∧ isWitness ρ R B S t

/--
Rep の会員同値（仕様）:
`B ∈ Rep ρ R ↔ IsBaseOfWitness ρ R B`.

※ ここは仕様として提示し，実装は後日（親スレ側で）埋める想定。
-/
def IsBaseOfWitness_closure
  [Fintype α] [DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) : Prop :=
  ∃ (t : Rule α) (A S : Finset α),
    A ∈ addedFamily (α:=α) R t ∧
    A = syncCl (R.erase t) (B ∪ S) ∧
    isWitness  ρ R B S t

lemma Rep_mem_iff_closure
  [Fintype α] [DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  B ∈ Rep ρ R ↔ IsBaseOfWitness_closure isWitness ρ R B := by
  -- 仕様段階では「存在」方向をAF_witness_exists_closureで取る
  -- 一意性側は exists_unique_base_for_added_closure で保証
  sorry

--こちらではなく上を証明するのかも。するとこれを引用している箇所も変える必要がある。
lemma Rep_mem_iff
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  B ∈ Rep ρ R ↔
    IsBaseOfWitness AF isWitness ρ R B := by
  -- SPEC: 代表集合の設計が確定した段階で実装する
  -- 例：左→右 は Rep の構成定義から witness を回収、
  --    右→左 は witness の基底が Rep に入ることを示す。
  -- 現段階では仕様の受け皿のみ提供。
  sorry

-- Witness の基底は代表系に属する。これは古い。witness_base_in_Rep_closureに置き換えられる。
/-- **A3. witness_base_in_Rep**
`A ∈ AF ρ R t`, `A = B ∪ S`, `isWitness ρ R B S t` なら `B ∈ Rep ρ R`。 -/
lemma witness_base_in_Rep
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A B S : Finset α}
  (hA  : A ∈ AF ρ R t)
  (hAS : A = B ∪ S)
  (hW  : isWitness ρ R B S t) :
  B ∈ Rep ρ R := by
  -- Rep の会員同値を取り出す
  have hiff :=
    Rep_mem_iff AF isWitness Rep ρ R B
  -- まず IsBaseOfWitness を構成する
  have hBase :
      IsBaseOfWitness AF isWitness ρ R B := by
    -- 証人として t, A, S を与える
    refine Exists.intro t ?_
    refine Exists.intro A ?_
    refine Exists.intro S ?_
    -- 3条件を並べる
    exact And.intro hA (And.intro hAS hW)
  -- Iff の右方向で membership を得る（`simpa using` は使わない）
  exact (Iff.mpr hiff) hBase

/-- witness の基底 B は Rep に属する（closure 版） -/
lemma witness_base_in_Rep_closure
  [Fintype α] [DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A B S : Finset α}
  (hA   : A ∈ addedFamily (α:=α) R t)
  (hAeq : A = syncCl (R.erase t) (B ∪ S))
  (hW   : isWitness ρ R B S t) :
  B ∈ Rep ρ R := by
  -- Rep の会員同値（closure 版）を取り出す
  --   B ∈ Rep ρ R ↔ IsBaseOfWitness_closure ρ R B
  have hiff :=
    Rep_mem_iff_closure (α:=α) (ρ:=ρ) (R:=R) (B:=B)
  -- 右辺（存在命題）を構成する
  --   証人として t, A, S を与え，
  --   (1) A ∈ addedFamily, (2) A = syncCl (R.erase t) (B ∪ S), (3) isWitness …
  have hBase :
      IsBaseOfWitness_closure isWitness ρ R B := by
    refine Exists.intro t ?_
    refine Exists.intro A ?_
    refine Exists.intro S ?_
    exact And.intro hA (And.intro hAeq hW)
  -- Iff の右→左で membership を得る
  exact (Rep_mem_iff_closure isWitness Rep ρ R B).mpr hBase

/-
/- Witness による基底 B の一意性：同じ A の分解なら基底は一致 -/
variable (witness_base_unique :
  ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
    (A B₁ S₁ B₂ S₂ : Finset α),
    A = B₁ ∪ S₁ → A = B₂ ∪ S₂ →
    isWitness ρ R B₁ S₁ t → isWitness ρ R B₂ S₂ t → B₁ = B₂)

/- Witness の基底は代表系に属する -/
variable (witness_base_in_Rep :
  ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
    (B S : Finset α),
    isWitness ρ R B S t → B ∈ Rep ρ R)

/- (A∈AF) なら Witness 分解が存在：A = B ∪ S かつ isWitness … -/
variable (AF_witness_exists :
  ∀ ρ R t {A}, A ∈ AF ρ R t → ∃ B S, A = B ∪ S ∧ isWitness ρ R B S t)
-/

/- (t, A) の請求先 B を与える写像（`Rep ρ R` の元になる） -/
lemma exists_unique_base_for_added
  --(AF :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  --(Rep :
  --  RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A : Finset α} (hA : A ∈ AF ρ R t) (hUC : UniqueChild (α:=α) R) (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS : NoSwap (R.erase t)) (hA: OnlyTLastDiff ρ R t)
 :
  ∃! (B : Finset α),
    B ∈ Rep ρ R ∧ ∃ S, A = B ∪ S ∧ isWitness ρ R B S t := by
  classical

  obtain ⟨B, S, hAs, hW⟩ := AF_witness_exists
    (AF:=AF) (isWitness:=isWitness)
    (ρ:=ρ) (R:=R) (t:=t) (A:=A) ?_

  

    --AF_witness_exists (ρ:=ρ) (R:=R) (t:=t) (A:=A) hA
  -- 2) その基底 B は代表系に属する
  have hBmem : B ∈ Rep ρ R := by
    exact witness_base_in_Rep AF (fun ρ R B S t => A ∈ AF ρ R t) Rep ρ R t hA hAs hA

   -- 3) 存在と一意性で ∃! を構成
  refine ExistsUnique.intro B ?hex ?uniq
  · -- 存在部
    exact And.intro hBmem ⟨S, And.intro hAs hW⟩
  · -- 一意性：条件を満たす任意の B' は B に等しい
    intro B' hB'
    rcases hB' with ⟨_hB'in, ⟨S', hAs', hW'⟩⟩

    let wb := witness_base_unique ρ R t hUC
    apply wb hNTF hNS
    exact hA
    exact hAs'
    exact hAs
    show Twostem.isWitness ρ R B' S' t
    sorry
    show Twostem.isWitness ρ R B S t
    sorry






lemma exists_unique_base_for_added_closure
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (Rep : Finset (Finset α))
  -- 主同値（親スレ推奨形）
  (AF_mem_iff_closure :
    ∀ {A : Finset α},
      A ∈ addedFamily (α:=α) R t
      ↔ ∃ (B S : Finset α),
           A = syncCl (R.erase t) (B ∪ S) ∧ isWitness  ρ R B S t)
  -- witness の基底は Rep に属する（closure 版）
  (witness_base_in_Rep_closure :
    ∀ {A B S : Finset α},
      A ∈ addedFamily (α:=α) R t →
      A = syncCl (R.erase t) (B ∪ S) →
      isWitness  ρ R B S t →
      B ∈ Rep)
  -- 同じ A（= 同じ閉包像）を与える witness なら基底は一意
  (base_unique_of_closure_witness :
    ∀ {B₁ S₁ B₂ S₂ : Finset α},
      B₁ ∈ Rep → B₂ ∈ Rep →
      syncCl (R.erase t) (B₁ ∪ S₁) = syncCl (R.erase t) (B₂ ∪ S₂) →
      isWitness  ρ R B₁ S₁ t →
      isWitness  ρ R B₂ S₂ t →
      B₁ = B₂)
  {A : Finset α} (hA : A ∈ addedFamily (α:=α) R t)
  :
  ∃! (B : Finset α),
    B ∈ Rep ∧ ∃ S, A = syncCl (R.erase t) (B ∪ S) ∧ isWitness ρ R B S t := by
  classical
  -- 1) AF → witness（閉包つき）の存在
  rcases (AF_mem_iff_closure (A:=A)).mp hA with ⟨B₀, S₀, hAeq, hW₀⟩

  -- 2) その基底 B₀ は代表集合に属する
  have hB₀mem : B₀ ∈ Rep :=
    witness_base_in_Rep_closure (A:=A) (B:=B₀) (S:=S₀) hA hAeq hW₀

  -- 3) ∃! の構成：存在部
  refine ExistsUnique.intro B₀ ?hexists ?huniq
  · -- 存在：B₀ が条件を満たす
    refine And.intro hB₀mem ?hex2
    exact ⟨S₀, hAeq, hW₀⟩

  -- 4) 一意性：同条件を満たす任意の B は B₀ と等しい
  · intro B hB
    rcases hB with ⟨hBmem, ⟨S, hAeq', hW⟩⟩
    -- 両者とも同じ A を与えるので、閉包像が等しい
    have hclEq :
      syncCl (R.erase t) (B ∪ S) = syncCl (R.erase t) (B₀ ∪ S₀) := by
      -- A = syncCl … = A から対称で結ぶ
      -- 明示に： (B,S) 側 = A かつ (B₀,S₀) 側 = A
      -- より、左辺 = 右辺
      -- 具体的には trans で
      sorry
      --exact Eq.trans hAeq' (Eq.symm hAeq)
    -- 代表性 + witness + 閉包像一致 ⇒ 基底一意
    exact base_unique_of_closure_witness hBmem hB₀mem hclEq hW hW₀

/-- Task A の corollary：`chargeTo` の「AF内」での Rep 所属 -/
noncomputable def chargeTo
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α) :
  Finset α := by
  classical
  by_cases hA : A ∈ AF ρ R t
  ·
    -- Task A（存在一意）から B を classical choice で取り出して返す
    have hexu :
      ∃! (B : Finset α),
        B ∈ Rep ρ R ∧ ∃ S, A = B ∪ S ∧ isWitness ρ R B S t :=
      exists_unique_base_for_added
        (AF:=AF) (Rep:=Rep)
        (ρ:=ρ) (R:=R) (t:=t) (A:=A) hA
        (isWitness:=isWitness)
        --(AF_witness_exists:=AF_witness_exists)
        --(witness_base_unique:=witness_base_unique)
        --(witness_base_in_Rep:=witness_base_in_Rep)
    exact Classical.choose (ExistsUnique.exists hexu)
  ·
    -- AF 外は使われないので、デフォルト値として ∅ を返す
    exact ∅

--variable (chargeTo : RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)

lemma chargeTo_mem_Rep
  (ρ : RuleOrder α) (R : Finset (Rule α))
  {t : Rule α} {A : Finset α}
  (hA : A ∈ AF ρ R t) :
  chargeTo AF isWitness Rep ρ R t A
    ∈ Rep ρ R := by
  classical
  -- `chargeTo` を展開して AF 内外で分岐
  dsimp [chargeTo]
  by_cases h : A ∈ AF ρ R t
  ·
    -- AF ケース：Task A の一意存在から choice した基底が Rep に属する
    have hexu :
      ∃! (B : Finset α),
        B ∈ Rep ρ R ∧ ∃ S, A = B ∪ S ∧ isWitness ρ R B S t :=
      exists_unique_base_for_added
        (AF:=AF) (Rep:=Rep)
        (ρ:=ρ) (R:=R) (t:=t) (A:=A) h
        (isWitness:=isWitness)
        --(AF_witness_exists:=AF_witness_exists)
        --(witness_base_unique:=witness_base_unique)
        --(witness_base_in_Rep:=witness_base_in_Rep)
    -- choice で得た基底は性質を満たす：特に Rep 所属が左成分
    have hprop :
      (Classical.choose (ExistsUnique.exists hexu) ∈ Rep ρ R) ∧
        ∃ S, A = Classical.choose (ExistsUnique.exists hexu) ∪ S ∧
          isWitness ρ R (Classical.choose (ExistsUnique.exists hexu)) S t :=
      Classical.choose_spec (ExistsUnique.exists hexu)
    simp_all only [↓reduceDIte]

  ·
    -- こちらの分岐は前提 hA と矛盾（到達不能）
    exact (h hA).elim

/- chargeTo の値は代表系に属する（仮定として受け取る） -/
--variable (chargeTo_mem_Rep :
--  ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α),
--    A ∈ AF ρ R t → chargeTo ρ R t A ∈ Rep ρ R )

/-- B が t から受け取る寄与（ℤ）：(t の addedFamily のうち B に課金された個数) -/
noncomputable def contrib_from
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (t : Rule α) (B : Finset α) : ℤ :=
  (((AF ρ R t).filter (fun A => chargeTo (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t A = B)).card : ℤ)


/- 単一の規則 t についての局所的下界 -/
lemma per_rule_lower_bound
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) :
  ∑ B ∈ Rep ρ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B
    ≤ ((AF ρ R t).card : ℤ) := by
  -- ここから証明contrib_from ρ R t B := by
  -- TODO: 各 A をちょうど 1 回どこかの B へ課金する（重複なし）
  classical
  -- 記号整理
  set S := AF ρ R t
  set P := Rep ρ R
  -- B ごとのファイバー
  let T : Finset α → Finset (Finset α) :=
    fun B => S.filter (fun A => chargeTo (AF:=AF) Rep (isWitness:=isWitness) ρ R t A = B)
  -- 相異なる B 同士でファイバーは互いに素
  have hdisj : ∀ {B₁} (h₁ : B₁ ∈ P) {B₂} (h₂ : B₂ ∈ P), B₁ ≠ B₂ →
      Disjoint (T B₁) (T B₂) := by
    intro B₁ h₁ B₂ h₂ hne
    refine Finset.disjoint_left.2 ?_
    intro A hA₁ hA₂
    have h₁' := (Finset.mem_filter.1 hA₁).2 -- chargeTo A = B₁
    have h₂' := (Finset.mem_filter.1 hA₂).2 -- chargeTo A = B₂
    have : B₁ = B₂ := by
      -- h₂' : chargeTo A = B₂, 書き換えに h₁'
      -- ⇒ B₁ = B₂
      simpa [h₁'] using h₂'
    exact hne this
  -- ∪B T(B) ⊆ S（各ファイバーは S の filter）
  have hsub : (P.biUnion T) ⊆ S := by
    intro A hA
    rcases Finset.mem_biUnion.1 hA with ⟨B, hB, hAf⟩
    exact (Finset.mem_filter.1 hAf).1
  -- 自然数で：∑_B |T(B)| ≤ |S|
  have hNat : ∑ B ∈ P, (T B).card ≤ S.card := by
    -- |⋃ T(B)| = ∑ |T(B)|（互いに素）
    have hEq : (P.biUnion T).card = ∑ B ∈ P, (T B).card := by
      -- `card_biUnion` は左＝右の向き
      refine Finset.card_biUnion ?_
      intro B₁ h₁ B₂ h₂ hne; exact hdisj h₁ h₂ hne
    -- ⊆ により card(⋃) ≤ |S|
    have hLe : (P.biUnion T).card ≤ S.card := by exact card_le_card hsub
    -- 置換して結論
    -- （`simpa` は使わず，calc で書く）
    calc
      ∑ B ∈ P, (T B).card = (P.biUnion T).card := by exact hEq.symm
      _ ≤ S.card := hLe
  -- 整数へ持ち上げ：∑_B (|T(B)|:ℤ) ≤ (|S|:ℤ)
  have hInt : ((∑ B ∈ P, (T B).card) : ℤ) ≤ (S.card : ℤ) := by
    -- `Int.ofNat_le.2` で ℕ ≤ を ℤ ≤ に持ち上げ
    simp_all only [ne_eq, biUnion_subset_iff_forall_subset, filter_subset, implies_true, P, T, S]
    exact mod_cast hNat

  -- 右辺（contrib の総和）＝ ∑_B (|T(B)|:ℤ)
  have hR : ∑ B ∈ P, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B
              = ((∑ B ∈ P, (T B).card) : ℤ) := by
    -- 各項ごとに `contrib_from` の定義を展開
    refine Finset.sum_congr rfl ?_ ; intro B hB
    simp [contrib_from, S, T]
  -- したがって ∑ contrib ≤ |S|
  have hRle : ∑ B ∈ P, contrib_from (AF := AF) (Rep := Rep) (isWitness := isWitness) ρ R t B
                ≤ (S.card : ℤ) := by
    -- `calc` で等式→不等式
    calc
      ∑ B ∈ P, contrib_from (AF := AF) (Rep := Rep) (isWitness := isWitness) ρ R t B
          = ((∑ B ∈ P, (T B).card) : ℤ) := hR
      _ ≤ (S.card : ℤ) := hInt
  -- 目標形に並べ替えて終了
  -- 目標は (|S|:ℤ) ≥ ∑ contrib
  exact hRle

omit [DecidableEq α] [Fintype α] in
/- すべての規則で合計した寄与を、Barrier の右辺に整理 -/
lemma sum_over_rules_reshuffle
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ∑ B ∈ Rep ρ R,
      contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
    = ∑ B ∈ Rep ρ R,
        (Excess AF isWitness ρ R B
          - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
  classical
  -- ∑t∑B … = ∑B∑t … （和の順序入替え）
  have hswap :
    (∑ t ∈ R, ∑ B ∈ Rep ρ R,
        contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
      = ∑ B ∈ Rep ρ R, ∑ t ∈ R,
          contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B := by
    -- 標準補題 `Finset.sum_comm`
    exact Finset.sum_comm
  -- 各 B ごとに chargingIdentity を適用
  have happly :
    (∑ B ∈ Rep ρ R, ∑ t ∈ R,
        contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
      = ∑ B ∈ Rep ρ R,
          (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    refine Finset.sum_congr rfl ?_ ; intro B hB
    -- 右辺の各項に chargingIdentity
    have h := chargingIdentity B hB
    -- 書き換え
    exact h
  -- まとめ
  exact Eq.trans hswap happly

omit [DecidableEq α] [Fintype α] in
/- **Bridge II（addedFamily 版）**：総和の下界 -/
lemma addedFamily_sum_lower_bound
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ((AF ρ R t).card : ℤ))
    ≥ ∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B
      - (Finset.card (Free ρ R) : ℤ) * ∑ B ∈ Rep ρ R, Missing ρ R B := by
  classical
  -- 1) 左辺 ≥ ∑_{t∈R} ∑_{B∈Rep} contrib_from …
  have h1 :
    (∑ t ∈ R, ((AF ρ R t).card : ℤ))
      ≥ ∑ t ∈ R, ∑ B ∈ Rep ρ R,
            contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B := by
    -- 各 t ごとに per_rule_lower_bound を足し合わせる（Finset.sum_le_sum）
    refine Finset.sum_le_sum ?_ ; intro t ht
    exact per_rule_lower_bound AF  isWitness Rep ρ R t

  -- 2) 右辺の二重和を Barrier 右辺に並べ替え
  have h2 :
    (∑ t ∈ R, ∑ B ∈ Rep ρ R,
        contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
      = ∑ B ∈ Rep ρ R,
          (Excess AF isWitness ρ R B
            - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    apply sum_over_rules_reshuffle
    exact fun B a => chargingIdentity B a

  --    ∑ addedFamily.card ≥ (二重和) = (Barrier RHS)
  --    最後に `∑ (Excess - c*Missing)` を `∑ Excess - c*∑ Missing` に分配
  set c : ℤ := (Finset.card (Free ρ R) : ℤ) with hc
  have hdist :
    (∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - c * Missing ρ R B))
      = (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
        - (∑ B ∈ Rep ρ R, c * Missing ρ R B) := by
    -- Finset.sum_sub_distrib の直接適用
    exact sum_sub_distrib (Excess AF isWitness ρ R) fun x => c * Missing ρ R x

  have hmul :
    (∑ B ∈ Rep ρ R, c * Missing ρ R B)
      = c * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
    -- Finset.mul_sum は `c * ∑ f = ∑ c * f`。向きを合わせるために `symm` を取る。
    have base := Finset.mul_sum (Rep ρ R) (fun B => Missing ρ R B) c
    -- base : c * (∑ Missing) = ∑ (c * Missing)
    -- 目標は `∑ (c * Missing) = c * (∑ Missing)`
    exact base.symm
  calc
    (∑ t ∈ R, ((AF ρ R t).card : ℤ))
        ≥ (∑ t ∈ R, ∑ B ∈ Rep ρ R,
              contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B) := h1
    _ = ∑ B ∈ Rep ρ R,
          (Excess AF isWitness ρ R B - c * Missing ρ R B) := by

          calc
            ∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness)  ρ R t B
                = ∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := h2
            _ = ∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - c * Missing ρ R B) := by
                  apply congrArg (fun z => ∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - z * Missing ρ R B))
                  exact hc

    _ = (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
          - (∑ B ∈ Rep ρ R, c * Missing ρ R B) := by
          exact hdist
    _ = (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
          - c * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
          -- `∑ c * Missing` を `c * ∑ Missing` に置換
          -- 注意：ここでは `rw [hmul]` と等価
          have : (∑ B ∈ Rep ρ R, c * Missing ρ R B)
                    = c * (∑ B ∈ Rep ρ R, Missing ρ R B) := hmul
          -- 右辺第2項を書き換える
          exact by
            -- a - (∑ c*f) から a - c*(∑ f) へ
            -- `rw [this]` と同等の変形
            -- ただし `simpa` は使わない
            -- 書き換え用の等式 `this` を使う
            refine congrArg (fun z => (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B) - z) this


lemma chargeTo_mem_Rep_lemma

  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α} {A : Finset α}
  (hA : A ∈ AF ρ R t) :
  chargeTo (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t A ∈ Rep ρ R := by
  exact chargeTo_mem_Rep AF  isWitness Rep ρ R hA

lemma chargingIdentity
  (ρ : RuleOrder α) (R : Finset (Rule α))
  {B : Finset α} (hB : B ∈ Rep ρ R)
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R,
            contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) :
  (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
    = Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  exact hcore ρ R B hB

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- **全体版：Barrier/Charging の合算不等式**
    核等式（hcore）と `per_rule_lower_bound` を組み合わせて、
    \sum_B (Excess(B) - |Free|·Missing(B)) ≤ \sum_t |addedFamily ρ R t|.
    ここでは Δ ではなく card で述べ、その後に Δ 版コローラリを出します。 -/
--addedFamilyの仮定を除くべきかも。そして、AFを使う。
--addedFamilyをAFに置き換える。Excessもいらないかも。
lemma charging_sum_lower_bound_card
  (addedFamily :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
--  (chargeTo :
--    RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
  (contrib_from :
    (ρ : RuleOrder α) → (R : Finset (Rule α)) → (t : Rule α) → (B : Finset α) → ℤ)
  (per_rule_lower_bound :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α),
      ∑ B ∈ Rep ρ R, contrib_from ρ R t B
        ≤ ((addedFamily ρ R t).card : ℤ))
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R, contrib_from ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  (∑ B ∈ Rep ρ R,
     (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
  ≤ (∑ t ∈ R, ((addedFamily ρ R t).card : ℤ)) := by
  classical
  -- 1) per-rule の下界を t で総和
  have h1 :
      (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B)
        ≤ (∑ t ∈ R, ((addedFamily ρ R t).card : ℤ)) := by
    refine Finset.sum_le_sum ?term
    intro t ht
    exact per_rule_lower_bound ρ R t
  -- 2) Fubini（総和の入れ替え）
  have hswap :
      (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B)
        = (∑ B ∈ Rep ρ R, ∑ t ∈ R, contrib_from ρ R t B) := by
    -- Finset.sum_comm で入れ替え
    have := Finset.sum_comm (s := R) (t := Rep ρ R)
      (f := fun t B => contrib_from ρ R t B)
    -- `∑ B ∈ Rep ρ R, ...` の「∈」形に合わせるために eta 変形をほどこす
    -- （各側とも binder の並びが一致しているので rfl で整合します）
    exact this
  -- 3) 内側（B 固定）の和を chargingIdentity で展開
  have h2 :
      (∑ B ∈ Rep ρ R, ∑ t ∈ R, contrib_from ρ R t B)
        = (∑ B ∈ Rep ρ R,
             (Excess  ρ R B
               - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) := by
    refine Finset.sum_congr rfl ?step
    intro B hB
    -- chargingIdentity をそのまま適用
    have hId :
        (∑ t ∈ R, contrib_from ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B :=
      hcore ρ R B hB
    exact hId
  -- 4) まとめ：h1 と等式 hswap, h2 を突き合わせる
  --    左辺を書き換えて目的不等式を得る
  have hLHS_rewrite :
      (∑ B ∈ Rep ρ R,
         (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
      = (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B) := by
    -- hswap と h2 から
    -- h2 : ∑_B ∑_t ... = ∑_B (Excess - |Free|*Missing)
    -- 従って ∑_B (Excess - …) = ∑_B ∑_t ...
    -- さらに hswap で ∑_B ∑_t = ∑_t ∑_B
    -- 以上を連結して等式を得る
    -- 等式連鎖をそのまま書き下す：
    --   LHS = (∑ B, (Excess - …))
    --       = (∑ B, ∑ t, contrib_from)      (← h2 の逆向き)
    --       = (∑ t, ∑ B, contrib_from)      (← hswap の逆向き)
    have h2' :
        (∑ B ∈ Rep ρ R,
           (Excess ρ R B
             - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
        = (∑ B ∈ Rep ρ R, ∑ t ∈ R, contrib_from ρ R t B) := by
      -- h2 の両辺を入れ替えた形
      -- h2 : ∑_B ∑_t = ∑_B RHS
      -- よって ∑_B RHS = ∑_B ∑_t
      exact Eq.symm h2
    -- 次に ∑_B ∑_t = ∑_t ∑_B を適用
    calc
      (∑ B ∈ Rep ρ R,
         (Excess ρ R B
           - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
          = (∑ B ∈ Rep ρ R, ∑ t ∈ R, contrib_from ρ R t B) := h2'
      _ = (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B) := by
            -- hswap の逆向き
            exact Eq.symm hswap
  -- 最後に h1 と hLHS_rewrite を突き合わせて不等式
  -- h1 : ∑_t ∑_B contrib ≤ ∑_t card
  -- よって LHS = ∑_t ∑_B contrib ≤ 右辺
  have :
      (∑ B ∈ Rep ρ R,
         (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
      ≤ (∑ t ∈ R, ((addedFamily ρ R t).card : ℤ)) := by
    -- hLHS_rewrite で左辺を書き換えて h1 を適用
    -- 左辺を書き換え
    have := h1
    -- 置換：左辺を hLHS_rewrite の右辺に一致させる
    -- （置換後にそのまま ≤ が得られる）
    -- Lean では rewrite を2段で実施
    --   1) 左辺を書き換え（Eq.mpr / Eq.mp でも可）
    --   2) その結果 h1 と同形になる
    -- ここでは変数に束ねた h1 をそのまま使うため `rw` を使います
    --   (等式変形のみで不等式の向きは変わりません)
    -- ただし `simpa` は使わない方針なので、`rw` で逐次置換します。
    -- まず hLHS_rewrite を使って左辺を ∑_t ∑_B に
    have rew :
        (∑ B ∈ Rep ρ R,
           (Excess ρ R B
             - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
        = (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B) := hLHS_rewrite
    -- 置換して h1 を適用
    --   形式的には、goal の左辺を rew の RHS に置換してから h1 を使う
    -- ここは `have` でまとめてから `exact` します
    -- 置換後の主張はちょうど h1 なので、そのまま h1 が使えます
    -- （Lean 的には `rw [rew]; exact h1`）
    -- ただし「simpa」禁止につき、分割して書きます。
    -- まず置換
    --   注意：`rw` はゴールに作用するので、この `have` ブロック内では
    --   新しいゴールを作らずに `calc` の連鎖で返します。
    -- ここでは最終的な不等式を `exact` で返します。
    have :
        (∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from ρ R t B)
        ≤ (∑ t ∈ R, ((addedFamily ρ R t).card : ℤ)) := h1
    -- 置換結果を戻す
    -- すなわち
    --   (左辺) = … ≤ … = (右辺)
    -- を `calc` で与えます。
    -- まず左辺を rew で右側へ
    exact
      (by
        -- calc で書いてもよいですが、ここはそのまま `rw`→`exact` で。
        -- `rw` はこの `by` ブロック内部のゴールにのみ作用します。
        -- ゴール：LHS ≤ RHS
        -- `rw [rew]` でゴールの LHS を ∑_t ∑_B に置換
        -- その後 `exact h1`
        -- 注意：この `by` ブロック内にはゴールが1本必要なので、
        --       ここでは `have` で既に欲しい不等式を持っているため、
        --       同形にするための置換を施します。
        -- 具体的には `exact` はゴール一致が必要なので、
        -- `have` を `calc` の形で返します。
        -- よって最上位の `exact` の引数として `this` を返す前に
        -- ゴールを `rew` で整形するのが簡潔です。
        -- Lean では `refine` + `?goal` でも同等。
        -- ここでは最小限の手数で：
        --   1) ゴールを書き換える
        --   2) `exact this`
        -- という順にします。
        -- 1)
        -- しかし `rw` はこの `by` の現行ゴールにしか効きません。
        -- そこで `have` を返す小ブロックに分けず、直接書きます。
        -- 具体：
        --   `rw [rew]; exact this`
        -- で完了です。
        -- （長コメントすみません。）
        rw [rew]
        exact this)
  -- できあがり
  exact this

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma sum_addedFamily_card_eq_sum_delta
  --(AF :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  (∑ t ∈ R, ((AF ρ R t).card : ℤ))
    = (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
  classical
  refine Finset.sum_congr rfl ?step
  intro t ht
  -- ((addedFamily ρ R t).card : ℤ) = ((Δ addedFamily ρ R t : ℕ) : ℤ)
  -- Δ の定義がそのまま card なので rfl
  rfl




omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 補題2：左辺 ≤ 右辺（card 版）をまるごと与えるラッパ
    ＝ 既にある `charging_sum_lower_bound_card` を呼ぶだけ -/
lemma charging_sum_LHS_le_sum_addedFamily_card
  --(addedFamily :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
  --(chargeTo :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
  (contrib_from :
    (ρ : RuleOrder α) → (R : Finset (Rule α)) → (t : Rule α) → (B : Finset α) → ℤ)
  (per_rule_lower_bound :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α),
      ∑ B ∈ Rep ρ R, contrib_from ρ R t B
        ≤ ((AF ρ R t).card : ℤ))
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R, contrib_from ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  (∑ B ∈ Rep ρ R,
     (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
    ≤ (∑ t ∈ R, ((AF ρ R t).card : ℤ)) := by
  -- 既存の「card 版」総和不等式をそのまま適用
    apply charging_sum_lower_bound_card
    exact fun ρ R t => per_rule_lower_bound ρ R t
    exact fun ρ R B a => hcore ρ R B a

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma charging_sum_lower_bound_delta
  --(addedFamily :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
  --(chargeTo :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
  (contrib_from :
    (ρ : RuleOrder α) → (R : Finset (Rule α)) → (t : Rule α) → (B : Finset α) → ℤ)
  (per_rule_lower_bound :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α),
      ∑ B ∈ Rep ρ R, contrib_from ρ R t B
        ≤ ((AF ρ R t).card : ℤ))
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R, contrib_from ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  (∑ B ∈ Rep ρ R,
     (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
  ≤ (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
  classical
  -- まず card 版（右辺が (addedFamily…).card の形）を使う
  have h_card :=
    charging_sum_lower_bound_card
      AF Rep Missing Excess Free contrib_from
      per_rule_lower_bound hcore ρ R
  -- 右辺を Δ で書き換え（各項が定義一致）
  /-
  have hrhs :
      (∑ t ∈ R, ((AF ρ R t).card : ℤ))
        = (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
    refine Finset.sum_congr rfl ?step
    intro t ht
    simp_all only [sum_sub_distrib, tsub_le_iff_right, Δ_def]
    -- ここが以前の hpoint。今は定義一致なので rfl でOK。
    -- ((addedFamily ρ R t).card : ℤ) = ((Δ ρ R t : ℕ) : ℤ)
    -- `@[simp] Δ_cast_def` でも消えますが、方針通り `rfl` で。
  -/

  -- (1) 右辺を Δ に書換える部分（hrhs の sorry を置換）
  have hrhs :
      (∑ t ∈ R, ((AF ρ R t).card : ℤ))
        = (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
    apply sum_addedFamily_card_eq_sum_delta (AF := AF)

  -- (2) calc の最初の ≤（h_card の sorry を置換）
  calc
    (∑ B ∈ Rep ρ R,
       (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
      ≤ (∑ t ∈ R, ((AF ρ R t).card : ℤ)) := by
        apply charging_sum_LHS_le_sum_addedFamily_card AF
        exact fun ρ R t => per_rule_lower_bound ρ R t
        exact fun ρ R B a => hcore ρ R B a

    _ = (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := hrhs

/-! ### Distribute the sum on the left: ∑ (Excess - k·Missing) = ∑Excess - k·∑Missing -/

omit [LinearOrder α] [DecidableEq (Rule α)] in
lemma sum_excess_sub_kmissing
  (ρ : RuleOrder α) (R : Finset (Rule α)) (k : ℤ) :
  (∑ B ∈ Rep ρ R, (Excess AF isWitness  ρ R B - k * Missing ρ R B))
  =
  (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
  - k * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
  classical
  -- sum of differences is difference of sums
  have hsub :
      (∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - k * Missing ρ R B))
      =
      (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
      -
      (∑ B ∈ Rep ρ R, k * Missing ρ R B) := by
         exact Finset.sum_sub_distrib (Excess AF isWitness ρ R) fun x => k * Missing ρ R x

  -- pull out k from the sum (左定数乗)
  have hmul :
      (∑ B ∈ Rep ρ R, k * Missing ρ R B)
      =
      k * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
        exact Eq.symm (mul_sum (Rep ρ R) (Missing ρ R) k)

  -- combine
  calc
    (∑ B ∈ Rep ρ R, (Excess AF isWitness ρ R B - k * Missing ρ R B))
        = (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
          - (∑ B ∈ Rep ρ R, k * Missing ρ R B) := hsub
    _   = (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
          - k * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
            rw [hmul]

--omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/- ### Final “expanded” Δ-version statement -/
lemma charging_sum_lower_bound_delta_expanded
  (ρ : RuleOrder α) (R : Finset (Rule α))
  --(chargeTo : RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
   (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R,
            contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B):
  (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ))
  ≥
  (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
  - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
  classical
  -- From Δ-version inequality
  have hΔ :
    (∑ B ∈ Rep ρ R,
       (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
    ≤ (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
    let cs := charging_sum_lower_bound_delta
      (AF:=AF) (Rep:=Rep) (Missing:=Missing)
      (Excess := fun ρ R B => ∑ t ∈ R, Excess_t AF isWitness ρ R t B) (Free:=Free)
      (contrib_from := fun ρ R t B => contrib_from AF (Rep:=Rep) (isWitness:=isWitness) ρ R t B)

    apply  cs
    exact fun ρ R t => per_rule_lower_bound AF isWitness Rep ρ R t
    exact fun ρ R B a => hcore ρ R B a



  -- Expand the LHS with the distribution lemma
  have hexpand :
    (∑ B ∈ Rep ρ R,
       (Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
    =
    (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
      let se := sum_excess_sub_kmissing (Rep:=Rep)
      apply se



  -- Rewrite LHS of hΔ and read inequality in ≥ form
  have :
    (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ))
    ≥
    (∑ B ∈ Rep ρ R, Excess AF isWitness ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
    have h := hΔ
    rw [hexpand] at h
    exact h
  exact this
-------------------
lemma chargeTo_eq_iff
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  {A B : Finset α} (hA : A ∈ AF ρ R t) :
  chargeTo (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t A = B
  ↔ (B ∈ Rep ρ R ∧ ∃ S, A = B ∪ S ∧ isWitness ρ R B S t) := by
  classical
  -- A が AF に入っているかで場合分け（左→右両方向が揃いやすい）
  by_cases h : A ∈ AF ρ R t
  ·
    -- Task A（一意存在）を取得
    have hexu :
      ∃! (B0 : Finset α),
        B0 ∈ Rep ρ R ∧ ∃ S, A = B0 ∪ S ∧ isWitness ρ R B0 S t :=
      exists_unique_base_for_added
        (AF:=AF) (Rep:=Rep) (isWitness:=isWitness)
        ρ R t (A:=A) h
    let B0 := Classical.choose (ExistsUnique.exists hexu)
    have hB0 :
      B0 ∈ Rep ρ R ∧ ∃ S, A = B0 ∪ S ∧ isWitness ρ R B0 S t :=
      Classical.choose_spec (ExistsUnique.exists hexu)
    -- AFケースでは chargeTo は B0 を返す
    have hcharge : chargeTo (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t A = B0 := by
      simp [chargeTo, h, B0]
    constructor
    · -- → 方向
      intro hEq
      -- hcharge : ct = B0, hEq : ct = B から B0 = B
      have hEq' : B0 = B := by simp_all only [B0]
      rcases hB0 with ⟨hRep0, ⟨S0, hAs0, hW0⟩⟩
      -- 等式で性質を輸送
      have hRep : B ∈ Rep ρ R := by
        -- B0 = B を使って書き換え
        simpa [hEq'] using hRep0
      have hAsB : A = B ∪ S0 := by
        simpa [hEq'] using hAs0
      have hWB  : isWitness ρ R B S0 t := by
        simpa [hEq'] using hW0
      exact And.intro hRep ⟨S0, And.intro hAsB hWB⟩
    · -- ← 方向
      intro hCond
      -- 一意性から B = B0
      obtain ⟨hRep, ⟨S₁, hAs1, hW1⟩⟩ := hCond
      obtain ⟨hRep0, ⟨S0, hAs0, hW0⟩⟩ := hB0
      have huniq : B = B0 := by
        let wb := witness_base_unique  (ρ:=ρ) (R:=R) (t:=t) (A:=A) (isWitness:=isWitness)
        apply wb B S₁ B0 S0
        exact hAs1
        exact hAs0
        exact hW1
        exact hW0

      -- chargeTo = B0 を右辺書き換えで chargeTo = B にする
      exact hcharge.trans (Eq.symm huniq)
  ·
    -- こちらは仮定 hA と矛盾（到達不能）
    constructor
    · intro _; exact (h hA).elim
    · intro _; exact (h hA).elim


omit [LinearOrder α] [DecidableEq (Rule α)] in
/-- 展開用の simp 補題（必要なら） -/
@[simp] lemma chargeCount_def
  --(AF :
  --  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  --(isWitness :
  --  RuleOrder α → Finset (Rule α) → Finset α → Finset α → Rule α → Prop)
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α)
  [DecidablePred (fun A : Finset α => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)] :
  chargeCount AF isWitness ρ R B t
  =
  (((AF ρ R t).filter
     (fun A => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)).card : ℤ) := by
  classical
  simp [chargeCount]
  congr

omit [LinearOrder α] [DecidableEq (Rule α)] in
lemma charging_local_with_specs
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α)
  (hEx : Excess_t AF Witness ρ R t B =
          chargeCount AF (isWitness:=isWitness) ρ R B t)
  (hMi : Missing_t ρ R t B = 0) :
  chargeCount (AF:=AF) (isWitness:=isWitness) ρ R B t
    - (Finset.card (Free ρ R) : ℤ) * 0
  =
  Excess_t AF Witness ρ R t B
    - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
  classical
  -- 右辺を仕様で置換
  -- simpa using は使わず、rw で明示的に変形
  rw [hEx, hMi, mul_zero]

omit [LinearOrder α] [DecidableEq (Rule α)] in
/-- 【lemma（仮）】Charging の局所恒等式（t毎） -/
lemma charging_local_lem {AF : RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α)}
  {isWitness : RuleOrder α → Finset (Rule α) → Finset α → Finset α → Rule α → Prop}
  --{Rep : RuleOrder α → Finset (Rule α) → Finset (Finset α)}
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α):
  --(hB : B ∈ Rep ρ R) :
  chargeCount AF isWitness ρ R B t
  =
  Excess_t AF isWitness ρ R t B
    - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
  classical
  -- 定義を展開

  --unfold Excess_t Missing_t
  -- 右辺は `chargeCount - (|Free| : ℤ) * 0`
  -- `a = a - (k*0)` を素直に作る
  have hmul : (Finset.card (Free ρ R) : ℤ) * 0 = (0 : ℤ) := by
    exact mul_zero _
  calc
    chargeCount AF isWitness ρ R B t
        =
      chargeCount AF (isWitness:=isWitness) ρ R B t - 0 := by
        exact (sub_zero _).symm
    _ =
      chargeCount AF (isWitness:=isWitness) ρ R  B t
      - (Finset.card (Free ρ R) : ℤ) * 0 := by
        -- 右の引き算の第二項を `0` から `(k*0)` に置換
        exact congrArg
          (fun z => chargeCount AF (isWitness:=isWitness)  ρ R B t - z)
          hmul.symm
    _ =
      chargeCount AF (isWitness:=isWitness)  ρ R B t
      - (Finset.card (Free ρ R) : ℤ) * 0 := rfl
    _ =
      Excess_t AF isWitness ρ R t B - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
        apply charging_local_with_specs (AF:=AF) (isWitness:=isWitness) (ρ:=ρ) (R:=R) (B:=B) (t:=t) Free
        dsimp [Excess_t, Missing_t]
        exact hmul

omit [LinearOrder α] [DecidableEq (Rule α)] in
lemma charging_local_lem_no_unfold
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α)
 :
  chargeCount AF isWitness ρ R B t
  =
  Excess_t  AF isWitness ρ R t B
  - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
  classical
  -- 速攻ルートが与える「仕様（等式）」を、定義を開かずローカル事実として用意
  have hEx : Excess_t  AF isWitness ρ R t B
            = chargeCount AF isWitness ρ R B t := rfl   -- 定義通り
  have hMi : Missing_t ρ R t B = 0 := rfl               -- 定義通り

  -- 目標を `a = a - k*0` 型に整形
  calc
    chargeCount AF isWitness ρ R B t
        = chargeCount AF isWitness ρ R B t - 0 := (sub_zero _).symm
    _ = chargeCount AF isWitness ρ R B t - (Finset.card (Free ρ R) : ℤ) * 0 := by
          -- 右の 0 を (k*0) に置換
          exact congrArg
            (fun z => chargeCount AF isWitness ρ R B t - z)
            (mul_zero (Finset.card (Free ρ R) : ℤ)).symm
    _ = (Excess_t AF isWitness ρ R t B) - (Finset.card (Free ρ R) : ℤ) * 0 := by
          -- 左項を hEx で置換（congrArg で第1引数側）
          exact congrArg
            (fun z => z - (Finset.card (Free ρ R) : ℤ) * 0)
            hEx.symm
    _ = (Excess_t AF isWitness ρ R t B)
        - (Finset.card (Free ρ R) : ℤ) * (Missing_t ρ R t B) := by
          -- 右の 0 を hMi で Missing_t に置換（congrArg で第2引数側）
          exact congrArg
            (fun z => Excess_t AF isWitness ρ R t B
                      - (Finset.card (Free ρ R) : ℤ) * z)
            hMi.symm

/-
lemma charging_local_lem {AF : RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α)}
  {isWitness : RuleOrder α → Finset (Rule α) → Finset α → Finset α → Rule α → Prop}
  {Rep : RuleOrder α → Finset (Rule α) → Finset (Finset α)}
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α)
  (hB : B ∈ Rep ρ R) :
  chargeCount AF isWitness ρ R B t
  =
  Excess_t ρ R t B
    - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
  sorry
-/

omit [LinearOrder α] [DecidableEq (Rule α)] in
/-- 【lemma（仮）】Excess の t-総和分解 -/
lemma Excess_sum_lem
  --(Excess : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  Excess AF isWitness ρ R B = ∑ t ∈ R, Excess_t AF isWitness ρ R t B := by
  dsimp [Excess_t ]
  dsimp [chargeCount]
  dsimp [Excess]
  rfl

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 【lemma（仮）】Missing の t-総和分解 -/
lemma Missing_sum_lem
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  Missing ρ R B = ∑ t ∈ R, Missing_t ρ R t B := by
  dsimp [Missing_t]
  dsimp [Missing]
  rfl

omit [LinearOrder α] [DecidableEq (Rule α)] in
/- ── まずは「仮定として受ける汎用版」 ── -/
lemma chargingIdentity_core_with
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  --(hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t AF isWitness ρ R t B
           - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)
  (Excess_sum :
    Excess AF isWitness ρ R B = ∑ t ∈ R, Excess_t AF isWitness ρ R t B)
  (Missing_sum :
    Missing ρ R B = ∑ t ∈ R, Missing_t ρ R t B) :
  (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
  =
  Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  classical
  have hStep :
    (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
    =
    (∑ t ∈ R,
      (Excess_t AF isWitness ρ R t B
        - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact charging_local t
  have hSplit :
    (∑ t ∈ R,
      (Excess_t AF isWitness ρ R t B
        - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B))
    =
    (∑ t ∈ R, Excess_t AF isWitness ρ R t B)
      -
    (∑ t ∈ R,
      (Finset.card (Free ρ R) : ℤ) * Missing_t  ρ R t B) := by
    exact sum_sub_distrib (fun x => Excess_t AF isWitness ρ R x B) fun x => ↑(#(Free ρ R)) * Missing_t ρ R x B
  have hPull :
    (∑ t ∈ R,
      (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)
    =
    (Finset.card (Free ρ R) : ℤ) * (∑ t ∈ R, Missing_t ρ R t B) := by
    simpa using
      (Finset.mul_sum (Finset.card (Free ρ R) : ℤ)
        (s := R) (f := fun t => Missing_t ρ R t B)).symm
  have hE := Excess_sum
  have hM := Missing_sum
  calc
    (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
        = (∑ t ∈ R,
            (Excess_t AF isWitness ρ R t B
              - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
              exact hStep
    _ = (∑ t ∈ R, Excess_t AF isWitness ρ R t B)
          -
        ((∑ t ∈ R,
          (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
              exact hSplit
    _ = (∑ t ∈ R, Excess_t AF isWitness ρ R t B)
          -
        ((Finset.card (Free ρ R) : ℤ)
            * (∑ t ∈ R, Missing_t  ρ R t B)) := by
              apply congrArg (fun z => (∑ t ∈ R, Excess_t AF isWitness ρ R t B) - z)
              exact hPull
    _ = Excess AF isWitness ρ R B
          -
        ((Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
              have hE' :
                (∑ t ∈ R, Excess_t AF isWitness ρ R t B) = Excess AF isWitness ρ R B := hE.symm
              have hM' :
                (∑ t ∈ R, Missing_t ρ R t B) = Missing ρ R B := hM.symm
              have := congrArg
                (fun z => z - (Finset.card (Free ρ R) : ℤ)
                               * (∑ t ∈ R, Missing_t ρ R t B)) hE'
              -- `Missing` の置換を最後に
              simpa [hM'] using this

omit [LinearOrder α] [DecidableEq (Rule α)] in
/- ── 次に「lemma をそのまま渡すラッパ（便利版）」 ── -/
lemma chargingIdentity_core
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  --(hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t AF isWitness ρ R t B
           - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B):
  (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
  =
  Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  classical
  have hloc :
  ∀ t, chargeCount AF isWitness ρ R B t
       = Excess_t AF isWitness ρ R t B
         - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
    exact fun t => charging_local t


  let hE := Excess_sum_lem AF isWitness --ρ R B
  let hM := Missing_sum_lem ρ R B
  exact chargingIdentity_core_with AF isWitness  Free ρ R charging_local (hE ρ R B) hM

  -- lemma（仮）を関数にして渡す

omit [LinearOrder α] [DecidableEq (Rule α)] in
/-- ▲ 元の「filter で書いた形」へのラッパ。
    各 t で `DecidablePred` を立てて `chargeCount_def` に展開する。 -/
lemma chargingIdentity_core_filter
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  --(hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t AF isWitness ρ R t B
           - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)
  [DecidablePred (fun A : Finset α => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)] :
  (∑ t ∈ R,
      (by
        classical
        -- ★ 各 t ごとに述語の decidability を用意
        haveI :
          DecidablePred (fun A : Finset α =>
            ∃ S, A = B ∪ S ∧ isWitness ρ R B S t) :=
          (fun _ => Classical.propDecidable _)

        let aff := ((AF ρ R t).filter (fun A => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t))
        exact (aff.card : ℤ)
  ))
  =
  Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  classical
  -- 左辺を chargeCount に書き換える
  have hL :
    (∑ t ∈ R,
      (by
        classical
        haveI :
          DecidablePred (fun A : Finset α =>
            ∃ S, A = B ∪ S ∧ isWitness ρ R B S t) :=
          (fun _ => Classical.propDecidable _)
        exact
          (((AF ρ R t).filter
            (fun A => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)).card : ℤ)))
    =
    (∑ t ∈ R, chargeCount AF isWitness ρ R B t) := by
    apply Finset.sum_congr rfl
    intro t ht
    -- ここでも各 t 用のインスタンスを立ててから `chargeCount_def` で展開
    haveI :
      DecidablePred (fun A : Finset α =>
        ∃ S, A = B ∪ S ∧ isWitness ρ R B S t) :=
      (fun _ => Classical.propDecidable _)
    simp
    simp_all only [chargeCount_def]
    congr
  -- `chargeCount` 版の核恒等式を呼ぶ

  -- 連結
  calc
    (∑ t ∈ R,
      (by
        classical
        haveI :
          DecidablePred (fun A : Finset α =>
            ∃ S, A = B ∪ S ∧ isWitness ρ R B S t) :=
          (fun _ => Classical.propDecidable _)
        exact
          (((AF ρ R t).filter
            (fun A => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)).card : ℤ)))
        = (∑ t ∈ R, chargeCount AF isWitness ρ R B t) := by
          exact hL
    _ = Excess AF isWitness ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
        exact
          chargingIdentity_core AF isWitness Free ρ R
            charging_local
