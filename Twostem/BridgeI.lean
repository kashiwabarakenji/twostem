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

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α][DecidableEq (Rule α)]

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

variable (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
variable (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Free    : RuleOrder α → Finset (Rule α) → Finset α)

/-! ## Charging の骨組み（このスレで定義・証明していく） -/

variable (isWitness :
  RuleOrder α → Finset (Rule α) → Finset α → Finset α → Rule α → Prop)
--別ファイルで証明するかも。
lemma AF_witness_exists
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) {A : Finset α}
  (hA : A ∈ AF ρ R t) :
  ∃ (B S : Finset α), A = B ∪ S ∧ isWitness ρ R B S t := by
  sorry

-- 同じ A の分解に対する基底の一意性
lemma witness_base_unique
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (A B₁ S₁ B₂ S₂ : Finset α)
  (h1 : A = B₁ ∪ S₁) (h2 : A = B₂ ∪ S₂)
  (w1 : isWitness ρ R B₁ S₁ t) (w2 : isWitness ρ R B₂ S₂ t) :
  B₁ = B₂ := by
  sorry

-- Witness の基底は代表系に属する
lemma witness_base_in_Rep
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (B S : Finset α) (w : isWitness ρ R B S t) :
  B ∈ Rep ρ R := by
  sorry

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
  {A : Finset α} (hA : A ∈ AF ρ R t)
 :
  ∃! (B : Finset α),
    B ∈ Rep ρ R ∧ ∃ S, A = B ∪ S ∧ isWitness ρ R B S t := by
  classical

  obtain ⟨B, S, hAs, hW⟩ := AF_witness_exists
    (AF:=AF) (isWitness:=isWitness)
    (ρ:=ρ) (R:=R) (t:=t) (A:=A)
    hA
    --AF_witness_exists (ρ:=ρ) (R:=R) (t:=t) (A:=A) hA
  -- 2) その基底 B は代表系に属する
  have hBmem : B ∈ Rep ρ R :=
    witness_base_in_Rep (Rep:=Rep) (isWitness:=isWitness) ρ R t B S hW
  -- 3) 存在と一意性で ∃! を構成
  refine ExistsUnique.intro B ?hex ?uniq
  · -- 存在部
    exact And.intro hBmem ⟨S, And.intro hAs hW⟩
  · -- 一意性：条件を満たす任意の B' は B に等しい
    intro B' hB'
    rcases hB' with ⟨_hB'in, ⟨S', hAs', hW'⟩⟩
    exact witness_base_unique (isWitness:=isWitness) ρ R t A B' S' B S hAs' hAs hW' hW


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
  chargeTo AF Rep isWitness ρ R t A
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


--omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/- すべての規則で合計した寄与を、Barrier の右辺に整理 -/
lemma sum_over_rules_reshuffle
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ∑ B ∈ Rep ρ R,
      contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
    = ∑ B ∈ Rep ρ R,
        (Excess ρ R B
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
          (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    refine Finset.sum_congr rfl ?_ ; intro B hB
    -- 右辺の各項に chargingIdentity
    have h := chargingIdentity B hB
    -- 書き換え
    exact h
  -- まとめ
  exact Eq.trans hswap happly

/- **Bridge II（addedFamily 版）**：総和の下界 -/
lemma addedFamily_sum_lower_bound
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ((AF ρ R t).card : ℤ))
    ≥ ∑ B ∈ Rep ρ R, Excess ρ R B
      - (Finset.card (Free ρ R) : ℤ) * ∑ B ∈ Rep ρ R, Missing ρ R B := by
  classical
  -- 1) 左辺 ≥ ∑_{t∈R} ∑_{B∈Rep} contrib_from …
  have h1 :
    (∑ t ∈ R, ((AF ρ R t).card : ℤ))
      ≥ ∑ t ∈ R, ∑ B ∈ Rep ρ R,
            contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B := by
    -- 各 t ごとに per_rule_lower_bound を足し合わせる（Finset.sum_le_sum）
    refine Finset.sum_le_sum ?_ ; intro t ht
    exact per_rule_lower_bound AF Rep isWitness ρ R t

  -- 2) 右辺の二重和を Barrier 右辺に並べ替え
  have h2 :
    (∑ t ∈ R, ∑ B ∈ Rep ρ R,
        contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
      = ∑ B ∈ Rep ρ R,
          (Excess ρ R B
            - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    apply sum_over_rules_reshuffle
    exact fun B a => chargingIdentity B a

  --    ∑ addedFamily.card ≥ (二重和) = (Barrier RHS)
  --    最後に `∑ (Excess - c*Missing)` を `∑ Excess - c*∑ Missing` に分配
  set c : ℤ := (Finset.card (Free ρ R) : ℤ) with hc
  have hdist :
    (∑ B ∈ Rep ρ R, (Excess ρ R B - c * Missing ρ R B))
      = (∑ B ∈ Rep ρ R, Excess ρ R B)
        - (∑ B ∈ Rep ρ R, c * Missing ρ R B) := by
    -- Finset.sum_sub_distrib の直接適用
    exact sum_sub_distrib (Excess ρ R) fun x => c * Missing ρ R x

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
          (Excess ρ R B - c * Missing ρ R B) := by

          calc
            ∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness)  ρ R t B
                = ∑ B ∈ Rep ρ R, (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := h2
            _ = ∑ B ∈ Rep ρ R, (Excess ρ R B - c * Missing ρ R B) := by
                  apply congrArg (fun z => ∑ B ∈ Rep ρ R, (Excess ρ R B - z * Missing ρ R B))
                  exact hc

    _ = (∑ B ∈ Rep ρ R, Excess ρ R B)
          - (∑ B ∈ Rep ρ R, c * Missing ρ R B) := by
          exact hdist
    _ = (∑ B ∈ Rep ρ R, Excess ρ R B)
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
            refine congrArg (fun z => (∑ B ∈ Rep ρ R, Excess ρ R B) - z) this


lemma chargeTo_mem_Rep_lemma

  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α} {A : Finset α}
  (hA : A ∈ AF ρ R t) :
  chargeTo (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t A ∈ Rep ρ R := by
  exact chargeTo_mem_Rep AF Rep isWitness ρ R hA

lemma chargingIdentity
  (ρ : RuleOrder α) (R : Finset (Rule α))
  {B : Finset α} (hB : B ∈ Rep ρ R)
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R,
            contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) :
  (∑ t ∈ R, contrib_from (AF:=AF) (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
    = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  exact hcore ρ R B hB

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- **全体版：Barrier/Charging の合算不等式**
    核等式（hcore）と `per_rule_lower_bound` を組み合わせて、
    \sum_B (Excess(B) - |Free|·Missing(B)) ≤ \sum_t |addedFamily ρ R t|.
    ここでは Δ ではなく card で述べ、その後に Δ 版コローラリを出します。 -/
--addedFamilyの仮定を除くべきかも。そして、AFを使う。
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
             (Excess ρ R B
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

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma sum_excess_sub_kmissing
  (ρ : RuleOrder α) (R : Finset (Rule α)) (k : ℤ) :
  (∑ B ∈ Rep ρ R, (Excess ρ R B - k * Missing ρ R B))
  =
  (∑ B ∈ Rep ρ R, Excess ρ R B)
  - k * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
  classical
  -- sum of differences is difference of sums
  have hsub :
      (∑ B ∈ Rep ρ R, (Excess ρ R B - k * Missing ρ R B))
      =
      (∑ B ∈ Rep ρ R, Excess ρ R B)
      -
      (∑ B ∈ Rep ρ R, k * Missing ρ R B) := by
         exact Finset.sum_sub_distrib (Excess ρ R) fun x => k * Missing ρ R x

  -- pull out k from the sum (左定数乗)
  have hmul :
      (∑ B ∈ Rep ρ R, k * Missing ρ R B)
      =
      k * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
        exact Eq.symm (mul_sum (Rep ρ R) (Missing ρ R) k)

  -- combine
  calc
    (∑ B ∈ Rep ρ R, (Excess ρ R B - k * Missing ρ R B))
        = (∑ B ∈ Rep ρ R, Excess ρ R B)
          - (∑ B ∈ Rep ρ R, k * Missing ρ R B) := hsub
    _   = (∑ B ∈ Rep ρ R, Excess ρ R B)
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
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B):
  (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ))
  ≥
  (∑ B ∈ Rep ρ R, Excess ρ R B)
  - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
  classical
  -- From Δ-version inequality
  have hΔ :
    (∑ B ∈ Rep ρ R,
       (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
    ≤ (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ)) := by
    let cs := charging_sum_lower_bound_delta
      (AF:=AF) (Rep:=Rep) (Missing:=Missing)
      (Excess:=Excess) (Free:=Free)
      (contrib_from := fun ρ R t B => contrib_from AF (Rep:=Rep) (isWitness:=isWitness) ρ R t B)
    refine cs ?_ ?_ ?_ ?_
    exact fun ρ R t => per_rule_lower_bound AF Rep isWitness ρ R t
    exact fun ρ R B a => hcore ρ R B a


  -- Expand the LHS with the distribution lemma
  have hexpand :
    (∑ B ∈ Rep ρ R,
       (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
    =
    (∑ B ∈ Rep ρ R, Excess ρ R B)
    - (Finset.card (Free ρ R) : ℤ) * (∑ B ∈ Rep ρ R, Missing ρ R B) := by
      let se := sum_excess_sub_kmissing (Rep:=Rep) (Missing:=Missing) (Excess:=Excess)
      exact se ρ R ↑(#(Free ρ R))

  -- Rewrite LHS of hΔ and read inequality in ≥ form
  have :
    (∑ t ∈ R, ((Δ AF ρ R t : ℕ) : ℤ))
    ≥
    (∑ B ∈ Rep ρ R, Excess ρ R B)
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

/- 各規則 t に対する「Witness で数えた個数」の局所恒等式で使う局所寄与 -/
variable (Excess_t : RuleOrder α → Finset (Rule α) → Rule α → Finset α → ℤ)
variable (Missing_t : RuleOrder α → Finset (Rule α) → Rule α → Finset α → ℤ)

/-- Witness で (t,A) が B に課金される A の個数（ℤ に持ち上げ） -/
noncomputable def chargeCount
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) (t : Rule α) : ℤ := by
  classical
  exact ↑(#({A ∈ AF ρ R t | ∃ S, A = B ∪ S ∧ isWitness ρ R B S t}))


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

/-- 【lemma（仮）】Charging の局所恒等式（t毎） -/
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

/-- 【lemma（仮）】Excess の t-総和分解 -/
lemma Excess_sum_lem
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  Excess ρ R B = ∑ t ∈ R, Excess_t ρ R t B := by
  sorry

/-- 【lemma（仮）】Missing の t-総和分解 -/
lemma Missing_sum_lem
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  Missing ρ R B = ∑ t ∈ R, Missing_t ρ R t B := by
  sorry

/-! ── まずは「仮定として受ける汎用版」 ── -/
lemma chargingIdentity_core_with
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  (hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t ρ R t B
           - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)
  (Excess_sum :
    Excess ρ R B = ∑ t ∈ R, Excess_t ρ R t B)
  (Missing_sum :
    Missing ρ R B = ∑ t ∈ R, Missing_t ρ R t B) :
  (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
  =
  Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  classical
  have hStep :
    (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
    =
    (∑ t ∈ R,
      (Excess_t ρ R t B
        - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact charging_local t
  have hSplit :
    (∑ t ∈ R,
      (Excess_t ρ R t B
        - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B))
    =
    (∑ t ∈ R, Excess_t ρ R t B)
      -
    (∑ t ∈ R,
      (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B) := by
    exact sum_sub_distrib (fun x => Excess_t ρ R x B) fun x => ↑(#(Free ρ R)) * Missing_t ρ R x B
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
            (Excess_t ρ R t B
              - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
              exact hStep
    _ = (∑ t ∈ R, Excess_t ρ R t B)
          -
        ((∑ t ∈ R,
          (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B)) := by
              exact hSplit
    _ = (∑ t ∈ R, Excess_t ρ R t B)
          -
        ((Finset.card (Free ρ R) : ℤ)
            * (∑ t ∈ R, Missing_t ρ R t B)) := by
              apply congrArg (fun z => (∑ t ∈ R, Excess_t ρ R t B) - z)
              exact hPull
    _ = Excess ρ R B
          -
        ((Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
              have hE' :
                (∑ t ∈ R, Excess_t ρ R t B) = Excess ρ R B := hE.symm
              have hM' :
                (∑ t ∈ R, Missing_t ρ R t B) = Missing ρ R B := hM.symm
              have := congrArg
                (fun z => z - (Finset.card (Free ρ R) : ℤ)
                               * (∑ t ∈ R, Missing_t ρ R t B)) hE'
              -- `Missing` の置換を最後に
              simpa [hM'] using this

/- ── 次に「lemma をそのまま渡すラッパ（便利版）」 ── -/
lemma chargingIdentity_core
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  (hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t ρ R t B
           - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B):
  (∑ t ∈ R, chargeCount AF isWitness ρ R B t)
  =
  Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  classical
  have hloc :
  ∀ t, chargeCount AF isWitness ρ R B t
       = Excess_t ρ R t B
         - (Finset.card (Free ρ R) : ℤ) * Missing_t ρ R t B := by
    exact fun t => charging_local t


  let hE := Excess_sum_lem   (Excess:=Excess) (Excess_t:=Excess_t)  ρ R B
  let hM := Missing_sum_lem (Missing:=Missing) (Missing_t:=Missing_t) ρ R B
  exact chargingIdentity_core_with
    (AF:=AF) (Rep:=Rep) (isWitness:=isWitness)
    (Free:=Free) (Excess:=Excess) (Missing:=Missing)
    (Excess_t:=Excess_t) (Missing_t:=Missing_t)
    ρ R (B:=B) hB hloc hE hM
  -- lemma（仮）を関数にして渡す


/-- ▲ 元の「filter で書いた形」へのラッパ。
    各 t で `DecidablePred` を立てて `chargeCount_def` に展開する。 -/
lemma chargingIdentity_core_filter
  (ρ : RuleOrder α) (R : Finset (Rule α)) {B : Finset α}
  (hB : B ∈ Rep ρ R)
  (charging_local :
    ∀ t, chargeCount AF isWitness ρ R B t
         = Excess_t ρ R t B
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
        exact
          (((AF ρ R t).filter
            (fun A => ∃ S, A = B ∪ S ∧ isWitness ρ R B S t)).card : ℤ)))
  =
  Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
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
    _ = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
        exact
          chargingIdentity_core AF Rep Missing Excess Free isWitness Excess_t Missing_t ρ R hB
            charging_local
