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

@[simp] lemma Δ_def
  (AF :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) :
  Δ AF ρ R t = (AF ρ R t).card := rfl

/-- このセクション内では `Δ ρ R t` と短く書けるようにする -/
local notation "Δ" => Δ AF

/- 点wise 版（左 = 右 なので ≤ が成り立つ） -/
omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma addedFamily_card_le_delta
  [DecidableEq α] [DecidableEq (Rule α)] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  ∀ ⦃t : Rule α⦄, t ∈ R → #(AF ρ R t) ≤ Δ ρ R t := by
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
  ∑ t ∈ R, #(AF ρ R t) ≤ ∑ t ∈ R, Δ ρ R t := by
  classical
  refine Finset.sum_le_sum ?termwise
  intro t ht
  exact addedFamily_card_le_delta (AF := AF) ρ R ht

--********** Bridge I 本体：総和版 **********
/- 代表系・欠損・超過・自由点（論文の Barrier/Charging 側の量） -/
variable (myAddedFamily :
  RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
variable (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
variable (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
variable (Free    : RuleOrder α → Finset (Rule α) → Finset α)

/-! ## Charging の骨組み（このスレで定義・証明していく） -/

/- (t, A) の請求先 B を与える写像（`Rep ρ R` の元になる） -/
variable (chargeTo : RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)

/- chargeTo の値は代表系に属する（仮定として受け取る） -/
variable (chargeTo_mem_Rep :
  ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α),
    A ∈ AF ρ R t → chargeTo ρ R t A ∈ Rep ρ R )

/-- B が t から受け取る寄与（ℤ）：(t の addedFamily のうち B に課金された個数) -/
noncomputable def contrib_from
  (AF : RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (chargeTo : RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (t : Rule α) (B : Finset α) : ℤ := by
  classical
  -- {A ∈ AF ρ R t | chargeTo ρ R t A = B}.card を ℤ に持ち上げ
  exact (((AF ρ R t).filter (fun A => chargeTo ρ R t A = B)).card : ℤ)

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 単一の規則 t についての局所的下界 -/
lemma per_rule_lower_bound
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) :
  ∑ B ∈ Rep ρ R, contrib_from (AF := AF) (chargeTo := chargeTo) ρ R t B
    ≤ ((AF ρ R t).card : ℤ) := by
  -- ここから証明contrib_from ρ R t B := by
  -- TODO: 各 A をちょうど 1 回どこかの B へ課金する（重複なし）
  classical
  -- 記号整理
  set S := AF ρ R t
  set P := Rep ρ R
  -- B ごとのファイバー
  let T : Finset α → Finset (Finset α) :=
    fun B => S.filter (fun A => chargeTo ρ R t A = B)
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
  have hR : ∑ B ∈ P, contrib_from (AF := AF) (chargeTo := chargeTo) ρ R t B
              = ((∑ B ∈ P, (T B).card) : ℤ) := by
    -- 各項ごとに `contrib_from` の定義を展開
    refine Finset.sum_congr rfl ?_ ; intro B hB
    simp [contrib_from, S, T]
  -- したがって ∑ contrib ≤ |S|
  have hRle : ∑ B ∈ P, contrib_from (AF := AF) (chargeTo := chargeTo) ρ R t B
                ≤ (S.card : ℤ) := by
    -- `calc` で等式→不等式
    calc
      ∑ B ∈ P, contrib_from (AF := AF) (chargeTo := chargeTo) ρ R t B
          = ((∑ B ∈ P, (T B).card) : ℤ) := hR
      _ ≤ (S.card : ℤ) := hInt
  -- 目標形に並べ替えて終了
  -- 目標は (|S|:ℤ) ≥ ∑ contrib
  exact hRle


omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- すべての規則で合計した寄与を、Barrier の右辺に整理 -/
lemma sum_over_rules_reshuffle
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
          = (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ∑ B ∈ Rep ρ R,
      contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
    = ∑ B ∈ Rep ρ R,
        (Excess ρ R B
          - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
  classical
  -- ∑t∑B … = ∑B∑t … （和の順序入替え）
  have hswap :
    (∑ t ∈ R, ∑ B ∈ Rep ρ R,
        contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
      = ∑ B ∈ Rep ρ R, ∑ t ∈ R,
          contrib_from (AF:=AF  ) (chargeTo:=chargeTo) ρ R t B := by
    -- 標準補題 `Finset.sum_comm`
    exact Finset.sum_comm
  -- 各 B ごとに chargingIdentity を適用
  have happly :
    (∑ B ∈ Rep ρ R, ∑ t ∈ R,
        contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
      = ∑ B ∈ Rep ρ R,
          (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    refine Finset.sum_congr rfl ?_ ; intro B hB
    -- 右辺の各項に chargingIdentity
    have h := chargingIdentity B hB
    -- 書き換え
    exact h
  -- まとめ
  exact Eq.trans hswap happly

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- **Bridge II（addedFamily 版）**：総和の下界 -/
lemma addedFamily_sum_lower_bound
  [DecidableEq α] [Fintype α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (chargingIdentity : ∀ B ∈ Rep ρ R,
        (∑ t ∈ R, contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
          = (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B)) :
  (∑ t ∈ R, ((AF ρ R t).card : ℤ))
    ≥ ∑ B ∈ Rep ρ R, Excess ρ R B
      - (Finset.card (Free ρ R) : ℤ) * ∑ B ∈ Rep ρ R, Missing ρ R B := by
  classical
  -- 1) 左辺 ≥ ∑_{t∈R} ∑_{B∈Rep} contrib_from …
  have h1 :
    (∑ t ∈ R, ((AF ρ R t).card : ℤ))
      ≥ ∑ t ∈ R, ∑ B ∈ Rep ρ R,
            contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B := by
    -- 各 t ごとに per_rule_lower_bound を足し合わせる（Finset.sum_le_sum）
    refine Finset.sum_le_sum ?_ ; intro t ht
    exact per_rule_lower_bound (AF:=AF) (chargeTo:=chargeTo) (Rep:=Rep)
      (ρ:=ρ) (R:=R) (t:=t)
  -- 2) 右辺の二重和を Barrier 右辺に並べ替え
  have h2 :
    (∑ t ∈ R, ∑ B ∈ Rep ρ R,
        contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
      = ∑ B ∈ Rep ρ R,
          (Excess ρ R B
            - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) := by
    exact sum_over_rules_reshuffle (AF:=AF) (chargeTo:=chargeTo) (Rep:=Rep)
      (Excess:=Excess) (Free:=Free) (ρ:=ρ) (R:=R) (chargingIdentity:=chargingIdentity)
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
              contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B) := h1
    _ = ∑ B ∈ Rep ρ R,
          (Excess ρ R B - c * Missing ρ R B) := by
          -- h2 をそのまま適用
          --have hc : (Finset.card (Free ρ R) : ℤ) = c := by search_proof
          calc
            ∑ t ∈ R, ∑ B ∈ Rep ρ R, contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B
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
  (addedFamily :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (chargeTo : RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
  (chargeTo_mem_Rep :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) (A : Finset α),
      A ∈ addedFamily ρ R t → chargeTo ρ R t A ∈ Rep ρ R)
  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α} {A : Finset α}
  (hA : A ∈ addedFamily ρ R t) :
  chargeTo ρ R t A ∈ Rep ρ R := by
  exact chargeTo_mem_Rep ρ R t A hA

lemma chargingIdentity
  (ρ : RuleOrder α) (R : Finset (Rule α))
  {B : Finset α} (hB : B ∈ Rep ρ R)
  (hcore :
    ∀ (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α),
      B ∈ Rep ρ R →
        (∑ t ∈ R,
            contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
          = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B) :
  (∑ t ∈ R, contrib_from (AF:=AF) (chargeTo:=chargeTo) ρ R t B)
    = Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B := by
  exact hcore ρ R B hB

/-- **全体版：Barrier/Charging の合算不等式**
    核等式（hcore）と `per_rule_lower_bound` を組み合わせて、
    \sum_B (Excess(B) - |Free|·Missing(B)) ≤ \sum_t |addedFamily ρ R t|.
    ここでは Δ ではなく card で述べ、その後に Δ 版コローラリを出します。 -/
lemma charging_sum_lower_bound_card
  (addedFamily :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
  (chargeTo :
    RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
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

/-- 補題1：右辺の「card 版」から「Δ 版」への項別書換え -/
lemma sum_addedFamily_card_eq_sum_delta
  (AF :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  (∑ t ∈ R, ((AF ρ R t).card : ℤ))
    = (∑ t ∈ R, ((Δ ρ R t : ℕ) : ℤ)) := by
  classical
  refine Finset.sum_congr rfl ?step
  intro t ht
  -- ((addedFamily ρ R t).card : ℤ) = ((Δ addedFamily ρ R t : ℕ) : ℤ)
  -- Δ の定義がそのまま card なので rfl
  sorry

/-- 補題2：左辺 ≤ 右辺（card 版）をまるごと与えるラッパ
    ＝ 既にある `charging_sum_lower_bound_card` を呼ぶだけ -/
lemma charging_sum_LHS_le_sum_addedFamily_card
  (addedFamily :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
  (chargeTo :
    RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
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
    exact fun a a a a => Free ρ R
    exact fun ρ R t => per_rule_lower_bound ρ R t
    exact fun ρ R B a => hcore ρ R B a



lemma charging_sum_lower_bound_delta
  (addedFamily :
    RuleOrder α → Finset (Rule α) → Rule α → Finset (Finset α))
  (Rep     : RuleOrder α → Finset (Rule α) → Finset (Finset α))
  (Missing : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Excess  : RuleOrder α → Finset (Rule α) → Finset α → ℤ)
  (Free    : RuleOrder α → Finset (Rule α) → Finset α)
  (chargeTo :
    RuleOrder α → Finset (Rule α) → Rule α → Finset α → Finset α)
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
  ≤ (∑ t ∈ R, ((Δ ρ R t : ℕ) : ℤ)) := by
  classical
  -- まず card 版（右辺が (addedFamily…).card の形）を使う
  have h_card :=
    charging_sum_lower_bound_card
      AF Rep Missing Excess Free chargeTo contrib_from
      per_rule_lower_bound hcore ρ R
  -- 右辺を Δ で書き換え（各項が定義一致）
  have hrhs :
      (∑ t ∈ R, ((AF ρ R t).card : ℤ))
        = (∑ t ∈ R, ((Δ ρ R t : ℕ) : ℤ)) := by
    refine Finset.sum_congr rfl ?step
    intro t ht
    simp_all only [sum_sub_distrib, tsub_le_iff_right, Δ_def]
    -- ここが以前の hpoint。今は定義一致なので rfl でOK。
    -- ((addedFamily ρ R t).card : ℤ) = ((Δ ρ R t : ℕ) : ℤ)
    -- `@[simp] Δ_cast_def` でも消えますが、方針通り `rfl` で。

  -- (1) 右辺を Δ に書換える部分（hrhs の sorry を置換）
  have hrhs :
      (∑ t ∈ R, ((AF ρ R t).card : ℤ))
        = (∑ t ∈ R, ((Δ ρ R t : ℕ) : ℤ)) := by
    apply sum_addedFamily_card_eq_sum_delta (AF := AF)

  -- (2) calc の最初の ≤（h_card の sorry を置換）
  calc
    (∑ B ∈ Rep ρ R,
       (Excess ρ R B - (Finset.card (Free ρ R) : ℤ) * Missing ρ R B))
      ≤ (∑ t ∈ R, ((AF ρ R t).card : ℤ)) := by
        apply charging_sum_LHS_le_sum_addedFamily_card AF
        exact fun a a a => AF ρ R a
        exact fun a a a a => Free ρ R
        exact fun ρ R t => per_rule_lower_bound ρ R t
        exact fun ρ R B a => hcore ρ R B a

    _ = (∑ t ∈ R, ((Δ ρ R t : ℕ) : ℤ)) := hrhs
