import Mathlib.Data.Finset.Basic
import Twostem.Basic
import Twostem.ProblemA
import Twostem.Excess
import Twostem.ProblemA_UC
import Twostem.B_Existence
import Twostem.ProblemCC

universe u
variable {α : Type u} [DecidableEq α]

namespace B_Existence

open Classical
open ProblemA_UC
open ThreadA
open B_Existence

/-- C1'（安全版）:
NoBarrier のもとで、もし `parents ∈ Core` かつ `ViolSet ≠ ∅` かつ `size_lb` が成り立つなら、`child ∈ Core`。
（対偶：`child ∉ Core` なら Barrier が立つので NoBarrier と矛盾） -/
lemma NoBarrier_core_closed_under_child'
  (V : Finset α) (R : Finset (Rule α))
  (hNoB : ∀ t ∈ R, ¬ ThreadA.BarrierHyp V R t) :
  ∀ {t : Rule α}, t ∈ R →
    t.1 ∈ Core V R t → t.2.1 ∈ Core V R t →
    (ViolSet V R t ≠ ∅) →
    V.card ≤ 2 * (Core V R t).card →
    t.2.2 ∈ Core V R t := by
  intro t ht hpa hpb hne hsize
  by_contra hchild
  -- Core ⊆ I for any I ∈ ViolSet は定義から従う（既存補題）
  have hCoreSub : ∀ {I}, I ∈ ViolSet V R t → Core V R t ⊆ I := by
    intro I hI
    exact Core_subset_of_mem_ViolSet (V := V) (R := R) (t0 := t) hI
  -- Barrier 仮定が立つ
  have hB : ThreadA.BarrierHyp V R t := by
    refine
    { nonempty  := hne
      , parents   := ⟨hpa, hpb⟩
      , child_out := hchild
      , size_lb   := hsize
      , coreSub   := ?_ }
    intro I hI; simpa using hCoreSub hI
  -- NoBarrier と矛盾
  exact (hNoB t ht) hB

  /-- A1. supportedOn の保存（SCC 版ラッパ） -/
lemma supportedOn_contractRules_SCC
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  : supportedOn V (contractRules (π := Q.π) (σ := Q.σ) R) := by
  -- 既存：supportedOn_contractRules は (σ b ∈ V) だけあれば通る
  exact supportedOn_contractRules (V := V) (R := R)
    (π := Q.π) (σ := Q.σ) (hσ := Q.σ_in_V)

  /-- A2. SafeShrink 梱包（`contractRules` をそのまま R1 に） -/
lemma SafeShrink_of_contractRules
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hSup  : supportedOn V (contractRules (π := Q.π) (σ := Q.σ) R))
  (hCard : (contractRules (π := Q.π) (σ := Q.σ) R).card < R.card)
  (hNDS  : NDS2 V (family V R)
           ≤ NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R))) :
  SafeShrink V R (contractRules (π := Q.π) (σ := Q.σ) R) := by
  exact ⟨hCard, hSup, hNDS⟩

  /-- B0. `contractRules` の元写像を名前付きに -/
def mapRule_Q
  {V : Finset α} {R : Finset (Rule α)}
  (Q : SCCQuot α V R) (t : Rule α) : Rule α :=
  (Q.σ (Q.π t.1), (Q.σ (Q.π t.2.1), Q.σ (Q.π t.2.2)))

--dummy
def SCCClass {V : Finset α} {R : Finset (Rule α)} (Q : SCCQuot α V R) (C: Finset α): Prop:=
  True

--SCCClassは未定義
lemma exists_nontrivial_SCC_in_Core
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R)
  (hne : R ≠ ∅)
  (hV  : supportedOn V R)
  (hNoB : ∀ t∈R, ¬ ThreadA.BarrierHyp V R t) :
  ∃ C : Finset α, SCCClass Q C ∧ C ⊆ Finset.biUnion (R : Finset (Rule α)) (λ t => Core V R t) ∧ 2 ≤ C.card := by
  classical
  -- TODO: SCC.lean の到達関係と Core 構造から C を構成
  admit

lemma parent_saturation_in_SCC_Core
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hUC : UniqueChild R)
  (hNoB : ∀ t∈R, ¬ ThreadA.BarrierHyp V R t)
  {a a' b : α} (hSCC : Q.π a = Q.π a')
  (ha : a ∈ ⋃ t∈R, Core V R t)
  (ha' : a' ∈ ⋃ t∈R, Core V R t)
  (hb : b ∈ ⋃ t∈R, Core V R t)
  {r : α} (hR : ((a,b,r) : Rule α) ∈ R) :
  ∃ r', ((a',b,r') : Rule α) ∈ R ∧ Q.π r' = Q.π r := by
  classical
  -- TODO:
  -- 1) Core の性質（C1’）で、必要な局面の子も Core に入ることを確保
  -- 2) UniqueChild：各 r について InStar.card ≤ 1 を使い、
  --    (a,b,_) と (a',b,_) が「子の SCC を一致させる」ことから r' の存在を導く
  -- 3) Q.π r' = Q.π r を結論
  admit

--定義途中の補題を使っているためエラー
lemma noninjectiveOn_mapRule_from_UC_NoBarrier
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R)
  (hV  : supportedOn V R)
  (hUC : UniqueChild R)
  (hne : R ≠ ∅)
  (hNoB : ∀ t∈R, ¬ ThreadA.BarrierHyp V R t) :
  ¬ Set.InjOn (mapRule_Q (Q := Q)) (R : Set (Rule α)) := by
  classical
  -- 1) Core 合併上に |SCC|≥2 の成分を確保（C3）
  obtain ⟨C, hC_scc, hC_sub, hC_ge2⟩ :=
    exists_nontrivial_SCC_in_Core (V := V) (R := R) (Q := Q) hne hV hNoB
  -- 2) a ≠ a' かつ π a = π a' を選ぶ
  --    （SCCClass から2点を取り、SCCQuot の性質で hSCC を得る）
  -- TODO: a,a'∈C with a≠a' を取り、hSCC : Q.π a = Q.π a' を得る
  -- 3) b と (a,b,r)∈R を確保（supportedOn & Core 合併から）
  -- 4) C4 で (a',b,r')∈R かつ π r' = π r を得る
  -- 5) t₁≠t₂ かつ mapRule_Q t₁ = mapRule_Q t₂ ⇒ 非単射 witness 完成
  admit

lemma card_contractRules_lt_from_noninj
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R)
  (hNonInj : ¬ Set.InjOn (mapRule_Q (Q := Q)) (R : Set (Rule α))) :
  (contractRules (π := Q.π) (σ := Q.σ) R).card < R.card := by
  -- 既存補題（非単射 witness ⇒ `<`）をラップして使うだけ
  apply card_contractRules_lt_of_nonninj (R := R) (π := Q.π) (σ := Q.σ)
  dsimp [Set.InjOn] at hNonInj
  simp at hNonInj
  obtain ⟨t1, t2, t3, ht, q1, heq⟩ := hNonInj
  obtain ⟨q2,q3,hqq⟩ := heq
  use ⟨t1, t2, t3⟩
  constructor
  · exact ht
  · use ⟨q1, q2, q3⟩
    constructor
    · exact hqq.1
    · constructor
      · by_contra hqeq
        simp_all only [true_and, Prod.mk.injEq, not_true_eq_false, imp_false, and_false]
      · dsimp [mapRule_Q] at hqq
        simp_all only [Prod.mk.injEq]

noncomputable def cl_R1 (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (B : Finset α) : Finset α :=
  Finset.filter (fun x : α => (∀ II : Finset α, II ⊆ Rep (Q := Q) ∧ B ⊆ II ∧ isClosed (R1 (V := V) (R := R) (Q := Q)) II → x ∈ II)) V

lemma cl_R1_closed_mem_familyRep (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (B : Finset α):
  cl_R1 V R Q B ∈ familyRep V R Q := by
  dsimp [cl_R1, familyRep, Rep]
  sorry
lemma subset_cl_R1(V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (B : Finset α) : B ⊆ cl_R1 V R Q B := by search_proof
lemma cl_R1_idem  : cl_R1 V R Q (cl_R1 V R Q B) = cl_R1 V R Q B :=by sorry

lemma NDS2_family_contractRules_zero
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) (hV  : supportedOn V R):
  NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R)) = 0 := by
  classical
  -- 既存：R1 側の因数分解
  have hfac := ThreadC.NDS2_family_contractRules_factorized
                 (V := V) (R := R) (Q := Q)
  -- 既存：パワーセット上の係数和が 0
  have hsum := sum_over_powerset_block_coeff_zero (V := V) (R := R) (Q := Q)
  -- ↑ 2つを組み合わせて 0 を得る（詳細はプロジェクトの式形に合わせて rw / simp）
  -- 例：
  --   rw [hfac]; simpa [hsum]    あるいは    simpa [hfac, hsum]
  dsimp [contractRules] at hfac
  dsimp [contractRules]
  rw [hfac hV ]

  --dsimp [familyRep]
  --dsimp [isClosed]
  --dsimp [contractRules]
  --これは成り立たないかも。
  have : (Rep Q).powerset = familyRep V R Q := by
    ext X
    --これはR1に関するものなので違うかも。
    --let mfc := mem_family_contractRules_iff (V := V) (R := R) (Q := Q)
    --specialize mfc hV







    dsimp [familyRep, Rep]
    sorry


lemma nds_nondec_under_contractRules_UC_NoBarrier
  (V : Finset α) (R : Finset (Rule α))
  (Q : SCCQuot α V R)
  (hV  : supportedOn V R)
  (nonemp: (Free Q).Nonempty)
  (hUC : UniqueChild R)
  (hNoB : ∀ t∈R, ¬ ThreadA.BarrierHyp V R t) :
  NDS2 V (family V R)
    ≤ NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R)) := by
  classical
  -- R1 側が 0
  have hR1zero :
      NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R)) = 0 :=
    NDS2_family_contractRules_zero (V := V) (R := R) (Q := Q)
  -- 0-版の差分恒等式（一般形は使わない）
  have hDecomp :=
    NDS2_diff_eq_negDebt_plus_Excess_of_R1_zero
      (V := V) (R := R) (Q := Q) (hR1zero := hR1zero)
  -- Excess ≥ 0
  have hEx_ge0 :
      0 ≤ ∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B := by
    exact Excess_sum_nonneg (V := V) (R := R) (Q := Q) nonemp

  -- Debt 合計 ≤ 0 へ（ブロック版の小補題を総和に上げる）
  --   * UC＋NoBarrier＋B2（非単射 witness）→「正の寄与が立たない/相殺」
  --   * 既存の `Debt_nonpos`（ProblemCC）と併用して ≤ 0 を確定
  have hDebt_le0 :
      (∑ B ∈ (Rep (Q := Q)).powerset, ThreadC_Fiber.Debt V R Q B) ≤ 0 := by
    -- TODO: `debt_block_nonpos_under_NoBarrier_UC` を証明して、ここで `sum_le_zero` に集約
    sorry
  -- Δ = -∑Debt + ∑Excess ≥ 0
  have hΔ_ge0 :
      0 ≤
        (NDS2 V (family V (contractRules (π := Q.π) (σ := Q.σ) R))
           - NDS2 V (family V R)) := by
    -- 右辺を Debt/Excess 表現に置換
    -- hDecomp :
    --   NDS2(R1) - NDS2(R) = - (∑ Debt) + (∑ Excess)
    -- 符号付け注意： `- (∑Debt) ≥ 0` は `∑Debt ≤ 0` と同値
    have : 0 ≤ (-(∑ B ∈ (Rep (Q := Q)).powerset, ThreadC_Fiber.Debt V R Q B)
                +  (∑ B ∈ (Rep (Q := Q)).powerset, Excess V R Q B)) := by
      have := add_le_add (neg_nonneg.mpr hDebt_le0) hEx_ge0
      simpa using this
    simp_all only [Prod.forall, R1, zero_sub, le_neg_add_iff_add_le, add_zero]

  -- 目標へ（R ≤ R1）
  -- hR1zero により NDS2(R1) = 0、よって `0 ≤ NDS2(R1) - NDS2(R)` は `NDS2(R) ≤ NDS2(R1)` と同値
  exact sub_nonneg.mp hΔ_ge0
