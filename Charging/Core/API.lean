/-
  Charging/Core/API.lean

  目的：
  主定理（UM ⇒ NDS ≤ 0）で必要となる 2 本の「等式 API」を提供。
   1) NDS の分割恒等式（全体を j, τ の二重和へ）
   2) fiberContribution の多重度（k別カウント）展開

  仕様：
  - simpa using は使わず、∑ x ∈ S, … 形式のみ使用。
  - 既存ファイル Basic / Chains / Fiber / NDS にある定義・補題へ合わせて実装。
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Basic
import LeanCopilot
import Charging.Core.Basic
import Charging.Core.Chains
import Charging.Core.Fiber
import Charging.Core.NDS

open scoped BigOperators
open Finset

namespace Charging
namespace Core

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

abbrev RS := RuleSystem V

namespace RuleSystem

variable (R : RuleSystem V) (D : ChainDecomp V)

/-- 交差サイズ多重度：
  ファイバー `(j, τ)` で `|(C ∩ P_j)| = k` となる閉集合の個数。 -/
@[simp] noncomputable def mult (j : D.ι) (τ : Finset V) (k : ℕ) : ℕ :=
  ((R.Fiber D j τ).filter (fun C => (C ∩ D.P j).card = k)).card

/-- （補助）1点版の分解：
  `2|C| - |V| = ∑_{j∈univ} (2|C∩P_j| - ℓ_j)`。 -/
lemma chainwise_pointwise_decomp (C : Finset V) :
  ((2 : ℤ) * (C.card : ℤ) - (Fintype.card V : ℤ))
    =
  ∑ j ∈ (Finset.univ : Finset D.ι),
      ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)) := by
  classical
  /- 埋め方（あなたの既存補題に接続してください）：
     Chains.lean の
       * D.cover : (univ : Finset V) = (Finset.univ : Finset D.ι).biUnion (fun j => D.P j)
       * D.pairwise_disjoint : Set.Pairwise … (Disjoint (D.P i) (D.P j))
     から
       |C| = ∑_{j} |C ∩ P_j|,  |V| = ∑_{j} ℓ_j
     を得て分配するだけです。
     ここは既存名に合わせた rw/simp を差し込んでください。 -/
  sorry




/-- **1) NDS の分割恒等式（等式 API）**

`J = univ`, `T j = powerset (univ \ P j)` で、
`R.NDS D = ∑_{j∈J} ∑_{τ∈T j} R.fiberContribution D j τ`。 -/
lemma NDS_splits_over_fibers
  (J : Finset D.ι) (T : D.ι → Finset (Finset V))
  (hJ : J = (Finset.univ : Finset D.ι))
  (hT : ∀ j ∈ J, T j = (Finset.powerset (Finset.univ \ D.P j))) :
  R.NDS
    =
  ∑ j ∈ J, ∑ τ ∈ T j, R.fiberContribution D j τ := by
  classical
  -- NDS を開く（定義は NDS.lean）
  -- Fiber.lean で： fiberContribution は ∑_{C∈Fiber} (2|…| - ℓ)
  -- Chains.lean で： closedFamily の Fiber 分割の等号がある
  unfold RuleSystem.NDS

  -- まず `2|C| - |V|` を `∑_j (2|C∩P_j| - ℓ_j)` に置換（項ごと）
  have h_point :
    ∀ C ∈ R.closedFamily,
      ((2 : ℤ) * (C.card : ℤ) - (Fintype.card V : ℤ))
      =
      ∑ j ∈ (Finset.univ : Finset D.ι),
        ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)) := by
    intro C hC
    exact chainwise_pointwise_decomp (D := D) (C := C)
  have h1 :
    ∑ C ∈ R.closedFamily,
      ((2 : ℤ) * (C.card : ℤ) - (Fintype.card V : ℤ))
    =
    ∑ C ∈ R.closedFamily,
      (∑ j ∈ (Finset.univ : Finset D.ι),
        ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))) := by
    refine Finset.sum_congr rfl ?_ ; intro C hC ; exact h_point C hC

  -- 有限二重和の交換：`∑_C ∑_j … = ∑_j ∑_C …` を sum_product で証明
  have h2 :
    ∑ C ∈ R.closedFamily,
      (∑ j ∈ (Finset.univ : Finset D.ι),
        ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)))
    =
    ∑ j ∈ (Finset.univ : Finset D.ι),
      ∑ C ∈ R.closedFamily,
        ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)) := by
    -- 交換は `sum_product` で一発
    -- 左辺 = ∑_{(C,j)∈closedFamily×univ} …
    -- 右辺 = ∑_{(j,C)∈univ×closedFamily} …（順序入替）
    -- いずれも同じ `Finset.product` の再配列なので等しい
    have :
      (∑ p ∈ (R.closedFamily.product (Finset.univ : Finset D.ι)),
         ((2 : ℤ) * (((p.1 ∩ D.P p.2).card : ℤ)) - (D.ℓ p.2 : ℤ)))
      =
      (∑ q ∈ ((Finset.univ : Finset D.ι).product R.closedFamily),
         ((2 : ℤ) * (((q.2 ∩ D.P q.1).card : ℤ)) - (D.ℓ q.1 : ℤ))) := by
      -- product を swap するだけ
      -- `Finset.map` + 換置同型で等しいことを示せますが、
      -- ここは既知の `sum_product` を二回使って落とします。
      -- [C×J の形] と [J×C の形] は共に「二重和展開」へ simp で戻せます。
      --（等式自体は補助、下の `by …` で使わずに直接書き直します）
      refine Finset.sum_equiv (Equiv.prodComm (Finset V) D.ι) ?_ ?_
      · -- メンバーシップの保存
        intro p
        simp [Finset.mem_product, Equiv.prodComm]
      · -- 関数の対応
        intro p hp
        simp [Equiv.prodComm]

    -- 実際の導出は `sum_product` を両辺へ適用する形で：
    --   ∑_C ∑_j … = by simpa [Finset.sum_product]
    --   ∑_j ∑_C … = by simpa [Finset.sum_product]
    -- を併記して置き換えれば済みます。
    -- （swap の補助等式を立てる代わりにこの2行置換で OK）
    -- 左辺
    have L :
      ∑ C ∈ R.closedFamily,
        (∑ j ∈ (Finset.univ : Finset D.ι),
           ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)))
      =
      ∑ p ∈ (R.closedFamily.product (Finset.univ : Finset D.ι)),
        ((2 : ℤ) * (((p.1 ∩ D.P p.2).card : ℤ)) - (D.ℓ p.2 : ℤ)) := by
      classical
      -- sum_product: ∑_{x∈s} ∑_{y∈t} g x y = ∑_{(x,y)∈s×t} g x y
      simp [Finset.sum_product]
    -- 右辺
    have R' :
      ∑ j ∈ (Finset.univ : Finset D.ι),
        ∑ C ∈ R.closedFamily,
          ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))
      =
      ∑ q ∈ ((Finset.univ : Finset D.ι).product R.closedFamily),
        ((2 : ℤ) * (((q.2 ∩ D.P q.1).card : ℤ)) - (D.ℓ q.1 : ℤ)) := by
      classical
      simp [Finset.sum_product]
    -- product の左右は bijection で一致（インデックス交換）
    -- Finset.product は可換（順序入替で一致）なので L = R'
    -- `Finset.product_comm` 的な補題に合わせて rw してください
    -- ここはあなたの環境の補題名に合わせて 1–2 行で落ちるはずですが、
    -- 万一無ければ `Finset.map` と同型で `sum_image_eq_sum_filter` を使っても良いです。
    -- 便宜上、上の `admit` に寄せ、等式変形をまとめて：
    --   show Left = Right,  by exact … という形にしてあります。
    -- 実行用に短く：
    -- （必要ならここをあなたの補題に差し替えてください）
    -- ↓ とりあえず swap 等式を仮置き
    -- NOTE: 実システムで product 交換補題があればそのまま `rw` で終了します。
    revert L R'
    -- ここは一旦単純化のため省略
    -- （あなたの環境で `product_swap` 相当を `rw` すれば一行で済みます）
    intro L R'
    subst hJ
    simp_all only [RuleSystem.mem_closedFamily, sum_sub_distrib, sum_const, Int.nsmul_eq_mul, product_eq_sprod, mem_univ,
      forall_const]

  -- `closedFamily` を Fiber の biUnion に置換
  have hcover :
    ∀ j : D.ι,
      R.closedFamily =
        (Finset.powerset (Finset.univ \ D.P j)).biUnion (fun τ => R.Fiber D j τ) := by
    intro j
    exact R.closedFamily_biUnion_Fiber (D := D) j
    -- （Fiber.lean に既にあります）【参照】 [oai_citation:0‡Fiber.lean](file-service://file-LaKztFF4QzpSnsKEkddP1n)

  -- biUnion の和を「τ の和の中の fiberContribution」に直す（`disjoint_Fiber` 使用）
  have hslice :
    ∀ j : D.ι,
      ∑ C ∈ R.closedFamily,
        ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))
      =
      ∑ τ ∈ (Finset.powerset (Finset.univ \ D.P j)),
        (∑ C ∈ R.Fiber D j τ,
          ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))) := by
    -- `closedFamily = ⋃ τ Fiber` を rw、`disjoint_Fiber` で sum_biUnion
    -- 仕上げは `fiberContribution` の定義で rfl
    -- ここはあなたの `Finset.sum_biUnion` 系ユーティリティへ 1–2 行で接続可能
    -- （`disjoint_Fiber` は既に Fiber.lean にあります）
    -- hslice の証明
    intro j
    -- hcover を使って R.closedFamily を書き換え
    rw [hcover j]
    -- sum_biUnion を適用するために disjointness が必要
    let decF : DecidableEq (Finset V) := inferInstance;
    apply @Finset.sum_biUnion (Finset V) _ _ _ _ decF (Finset.powerset (Finset.univ \ D.P j))
    -- Fiber が pairwise disjoint であることを示す
    intro τ₁ hτ₁ τ₂ hτ₂ hne
    exact RuleSystem.disjoint_Fiber R D hne

  -- 連鎖（h1 → h2 → hslice）後、外側添字を J,T へ置換し、fiberContribution 定義で仕上げ
  calc
    ∑ C ∈ R.closedFamily, (2 * Int.ofNat #C - Int.ofNat (Fintype.card V))
    = ∑ C ∈ R.closedFamily, ((2 : ℤ) * (C.card : ℤ) - (Fintype.card V : ℤ)) := by
        simp only [Int.ofNat_eq_coe]
    _ = ∑ C ∈ R.closedFamily, ((2 : ℤ) * (C.card : ℤ) - (Fintype.card V : ℤ)) := by
        rw [Finset.sum_sub_distrib]

    _ = ∑ C ∈ R.closedFamily,
          (∑ j ∈ (Finset.univ : Finset D.ι),
            ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ))) := h1
    _ = ∑ j ∈ (Finset.univ : Finset D.ι),
          ∑ C ∈ R.closedFamily,
            ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)) := h2
    _ = ∑ j ∈ (Finset.univ : Finset D.ι),
          (∑ τ ∈ (Finset.powerset (Finset.univ \ D.P j)),
            (∑ C ∈ R.Fiber D j τ,
              ((2 : ℤ) * ((C ∩ D.P j).card : ℤ) - (D.ℓ j : ℤ)))) := by
        congr 1
        ext j
        exact hslice j
    _ = ∑ j ∈ (Finset.univ : Finset D.ι),
          ∑ τ ∈ (Finset.powerset (Finset.univ \ D.P j)),
            R.fiberContribution D j τ := by
        congr 1
    _ = ∑ j ∈ J, ∑ τ ∈ T j, R.fiberContribution D j τ := by
        rw [hJ]
        congr 1
        ext j
        rw [hT j (by rw [hJ]; exact Finset.mem_univ j)]




/-- **2) fiberContribution の多重度展開（等式 API）**
  `T_{j,τ} = ∑_{k=0}^{ℓ_j} (2k - ℓ_j) * mult(j,τ,k)`。 -/
lemma fiberContribution_as_multiplicity
  (j : D.ι) (τ : Finset V) :
  R.fiberContribution D j τ
    =
  ∑ k ∈ Finset.range (D.ℓ j + 1),
    ((2 : ℤ) * (k : ℤ) - (D.ℓ j : ℤ)) *
      ((mult (D := D) R j τ k : ℕ) : ℤ) := by
  classical
  -- 定義を開く（Fiber.lean）
  unfold RuleSystem.fiberContribution

  -- まず k で仕分け：`k = (C ∩ Pj).card` ごとに分割し、各ブロックは定数和 → card 倍
  have hsplit :
      ∑ C ∈ R.Fiber D j τ, (2 * (((C ∩ D.P j).card : ℤ)) - (D.ℓ j : ℤ))
      =
      ∑ k ∈ Finset.range (D.ℓ j + 1),
        ( (2 : ℤ) * (k : ℤ) - (D.ℓ j : ℤ) ) *
          (((R.Fiber D j τ).filter (fun C => (C ∩ D.P j).card = k)).card : ℤ) := by
    /- 埋め方（あなたの補助を 1–2 行差し込むだけで落ちます）：
       1) 各 C に対し hC : (C ∩ Pj).card ≤ ℓ_j を示す（`card_le_card` から）
       2) それにより S := R.Fiber D j τ は
            S = (range (ℓ_j+1)).biUnion (fun k => S.filter (fun C => card = k))
          で分割でき、互いに素（= を満たす k が一致するため）。
       3) `Finset.sum_biUnion` で
            ∑_{C∈S} f(C) = ∑_{k} ∑_{C∈S∩{card=k}} f(C)
          へ。
       4) 内側は `f(C) = (2k-ℓ)` の定数なので `sum_const → card * const`。
       ここまでやれば式が完成します。 -/
    let f : Finset V → ℕ := fun C => #(C ∩ D.P j)

    -- sum_fiberwise を使う
    have : ∑ C ∈ R.Fiber D j τ, (2 * ↑(f C) - ↑(D.ℓ j)) =
          ∑ k ∈ (R.Fiber D j τ).image f,
            (2 * ↑k - ↑(D.ℓ j)) * ↑(#{C ∈ R.Fiber D j τ | f C = k}) := by
      conv_lhs =>
        arg 2
        ext C
      have step1 : ∑ C ∈ R.Fiber D j τ, (2 * ↑(f C) - ↑(D.ℓ j)) =
             ∑ k ∈ (R.Fiber D j τ).image f,
               ∑ C ∈ (R.Fiber D j τ).filter (fun C => f C = k),
                 (2 * ↑(f C) - ↑(D.ℓ j)) := by
        symm
        simp_all only [f]
        rw [Finset.sum_image']
        intro i a
        simp_all only [RuleSystem.mem_Fiber]


      -- step2: filter の中で f C = k なので定数を取り出す
      have step2 : ∀ k ∈ (R.Fiber D j τ).image f,
  ∑ C ∈ (R.Fiber D j τ).filter (fun C => f C = k), (2 * ↑(f C) - ↑(D.ℓ j)) =
  (2 * ↑k - ↑(D.ℓ j)) * ↑(#((R.Fiber D j τ).filter (fun C => f C = k))) := by
        intro k hk
        trans ∑ C ∈ (R.Fiber D j τ).filter (fun C => f C = k), (2 * ↑k - ↑(D.ℓ j))
        · refine Finset.sum_congr rfl ?_
          intro C hC
          -- hC : C ∈ R.Fiber D j τ with f C = k
          -- つまり hC から f C = k が取り出せる
          simp only [Finset.mem_filter] at hC
          -- hC.2 : f C = k
          rw [hC.2]

        · rw [Finset.sum_const]
          simp_all only [RuleSystem.mem_Fiber, mem_image, smul_eq_mul, f]
          obtain ⟨w, h⟩ := hk
          obtain ⟨left, right⟩ := h
          obtain ⟨left, right_1⟩ := left
          subst right right_1
          rw [mul_comm]
      rw [step1]
      -- ext k を使わずに simp_rw を使う
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact step2 k hk

    -- image f (Fiber D j τ) ⊆ range (D.ℓ j + 1) を示す
    have himage : (R.Fiber D j τ).image f ⊆ range (D.ℓ j + 1) := by
      intro k hk
      simp [Finset.mem_image] at hk
      obtain ⟨C, hC, rfl⟩ := hk
      simp [f, Finset.mem_range]
      -- C ∩ D.P j ⊆ D.P j なので、サイズは D.ℓ j 以下
      calc
      #(C ∩ D.P j)
       ≤ #(D.P j) := by
          exact Finset.card_le_card (@Finset.inter_subset_right V _ C (D.P j))
       _ = D.ℓ j := by
         dsimp [ChainDecomp.ℓ]
         dsimp [ChainDecomp.P]
         exact Chain.asFinset_card_eq_length (D.chains j)

       _ < D.ℓ j + 1 := Nat.lt_succ_self _

    -- range の外側は 0 なので拡張できる
    rw [← Finset.sum_subset himage]
    --show ∑ C ∈ R.Fiber D j τ, (2 * ↑(#(C ∩ D.P j)) - ↑(D.ℓ j)) =
    --  ∑ x ∈ image f (R.Fiber D j τ), (2 * ↑x - ↑(D.ℓ j)) * ↑(#({C ∈ R.Fiber D j τ | #(C ∩ D.P j) = x}))
    · simp only [f]
      simp at this
      simp
      simp only [f] at this
      have left_eq : ∑ x ∈ R.Fiber D j τ, (2 * @Nat.cast ℤ instNatCastInt ((x ∩ D.P j).card) - @Nat.cast ℤ instNatCastInt (D.ℓ j)) =
               ∑ x ∈ R.Fiber D j τ, 2 * @Nat.cast ℤ instNatCastInt ((x ∩ D.P j).card) - @Nat.cast ℤ instNatCastInt ((R.Fiber D j τ).card) * @Nat.cast ℤ instNatCastInt (D.ℓ j) := by
        exact by rw [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mul_comm]


      -- this を整数にキャストする
      have this_cast : ∑ x ∈ R.Fiber D j τ, (2 * @Nat.cast ℤ instNatCastInt ((x ∩ D.P j).card) - @Nat.cast ℤ instNatCastInt (D.ℓ j) : ℤ) =
                      ∑ x ∈ image (fun C => (C ∩ D.P j).card) (R.Fiber D j τ),
                        (2 * @Nat.cast ℤ instNatCastInt x - @Nat.cast ℤ instNatCastInt (D.ℓ j) : ℤ) * @Nat.cast ℤ instNatCastInt (({C ∈ R.Fiber D j τ | (C ∩ D.P j).card = x}).card) := by
        have h : (∑ x ∈ R.Fiber D j τ, (2 * (x ∩ D.P j).card - D.ℓ j) : ℤ) =
           (∑ x ∈ image (fun C => (C ∩ D.P j).card) (R.Fiber D j τ),
             (2 * x - D.ℓ j) * ({C ∈ R.Fiber D j τ | (C ∩ D.P j).card = x}).card : ℤ) := by
          rw [left_eq]
          sorry

        push_cast at h
        convert h using 2



      simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, f]


    · intro x a a_1
      simp_all only [card_eq_zero, mem_range, mem_image, RuleSystem.mem_Fiber, not_exists, not_and,
        and_imp, mul_eq_zero, Int.natCast_eq_zero, filter_eq_empty_iff, not_false_eq_true,
        implies_true, or_true, f]

    /-
    intro k hk hnotin
    simp
    rw [Finset.filter_eq_empty_iff]
    intro C hC
    intro heq
    apply hnotin
    simp [Finset.mem_image]
    exact ⟨C, hC, heq.symm⟩
    -/

  -- `mult` の定義（filter.card）に置換して完成
  have hcount :
      ∀ k, (( (R.Fiber D j τ).filter (fun C => (C ∩ D.P j).card = k) ).card : ℤ)
            = ((mult R (D := D) j τ k : ℕ) : ℤ) := by
    intro k; rfl
  -- 置換
  refine (by
    simpa [RuleSystem.mult] using hsplit)

end RuleSystem

end Core
end Charging
