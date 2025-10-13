import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Finsupp.Basic
--import Mathlib.Data.Finset.LocallyFinite
--import Mathlib.Algebra.BigOperators.Ring

open scoped BigOperators
open Finset

namespace Charging

variable {V : Type*} [DecidableEq V]

/-- 多重度: 閉集合 `closedSets`、鎖成分 `Pj`、外側固定部 `τ`、交差サイズ `k`。 -/
def mult
  (closedSets : Finset (Finset V))
  (Pj τ : Finset V) (k : ℕ) : ℕ :=
  #({C ∈ closedSets |
       C \ Pj = τ ∧ (C ∩ Pj).card = k })

/-- ファイバー寄与（定義式の書換え先）。 -/
def fiberContribution
  (closedSets : Finset (Finset V))
  (Pj τ : Finset V) : ℤ :=
  ∑ C ∈ (closedSets.filter (fun C => C \ Pj = τ)),
    (2 * ((C ∩ Pj).card : ℤ) - (Pj.card : ℤ))

/-- Fiber–MS: 支持が初期区間 `{0,…,K}` をなす。 -/
def FiberMS
  (closedSets : Finset (Finset V))
  (Pj τ : Finset V) : Prop :=
  ∃ K ≤ Pj.card,                      -- K は ℓ=|Pj| 以下
    (∀ k, k ≤ Pj.card →                -- 支持の包含
      (mult closedSets Pj τ k > 0 → k ≤ K)) ∧
    (∀ k ≤ K, mult closedSets Pj τ k > 0)  -- 穴なし

/-- UM: 多重度が単調非増加。 -/
def UM
  (closedSets : Finset (Finset V))
  (Pj τ : Finset V) : Prop :=
  ∀ {k k' : ℕ}, k ≤ k' → k' ≤ Pj.card →
    mult closedSets Pj τ k' ≤ mult closedSets Pj τ k

/-- 多重度による表現（等価書換）—証明は後続ファイルで。 -/
def fiberContributionAsMultiplicity
  (closedSets : Finset (Finset V))
  (Pj τ : Finset V) : Prop :=
  True  -- TODO: replace by an `=` lemma once RuleSystem API is wired
