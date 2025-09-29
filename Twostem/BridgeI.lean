-- Twostem/BridgeI.lean
import Twostem.Bridge
import Twostem.Fiber
import Twostem.Closure
import Mathlib.Algebra.BigOperators.Finsupp.Basic

namespace Twostem

open Finset BigOperators

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/- Bridge I の主和の左辺インデックス（欠損セル） -/
--structure MissingCell (α : Type _) where
--  (B : Finset α)
--  (ω : Finset α)      -- Free 側の 0/1 割り当てのうち「存在しない（欠損）」セル
  -- 実装では ω ⊆ Free, fiber_R(B) に対応する I が存在しないこと、などを格納


/-- 欠損セルのデータ：
  B : Rep 側の固定部分
  ω : Free 側の 0/1 割当（ここでは 1 の集合として表現）
  valid : ω ⊆ Free
  missing : 「fiber_R(B) に ω を拡張した R-閉集合が存在しない」 -/
structure MissingCell
  (α : Type _) [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) [DecidablePred (IsClosed R)]
  (Rep : Finset α) where
  B      : Finset α
  ω      : Finset α
  Free   : Finset α
  valid  : ω ⊆ Free
  missing :
    ¬ ∃ I, I ∈ fiber (α := α) R Rep B ∧ I ∩ Free = ω

/- 重複しているのでコメントアウト
/-- 欠損セル → 正規極小証人 → addedFamily への写像（Two-Stem+UC で多重度≤1） -/
noncomputable def packMissingToAdded
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  MissingCell α → Σ' t : Rule α, Finset α := fun mc =>
  -- 具体：mc から first violation ルール t と witness S を構成して返す
  -- ここではシグマ型で (t,S) を返しておき、sum_bij で単射化する。
  ⟨Classical.choice (by classical exact ⟨arbitrary (Rule α), ∅⟩), ∅⟩
-/

/-重複しているのでコメントアウト
/-- 群分割：左辺（欠損セル）から右辺（addedFamily）の和へ `sum_bij` で対応付ける骨格 -/
lemma bridgeI_sum_bij_skeleton
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hTS : TwoStemR (α:=α) R) (hUC : UniqueChild (α:=α) R) :
  True := by
  -- ここで本来は
  --   ∑_{missing cells} (|S|-2|B|) ≤ ∑_{t,I∈addedFamily} (2|I|-|S|)
  -- を `sum_bij` で構成する。
  -- 左：MissingCell リスト化 → packMissingToAdded で (t,S) へ
  -- 右：addedFamily の (t,I) でインデックス化
  -- firstDiff_localizes_one_coordinate & multiplicity_le_one_addedFamily を使って単射を担保。
  trivial
-/

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- 欠損セルから first violation を取り、その極小証人 S を返す（正規化付き） -/

structure PackedWitness
  (α : Type _) [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) [DecidableEq (Rule α)]
  (ρ : RuleOrder α) (B : Finset α) where
  t     : Rule α
  S     : Finset α
  t_mem : t ∈ R
  wit   : isWitness ρ R B S t


--上のpackMissingToWitnessの実装はWitnessのところで定めているので重複定義になっている。
/-- 欠損セル → PackedWitness 。
  実装は：
    欠損セル (B,ω) を B∪ω から反転して非閉にし、最初の違反 t を取り、
    その極小証人 S を辞書式最小で選ぶ。 -/
noncomputable def packMissingToWitness
  (ρ : RuleOrder α) (R : Finset (Rule α)) [DecidablePred (IsClosed R)](nonemp: R.Nonempty) (Rep : Finset α)
  (mc : MissingCell α R Rep) : PackedWitness α R ρ Rep :=
  -- ここはロジックだけ提示：実装は “first violation” 関数と
  -- “極小証人の辞書式正規化” が必要（Synchronous で既に雛形あり）。
  -- 以降の sum_bij では「この写像が定義されること」だけ使う。
  ⟨Classical.choose nonemp,
   ∅, Classical.choose_spec nonemp, sorry⟩

/-- PackedWitness から addedFamily の要素へ：
  t を消した閉包 J := cl[R\{t}](B∪S) を返す。 -/
def witnessToAddedFamily {α : Type _} [Fintype α] [DecidableEq α][LinearOrder α]
  (ρ : RuleOrder α)
  (R : Finset (Rule α)) (Rep : Finset α) (B : Finset α)
  (pw : PackedWitness α R ρ Rep) : Finset α :=
  syncCl (R.erase pw.t) (B ∪ pw.S)

/-- 欠損セル → addedFamily への合成写像 -/
noncomputable def packMissingToAdded
  (ρ : RuleOrder α) (R : Finset (Rule α)) [DecidablePred (IsClosed R)](nonemp: R.Nonempty) (Rep : Finset α) (B : Finset α) :
  MissingCell α R Rep → Finset α :=
  fun mc => witnessToAddedFamily ρ R Rep B (packMissingToWitness (α:=α) ρ R nonemp Rep mc)

lemma witness_to_added_mem
  [DecidableEq α] [Fintype α]
  {R : Finset (Rule α)} [DecidablePred (IsClosed R)]
  {B : Finset α} {ρ : RuleOrder α}
  {t : Rule α} {S : Finset α} :
  isWitness ρ R B S t →
  syncCl (R.erase t) (B ∪ S) ∈ addedFamily (α:=α) R t := by
  sorry


omit [Fintype α] [LinearOrder α] in
/-- Bridge I の群分割スケルトン：
  sum_bij で「欠損セルの総和 ≤ addedFamily の総和」に対応付ける準備。 -/
lemma bridgeI_sum_bij_skeleton
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hTS : TwoStemR (α:=α) R) (hUC : UC (α:=α) R)
  (Rep Free : Finset α) :
  True := by
  -- 実装方針メモ：
  -- * 左辺インデックス：{ MissingCell α | B⊆Rep, ω⊆Free, missing } を Finset 化
  -- * 右辺インデックス：⋃_{t∈R} addedFamily(R,t) を Finset 化
  -- * f := packMissingToAdded で sum_bij（定義域 → 値域）を与える
  -- * injective：multiplicity_le_one_addedFamily を使用
  -- * well-defined：witness の構成が addedFamily の要件（prem⊆…, head∉…）を満たすのは Witness 補題
  -- * fibers/weights：各項の寄与 (|S|-2|B|) vs (2|I|-|S|) の比較は per-rule 優越の加算で処理
  trivial

end Twostem
