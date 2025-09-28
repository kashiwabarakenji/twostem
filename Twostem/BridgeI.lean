-- Twostem/BridgeI.lean
import Twostem.Bridge
import Twostem.Fiber
import Twostem.Closure
import Mathlib/Algebra/BigOperators.Basic

namespace Twostem

open Finset BigOperators

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- Bridge I の主和の左辺インデックス（欠損セル） -/
structure MissingCell (α : Type _) where
  (B : Finset α)
  (ω : Finset α)      -- Free 側の 0/1 割り当てのうち「存在しない（欠損）」セル
  -- 実装では ω ⊆ Free, fiber_R(B) に対応する I が存在しないこと、などを格納

/-- 欠損セル → 正規極小証人 → addedFamily への写像（Two-Stem+UC で多重度≤1） -/
def packMissingToAdded
  (ρ : RuleOrder α) (R : Finset (Rule α)) :
  MissingCell α → Σ' t : Rule α, Finset α := fun mc =>
  -- 具体：mc から first violation ルール t と witness S を構成して返す
  -- ここではシグマ型で (t,S) を返しておき、sum_bij で単射化する。
  ⟨Classical.choice (by classical exact ⟨arbitrary (Rule α), ∅⟩), ∅⟩

/-- 群分割：左辺（欠損セル）から右辺（addedFamily）の和へ `sum_bij` で対応付ける骨格 -/
lemma bridgeI_sum_bij_skeleton
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hTS : TwoStem (α:=α) R) (hUC : UniqueChild (α:=α) R) :
  True := by
  -- ここで本来は
  --   ∑_{missing cells} (|S|-2|B|) ≤ ∑_{t,I∈addedFamily} (2|I|-|S|)
  -- を `sum_bij` で構成する。
  -- 左：MissingCell リスト化 → packMissingToAdded で (t,S) へ
  -- 右：addedFamily の (t,I) でインデックス化
  -- firstDiff_localizes_one_coordinate & multiplicity_le_one_addedFamily を使って単射を担保。
  trivial

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- 欠損セルのデータ：
  B : Rep 側の固定部分
  ω : Free 側の 0/1 割当（ここでは 1 の集合として表現）
  valid : ω ⊆ Free
  missing : 「fiber_R(B) に ω を拡張した R-閉集合が存在しない」 -/
structure MissingCell (α : Type _) where
  (B : Finset α)
  (ω : Finset α)
  (Free : Finset α)
  (valid : ω ⊆ Free)
  (missing :
    ¬ ∃ I ∈ fiber R B, (I ∩ Free) = ω)   -- fiber 側の “該当セルが空”

/-- 欠損セルから first violation を取り、その極小証人 S を返す（正規化付き） -/
structure PackedWitness (α : Type _) where
  (t : Rule α)
  (S : Finset α)
  (canon_min : True)   -- 実装では “辞書式最小” を保証する述語を置く

/-- 欠損セル → PackedWitness 。
  実装は：
    欠損セル (B,ω) を B∪ω から反転して非閉にし、最初の違反 t を取り、
    その極小証人 S を辞書式最小で選ぶ。 -/
def packMissingToWitness
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (mc : MissingCell α) : PackedWitness α :=
  -- ここはロジックだけ提示：実装は “first violation” 関数と
  -- “極小証人の辞書式正規化” が必要（Synchronous で既に雛形あり）。
  -- 以降の sum_bij では「この写像が定義されること」だけ使う。
  ⟨Classical.choice (by classical exact ⟨arbitrary (Rule α), True.intro⟩),
   ∅, True.intro⟩

/-- PackedWitness から addedFamily の要素へ：
  t を消した閉包 J := cl[R\{t}](B∪S) を返す。 -/
def witnessToAddedFamily
  (R : Finset (Rule α)) (B : Finset α)
  (pw : PackedWitness α) : Finset α :=
  closure (R.erase pw.t) (B ∪ pw.S)

/-- 欠損セル → addedFamily への合成写像 -/
def packMissingToAdded
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B : Finset α) :
  MissingCell α → Finset α :=
  fun mc => witnessToAddedFamily (R:=R) B (packMissingToWitness (α:=α) ρ R mc)

/-- Bridge I の群分割スケルトン：
  sum_bij で「欠損セルの総和 ≤ addedFamily の総和」に対応付ける準備。 -/
lemma bridgeI_sum_bij_skeleton
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hTS : TwoStem (α:=α) R) (hUC : UniqueChild (α:=α) R)
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
