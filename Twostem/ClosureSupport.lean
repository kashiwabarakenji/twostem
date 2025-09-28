-- Twostem/ClosureSupport.lean
import Mathlib/Data/Finset/Basic
import Twostem.Rules
import Twostem.Closure

namespace Twostem

open Finset

variable {α : Type _} [DecidableEq α]

/-- 導出存在補題（Closure の標準事実）：
  a が closure(R,X) に入るのは、
  (i) a∈X か、または
  (ii) あるルール t∈R が head=t.head=a をもち、t.prem ⊆ closure(R,X) であるとき。 -/
theorem head_in_closure_iff_exists_rule
  {R : Finset (Rule α)} {X : Finset α} {a : α} :
  a ∈ closure R X ↔ (a ∈ X ∨ ∃ t ∈ R, t.head = a ∧ t.prem ⊆ closure R X) := by
  -- ここは Twostem/Closure の定義に依存して機械的に証明できます。
  -- 今回はインターフェースとして公開。Closure 側で証明を与える予定。
  -- 一旦、Closure モジュールに備えてあるはずの補題名を想定してリライトするなら
  --   exact closure_mem_iff_head_or_rule ...
  -- 等で短く終えられます。実装は次のステップで埋めます。
  admit

/-- monotonicity：R を縮めれば（ルールを消せば）closure は小さくなる。 -/
theorem closure_mono_rules
  {R R' : Finset (Rule α)} {X : Finset α}
  (h : R' ⊆ R) :
  closure R' X ⊆ closure R X := by
  admit

/-- 生成単調性：基底集合が増えれば closure も増える。 -/
theorem closure_mono_base
  {R : Finset (Rule α)} {X Y : Finset α}
  (h : X ⊆ Y) :
  closure R X ⊆ closure R Y := by
  admit

end Twostem