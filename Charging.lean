-- This module serves as the root of the `Charging` library.
-- Import modules here that should be built as part of the library.
/-
  Charging: DAG + (F) による NDS 非正性
  ルート・インポート・ハブ
-/
import Mathlib

-- Core: 規則系の基礎定義・NDS の定義・鎖分割など
import Charging.Core.Basic
import Charging.Core.NDS
import Charging.Core.Chains
/-
import Charging.Core.DAG

-- Assumptions: 仮定 (F), SC† の定義
import Charging.Assumptions.F
import Charging.Assumptions.SCdagger

-- Fiber: (F) ⇒ NDS ≤ 0 の心臓部
import Charging.Fiber.FiberF

-- Proofs: SC† ⇒ (F) の証明
import Charging.Proofs.SCdagger_to_F

-- Main: 上記を合成して主結果を得る
import Charging.Main.Main_NDS

-- Examples: 反例や小さな系の検証用（任意）
import Charging.Examples.Counterexample
-/
