import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Nat.Choose.Sum
import LeanCopilot

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

open scoped BigOperators
variable {α : Type u} [DecidableEq α]

lemma finset_sum_le_finset_sum {ι : Type _} [DecidableEq ι] {N : Type _}
    [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N]
    {f g : ι → N} {s : Finset ι} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  refine Finset.induction_on s (by simp) (fun a s has IH => ?_) h
  ·
    intro x
    simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
      Finset.sum_insert]
    obtain ⟨left, right⟩ := x
    gcongr


omit [DecidableEq α] in
lemma sum_card_powerset_int (S : Finset α):-- (nonempty : S.Nonempty) :
  ∑ T ∈ S.powerset, (T.card : Int)
    = (2 : Int) ^ (S.card - 1) * (S.card : Int) := by
  classical
  by_cases hS : S.card = 0
  · -- S = ∅ の場合
    simp_all only [Finset.card_eq_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.cast_zero,
    zero_tsub, pow_zero, mul_zero]
  · -- S ≠ ∅ の場合

  -- powerset 上の「サイズだけに依存する」総和を階数別（card = k）に並べ替える
  --   ∑_{T⊆S} (|T| : ℤ)
  -- = ∑_{k=0..|S|} (|S| choose k) • (k : ℤ)
    have h₁ :
        ∑ T ∈ S.powerset, (T.card : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) • (k : Int) := by

      simpa using
        (Finset.sum_powerset_apply_card
          (α := Int) (f := fun k => (k : Int)) (x := S))

    -- `•`（nsmul）を通常の積に直す
    have h₂ :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) • (k : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) * (k : Int) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp

    -- 二項係数の恒等式：
    --   ∑_{k=0..n} k * (n choose k) = n * 2^{n-1}
    -- を ℤ へキャストして適用
    have h₃ :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) * (k : Int)
          =
        ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int) := by
      -- `range (n+1)` を `0` と `range n` に分解し、k ↦ k.succ で付け替え
      have hk0 :
        (S.card.choose 0 : Int) * (0 : Int) = 0 := by simp
      -- 分解
      have :
        ∑ k ∈ Finset.range (S.card + 1),
            (S.card.choose k : Int) * (k : Int)
        =
        (S.card.choose 0 : Int) * (0 : Int)
        + ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int) := by
        -- `range_succ` で末尾を分解 → 先頭の k=0 を取り出し、残りは k.succ で表す
        -- ここは等式を書いてから両辺を `simp` で整える
        -- 左辺
        have : Finset.range (S.card + 1)
                = insert 0 ((Finset.range S.card).map ⟨Nat.succ, Nat.succ_injective⟩) := by
          -- 標準事実： {0,1,...,n} = {0} ∪ {1,...,n}、後者は succ の像
          -- mathlib 既存の性質を `ext`/`simp` で示す
          apply Finset.ext
          intro k
          constructor <;> intro hk
          · by_cases hk0' : k = 0
            · subst hk0'; simp
            · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0'
              have hklt : k ≤ S.card := by
                -- `k ∈ range (n+1)` → `k < n+1`
                simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Finset.mem_range]
                omega
              rcases Nat.exists_eq_succ_of_ne_zero hk0' with ⟨j, rfl⟩
              simp [Finset.mem_range]
              exact hklt
          · -- 逆向き：画像にあれば range (n+1) に入る
            simp [Finset.mem_range] at hk
            rcases hk with hk | ⟨j, hj, rfl⟩
            · subst hk
              simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Finset.mem_range, lt_add_iff_pos_left,
                  add_pos_iff, Finset.card_pos, zero_lt_one, or_true]
            · have : j.succ < S.card + 1 := Nat.succ_lt_succ hj
              simpa [Finset.mem_range] using this
        -- これで右辺の形が得られる
        -- `sum` を `insert` と `map` に分解（0 は像に含まれないので `sum_insert` 可）
        -- ただしこの詳細展開は長くなるので、ここでは等式として採用
        -- 実務上は既存の reindex 補題 (`sum_bij`) で同値変換できる
        -- ここでは完成形だけ用いる
        -- （必要なら、この等式の証明を補題として別途立てる）
        simp_all only [Int.zsmul_eq_mul, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one,
          Nat.add_eq_zero, one_ne_zero, and_false, exists_const, not_false_eq_true, Finset.sum_insert, Nat.choose_zero_right,
          Nat.cast_one, Nat.cast_zero, mul_zero, Finset.sum_map, Nat.cast_add, zero_add]
          -- k=0項を消して完成
      simp_all only [Int.zsmul_eq_mul, Nat.choose_zero_right, Nat.cast_one, mul_zero, Nat.succ_eq_add_one, Nat.cast_add,
      zero_add]

    -- 3b) 各項を書き換え： `(k+1) * C(n, k+1) = n * C(n-1, k)`
    have h₄ :
        ∑ k ∈ Finset.range S.card,
            (S.card.choose k.succ : Int) * (k.succ : Int)
          =
        (S.card : Int) *
          ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int) := by
      rw [@Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      -- 自然数等式 `(k+1) * choose n (k+1) = n * choose (n-1) k`
      have hnat :
          (k.succ) * S.card.choose k.succ
            = S.card * (S.card - 1).choose k := by

        let nsm := (Nat.succ_mul_choose_eq (S.card - 1) k).symm
        simp
        simp at nsm
        have : S.card > 0 := by
          exact Nat.zero_lt_of_ne_zero hS
        have :S.card -1 + 1 = S.card := by
          exact Nat.sub_add_cancel this
        rw [this] at nsm
        rw [mul_comm] at nsm
        exact nsm
      -- 整数へキャストして左右を並べ替え
      -- まず両辺を `Int` に
      have hZ :
          ( (S.card.choose k.succ : Int) * (k.succ : Int) )
            = (S.card : Int) * ((S.card - 1).choose k : Int) := by
        -- `hnat` を `congrArg` でキャストし、`simp` で整形
        have hZ' := congrArg (fun n : ℕ => (n : Int)) hnat
        -- 左右を見かけの形に揃える
        -- （ここは `ring` 的な交換結合のみ）
        simpa [Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc]
          using hZ'
      -- 各項を書き換え
      simpa [hZ]
    -- 3c) 残った和は二項定理： `∑_{k=0}^{n-1} (n-1 choose k) = 2^{n-1}`
    have h₅ :
        ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int)
          = (2 : Int) ^ (S.card - 1) := by
      -- 自然数版を取得
      have hNat :
          ∑ k ∈ Finset.range S.card, (S.card - 1).choose k
            = 2 ^ (S.card - 1) := by
        -- `Nat.sum_range_choose` は `∑_{m=0}^{n} choose n m = 2^n`
        -- ここでは `n := S.card - 1`、かつ `range S.card = range (n+1)`
        -- よってそのまま適用できる
        -- 具体的には両辺を `Finset.range (S.card - 1 + 1)` に直して一致
        have := Nat.sum_range_choose (n := S.card - 1)
        -- `range (n+1) = range S.card` を使って形を合わせる
        -- ※ `Nat.sub_add_cancel` は `S.card ≥ 1` が必要だが、
        --    左右とも同じ `range (n+1)` 形にすることで回避できる
        -- ここではそのまま採用（`this` の右辺はちょうど必要な形）
        simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        have eq: (S.card - 1 + 1)= S.card := by
          exact Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero hS)
        rw [eq] at this
        exact this

      -- 両辺を `Int` へキャストして整形
      -- （`simp` のみで、`using` は使わない）
      have hInt : ((∑ k ∈ Finset.range S.card, (S.card - 1).choose k : ℕ) : Int)
                  = (2 : Int) ^ (S.card - 1) := by
        -- 右辺は自動で `Nat.cast_pow` に展開される
        -- 左辺は `Nat.cast_sum` 等で展開される
        -- ここでも `simp` のみ
        simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]


      -- 目的の左辺は最初から `Int` なので、これで一致
      -- なお `Finset.sum` の型は変わっていない（被積分関数を `Int` にしただけ）
      simp_all only [Int.zsmul_eq_mul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Nat.cast_sum]
      simp_all only [Nat.cast_pow, Nat.cast_ofNat]
    -- 4) 連結して整理
    calc
      ∑ T ∈ S.powerset, (T.card : Int)
          = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) • (k : Int) := h₁
      _   = ∑ k ∈ Finset.range (S.card + 1),
              (S.card.choose k : Int) * (k : Int) := h₂
      _   = ∑ k ∈ Finset.range S.card,
              (S.card.choose k.succ : Int) * (k.succ : Int) := h₃
      _   = (S.card : Int) *
              ∑ k ∈ Finset.range S.card, ((S.card - 1).choose k : Int) := h₄
      _   = (S.card : Int) * (2 : Int) ^ (S.card - 1) := by
              -- h₅ を右辺に代入
              exact congrArg (HMul.hMul ↑S.card) h₅

      _   = (2 : Int) ^ (S.card - 1) * (S.card : Int) := by
              simp [mul_comm]
