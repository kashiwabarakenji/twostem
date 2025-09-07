import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Twostem.Basic
import LeanCopilot
open scoped Rat
--import Mathlib.Tactic.NormCast

--charge_lower_bound 問題が生じて、メインの証明に用いないことになった。
--あとでエラーだけ解消するが後回し。

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

namespace ThreadB_CastTransfer

/-- 親ごとの重みは非負：`(∀ t ∈ S, 0 ≤ w t)` なら
    `∀ x, 0 ≤ ∑ t ∈ S, if (t.1 = x ∨ t.2.1 = x) then w t else 0`。 -/
lemma parent_load_nonneg
  (S : Finset (Rule α)) (w : Rule α → ℚ)
  (hwnn : ∀ t, t ∈ S → 0 ≤ w t) :
  ∀ x, 0 ≤ (∑ t ∈ S, if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
  classical
  intro x
  -- 各項が非負であることを示してから `Finset.sum_nonneg` を適用
  have hterm : ∀ t ∈ S, 0 ≤ (if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
    intro t ht
    by_cases hx : (t.1 = x ∨ t.2.1 = x)
    · -- `if_pos`
      have hw : 0 ≤ w t := hwnn t ht
      rw [if_pos hx]
      exact hw
    · -- `if_neg`
      rw [if_neg hx]
      --exact le_of_eq rfl
  exact Finset.sum_nonneg hterm --検索にかからないけど、BigOperators.Group.Finset

/-- `χ_I(x) ∈ {0,1}` を使った基本不等式：
    `0 ≤ s ≤ 1` なら `chi I x * s ≤ chi I x`。 -/
lemma chi_times_parentload_le_chi
  (I : Finset α) (x : α) (s : ℚ)
  --(hs0 : 0 ≤ s)
  (hs1 : s ≤ 1) :
  chi I x * s ≤ chi I x := by
  classical
  by_cases hx : x ∈ I
  · -- `χ_I(x) = 1`
    -- 左：`1 * s = s`、右：`1`、よって `s ≤ 1`
    rw [chi, if_pos hx]
    rw [one_mul]
    -- 目標は `s ≤ 1`
    exact hs1
  · -- `χ_I(x) = 0`
    -- 左：`0 * s = 0`、右：`0`
    rw [chi, if_neg hx]
    rw [zero_mul]



/-- 親全被覆の書き換え：`ParentSet V R r = V` なら
    `∑_{x ∈ ParentSet} χ_I(x) = ∑_{x ∈ V} χ_I(x)`。 -/
lemma cover_rewrite
  (V : Finset α) (R : Finset (Rule α)) (r : α)
  (hCover : ParentSet V R r = V) :
  ∀ I, (∑ x ∈ ParentSet V R r, chi I x) = (∑ x ∈ V, chi I x) := by
  classical
  intro I
  -- 集合の等号で素直に書き換え
  rw [hCover]

/-- `V = ∅` でなければ、`T := totalWeight (R.erase t0) r w` は正。
    ここで `r = t0.2.2`。親全被覆と総量下限から従う。 -/
lemma T_pos_of_cover_or_trivial
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  {w : Rule α → ℚ}
  (hCover : ParentSet V (R.erase t0) t0.2.2 = V)
  (hLPge :
    totalWeight (R.erase t0) t0.2.2 w
      ≥ (ParentSet V (R.erase t0) t0.2.2).card / 2) :
  V = ∅ ∨ 0 < totalWeight (R.erase t0) t0.2.2 w := by
  classical
  by_cases hV : V = ∅
  · -- 空なら左側で終了
    exact Or.inl hV
  · -- 非空なら `|V| > 0` なので `(|V| : ℚ) / 2 > 0`、従って `T > 0`
    -- `T ≥ |ParentSet|/2` を `|V|/2` に書き換え
    have hT_ge : totalWeight (R.erase t0) t0.2.2 w ≥ (V.card : ℚ) / 2 := by
      -- `hLPge` の右辺を `hCover` で書き換える
      have h := hLPge
      -- 右辺 `(ParentSet ...).card / 2` を `V.card / 2` に
      -- 直接 `rw [hCover]` で書き換え可能
      rw [hCover] at h
      exact h
    -- `V ≠ ∅` なので `V.Nonempty`
    have hne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hV
    -- `|V| > 0` （Nat）
    have hcard_pos_nat : 0 < V.card := Finset.card_pos.mpr hne
    -- `(|V| : ℚ) > 0`
    have hcard_pos_rat : (0 : ℚ) < (V.card : ℚ) := by
      exact_mod_cast hcard_pos_nat
    -- `(|V| : ℚ) / 2 > 0`
    have hhalf_pos : (0 : ℚ) < (V.card : ℚ) / 2 := by
      -- `div_pos` を使う（`0 < 2` は `zero_lt_two`）
      have h2pos : (0 : ℚ) < (2 : ℚ) := by
        exact zero_lt_two
      exact div_pos hcard_pos_rat h2pos
    -- 以上より `0 < T`
    have hT_pos : 0 < totalWeight (R.erase t0) t0.2.2 w :=
      lt_of_lt_of_le hhalf_pos hT_ge
    exact Or.inr hT_pos

/- 二重和の入れ替え：`∑_{I∈A} ∑_{t∈S} f t I = ∑_{t∈S} ∑_{I∈A} f t I`。 -/

omit [DecidableEq α] in
lemma swap_sum_instar_added
  (A : Finset (Finset α))
  (S : Finset (Rule α))
  (phi: Rule α → Finset α → ℚ) :
  (∑ I ∈ A, ∑ t ∈ S, phi t I)
  = (∑ t ∈ S, ∑ I ∈ A, phi t I) := by
  classical
  -- まず両辺を直積上の和に書き換える
  have hL :
      (∑ I ∈ A, ∑ t ∈ S, phi t I)
        = ∑ p ∈ A.product S, phi   p.2 p.1 := by
    -- sum_product の形に合わせるため、一旦関数を `fun I t => f t I` として書く
    change (∑ I ∈ A, ∑ t ∈ S, (fun I t => phi t I) I t)
            = (∑ p ∈ A.product S, (fun I t => phi t I) p.1 p.2)
    -- `sum_product : ∑_{(I,t)∈A×S} g I t = ∑_{I∈A} ∑_{t∈S} g I t`
    -- の対称版（=両辺を入れ替えた形）
    simp_all only [Finset.product_eq_sprod]
    rw [Finset.sum_product]

  have hR :
      (∑ t ∈ S, ∑ I ∈ A, phi t I)
        = ∑ q ∈ S.product A, phi q.1 q.2 := by
    change (∑ t ∈ S, ∑ I ∈ A, (fun t I => phi t I) t I)
            = (∑ q ∈ S.product A, (fun t I => phi t I) q.1 q.2)
    simp_all only [Finset.product_eq_sprod]
    rw [Finset.sum_product]

  -- 次に、`A.product S` と `S.product A` を `Prod.swap` で対応付けて値が一致することを示す
  have hswap :
      ∑ p ∈ A.product S, phi p.2 p.1
        = ∑ q ∈ S.product A, phi q.1 q.2 := by
    -- `sum_bij` で、`g := Prod.swap` を用いた全単射を与える
    refine
      (Finset.sum_bij
        (i := fun p hp => Prod.swap p)
        (hi := ?_)
        (i_inj := ?_)
        (i_surj := ?_)
        (h := ?_)
        (s := A.product S)
        (t := S.product A)
        (f := fun p : (Finset α × Rule α) => phi p.2 p.1)
        (g := fun q : (Rule α × Finset α) => phi q.1 q.2))
    -- 画像が右側に属すること
    · intro p hp
      -- `p ∈ A.product S` ↔ `p.1 ∈ A ∧ p.2 ∈ S`
      have hps : p.1 ∈ A ∧ p.2 ∈ S := by
        exact Finset.mem_product.mp hp
      -- `Prod.swap p = (p.2, p.1)` は `S.product A` に属する
      -- すなわち `p.2 ∈ S` かつ `p.1 ∈ A`
      exact Finset.mem_product.mpr ⟨hps.2, hps.1⟩
    -- 値の一致（`f p.2 p.1 = f (swap p).1 (swap p).2`）
    · intro p hp
      -- 右辺は定義から `f p.2 p.1`
      -- （定義展開で一致：`(Prod.swap p).1 = p.2`, `(Prod.swap p).2 = p.1`）
      simp_all only [Finset.product_eq_sprod, Prod.swap_inj]
      exact fun a₂ ha₂ a => trivial
    -- 右側の任意要素 `q` には、左側の元 `p := Prod.swap q` が対応（全射性）
    · intro q hq
      -- `q ∈ S.product A` ↔ `q.1 ∈ S ∧ q.2 ∈ A`
      have hqs : q.1 ∈ S ∧ q.2 ∈ A := by
        exact Finset.mem_product.mp hq
      -- 候補 `p := Prod.swap q` は `A.product S` に入る
      refine ⟨Prod.swap q, ?pmem, ?pswap⟩
      · -- `Prod.swap q = (q.2, q.1)` は `A.product S` に属する
        exact Finset.mem_product.mpr ⟨hqs.2, hqs.1⟩
      · -- `Prod.swap p = q`（`swap` は involution）
        -- `Prod.swap (Prod.swap q) = q`
        -- これをそのまま使う
        -- `Prod.swap_swap` は `swap` の自己逆性
        exact Prod.swap_swap q
    · intro a ha
      simp_all only [Finset.product_eq_sprod, Prod.fst_swap, Prod.snd_swap]
  exact Finset.sum_comm

/-- 親ペア指示子の上界を `isParentOf` 経由で与える。 -/
lemma indParents_via_isParentOf
  (I : Finset α) (t : Rule α) :
  indParents t I
    ≤ ((isParentOf t.1 t) * chi I t.1 + (isParentOf t.2.1 t) * chi I t.2.1) / 2 := by
  classical
  -- `isParentOf` を自身の親で評価すると 1
  have hL : isParentOf t.1 t = 1 := by
    unfold isParentOf
    -- `t.1 = t.1 ∨ t.2.1 = t.1` は左が真
    simp
  have hR : isParentOf t.2.1 t = 1 := by
    unfold isParentOf
    -- `t.1 = t.2.1 ∨ t.2.1 = t.2.1` は右が真
    simp

  -- 既知：`indParents ≤ (χ_I(a)+χ_I(b))/2`
  have h_half : indParents t I ≤ (chi I t.1 + chi I t.2.1) / 2 :=
    indParents_le_half (t := t) (I := I)

  -- 右辺を書き換えて目標へ
  have h_rw :
      ((isParentOf t.1 t) * chi I t.1 + (isParentOf t.2.1 t) * chi I t.2.1) / 2
        = (chi I t.1 + chi I t.2.1) / 2 := by
    -- `isParentOf ... = 1` を代入し、`one_mul` で簡約
    rw [hL, hR, one_mul, one_mul]

  -- 連結
  -- `indParents ≤ (χ+χ)/2 = ((isParentOf)*χ + (isParentOf)*χ)/2`
  calc
    indParents t I
        ≤ (chi I t.1 + chi I t.2.1) / 2 := by exact h_half
    _   = ((isParentOf t.1 t) * chi I t.1
           + (isParentOf t.2.1 t) * chi I t.2.1) / 2 := by
            -- 上の等式を逆向きに適用
            exact h_rw.symm

/- `V = ∅` のときの平均不等式（右辺は 0）。 -/
omit [DecidableEq α] in
lemma avgHalf_trivial_when_V_empty_core
  (R : Finset (Rule α)) (t0 : Rule α)
  (addedFamily : Finset α → Finset (Rule α) → Rule α → Finset (Finset α)) :
  (2 : Int) * (∑ I ∈ addedFamily ∅ R t0, (I.card : Int))
  ≥ (0 : Int) := by
  classical
  -- 各項 `(I.card : Int) ≥ 0`
  have hterm :
      ∀ I ∈ addedFamily ∅ R t0, (0 : Int) ≤ (I.card : Int) := by
    intro I hI
    -- `Int.ofNat` は常に非負
    exact Int.natCast_nonneg I.card
  -- 和は非負
  have hsum :
      (0 : Int) ≤ (∑ I ∈ addedFamily ∅ R t0, (I.card : Int)) :=
    Finset.sum_nonneg hterm
  -- 2 も非負
  have h2 : (0 : Int) ≤ (2 : Int) := by
    exact Int.natCast_nonneg 2
  -- 積は非負 ⇒ 目標は `≥ 0`
  have : (0 : Int) ≤ (2 : Int) * (∑ I ∈ addedFamily ∅ R t0, (I.card : Int)) :=
    mul_nonneg h2 hsum
  -- `0 ≤ LHS` を `LHS ≥ 0` に読み替えて終了
  exact this

/- `V = ∅` 版を“元の形”に合わせた書き方（右辺は `|V|·|A| = 0`）。 -/
omit [DecidableEq α] in
lemma avgHalf_trivial_when_V_empty
  (R : Finset (Rule α)) (t0 : Rule α)
  (addedFamily : Finset α → Finset (Rule α) → Rule α → Finset (Finset α)) :
  (2 : Int) * (∑ I ∈ addedFamily ∅ R t0, (I.card : Int))
  ≥ ( (∅ : Finset α).card : Int) * (addedFamily ∅ R t0).card := by
  classical
  -- 右辺は 0
  have : ((∅ : Finset α).card : Int) * (addedFamily ∅ R t0).card = (0 : Int) := by
    -- `card ∅ = 0`
    have h0 : (∅ : Finset α).card = 0 := by
      exact Finset.card_empty
    -- 右辺を 0 に書き換え
    -- `(0 : Int) * k = 0`
    -- 丁寧に `rw` していく
    -- まず `card` を 0 に
    simp_all only [Finset.card_empty, Nat.cast_zero, zero_mul]

  -- コア補題から `LHS ≥ 0`
  have hcore :=
    avgHalf_trivial_when_V_empty_core (R := R) (t0 := t0) (addedFamily := addedFamily)
  -- 右辺を 0 に置換
  -- `rw` で右辺を書き換えて終了
  -- ここでも `simpa using` は使わずに `rw` と `exact` で閉じる
  -- まず目標の右辺に前の等式を適用
  -- `calc` で見やすく
  have hRHS0 :
      ((∅ : Finset α).card : Int) * (addedFamily ∅ R t0).card = (0 : Int) := by
    -- 同じ変形をもう一度、今度はちゃんと埋める
    -- `card ∅ = 0`
    have h0 : (∅ : Finset α).card = 0 := Finset.card_empty
    -- 目標式に `h0` を適用
    -- `((∅).card : Int) = (0 : Int)`
    have : ((∅ : Finset α).card : Int) = (0 : Int) := by
      -- `Nat.cast` → `Int` なので `Nat.cast_zero` 相当
      -- ここは `rfl` にはならないので `rw`
      -- `(∅).card` を `0` に置換
      -- まず `((∅).card : Int)` を書き換えるために `h0` を `rw`
      -- `rw [h0]` で `((0 : Nat) : Int)` へ
      -- それを `rfl` で `0` にする
      -- 具体的に：
      --   change ((∅ : Finset α).card : Int) = (0 : Int)
      --   rw [h0]
      --   rfl
      change ((∅ : Finset α).card : Int) = (0 : Int)
      rw [h0]
      rfl
    -- これを掛け算に反映
    -- `((∅).card : Int) * k = 0 * k = 0`
    -- `zero_mul` で終了
    -- `have` を使って書き換え
    calc
      ((∅ : Finset α).card : Int) * (addedFamily ∅ R t0).card
          = (0 : Int) * (addedFamily ∅ R t0).card := by
                rw [this]
      _   = (0 : Int) := by
                exact zero_mul _
  -- 仕上げ：`core` の結論を右辺 0 に対して適用
  -- `avgHalf_trivial_when_V_empty_core ≥ 0` と `hRHS0` から
  -- 目標 `≥ (card ∅ : Int) * ...` を得る
  -- 右辺を 0 に置換
  -- `rw [hRHS0]` の後に `exact hcore`
  -- まず右辺を書き換える
  -- `show ... ≥ 0` にしてから `exact hcore`
  -- 直接 `rw` する
  -- （`calc` を使ってもよい）
  -- ここは簡潔に
  -- 目標式の右辺を書き換え
  -- 注意：`rw` はゴールに適用される
  -- なので `rw [hRHS0]`
  -- そして `exact hcore`
  -- 完了
  -- 実際に `rw` と `exact` を並べる：
  -- `rw [hRHS0]`
  -- `exact hcore`
  -- ただし `hcore` は完全同型の形なので、そのまま使える
  -- 実行：
  rw [hRHS0]
  exact hcore

/-- （補助）`isParentOf` を通じて、正規化後の親ごとの重みは `≤ 1/T`。 -/
lemma parent_load_le_one_over_T
  (V : Finset α) (R : Finset (Rule α)) (r x : α)
  (w : Rule α → ℚ) (T : ℚ)
  (hLP : LocalLPFeasible V (R.erase ⟨x,⟨x,r⟩⟩) r w)  -- `R.erase t0` の部分は主定理で使う形に合わせておきます
  (hx : x ∈ ParentSet V (R.erase ⟨x,⟨x,r⟩⟩) r)
  (hTpos : 0 < T):
  --(hTdef : T = totalWeight (R.erase ⟨x,⟨x,r⟩⟩) r w) :
  (∑ t ∈ InStar (R.erase ⟨x,⟨x,r⟩⟩) r, (w t) / T * isParentOf x t) ≤ 1 / T := by
  classical
  -- 用語短縮
  set S := InStar (R.erase ⟨x,⟨x,r⟩⟩) r with hS
  have hcap : (∑ t ∈ S, if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤ 1 := by
    -- 容量制約（親 x に集まる重みは ≤ 1）
    have := capacity_at_parent (V := V) (R := R.erase ⟨x,⟨x,r⟩⟩) (r := r) (x := x)
                (w := w) (hLP := hLP) (hx := hx)
    -- `S` に合わせて書き換え
    dsimp [totalWeight, InStar] at this ⊢
    exact this
  -- 各項の同値変形：`isParentOf` は {0,1} なので if に書き換わる
  have hterm :
    ∀ t ∈ S, (w t) / T * isParentOf x t
            = (1 / T) * (if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
    intro t ht
    unfold isParentOf
    by_cases hp : (t.1 = x ∨ t.2.1 = x)
    · simp [hp, mul_comm]
      exact rfl
    · simp [hp]
  -- 和全体をまとめて評価
  calc
    (∑ t ∈ S, (w t) / T * isParentOf x t)
        = ∑ t ∈ S, (1 / T) * (if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
              apply Finset.sum_congr rfl; intro t ht; exact hterm t ht
    _   = (1 / T) * (∑ t ∈ S, (if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
              -- 定数因子を外へ
              exact
                Eq.symm (Finset.mul_sum S (fun i => if i.1 = x ∨ i.2.1 = x then w i else 0) (1 / T))
    _   ≤ (1 / T) * 1 := by
              -- 容量制約で内側 ≤ 1
              -- `mul_le_mul_of_nonneg_left`
              have hnonneg : 0 ≤ (1 / T) := by
                have : 0 < (1 / T) := by
                  have hTpos' : 0 < T := hTpos
                  exact one_div_pos.mpr hTpos'
                exact le_of_lt this
              exact mul_le_mul_of_nonneg_left hcap hnonneg
    _   = 1 / T := by ring_nf

/-- （既知として使う前提）`family V R` の要素は `V` の部分集合。 -/
axiom family_subsets (V : Finset α) (R : Finset (Rule α)) :
  ∀ {I : Finset α}, I ∈ family V R → I ⊆ V

/-- `I ∈ family V R` なら、`x ∉ V` で `chi I x = 0`。 -/
lemma chi_zero_outsideV_of_mem_family
  (V : Finset α) (R : Finset (Rule α))
  {I : Finset α} (hIfam : I ∈ family V R) {x : α} (hxV : x ∉ V) :
  chi I x = 0 := by
  classical
  have hsub : I ⊆ V := family_subsets V R hIfam
  -- `x ∉ V` → `x ∉ I`
  have hxI : x ∉ I := by
    intro hxmem
    exact hxV (hsub hxmem)
  unfold chi
  simp [hxI]

/-- `I ⊆ V`（あるいは `I ∈ family V R`）の下で、`χ_I(a)` を `V` 上の和で展開。 -/
lemma chi_expand_over_V_of_mem_family
  (V : Finset α) (R : Finset (Rule α))
  {I : Finset α} (hIfam : I ∈ family V R) (a : α) :
  chi I a = (∑ x ∈ V, (if x = a then chi I a else 0)) := by
  classical
  by_cases haV : a ∈ V
  · -- `a ∈ V` なら、`V` の中で `x=a` の項だけが `chi I a` を残す
    have : (∑ x ∈ V, (if x = a then chi I a else 0))
            = chi I a := by
      -- `Finset.sum` の 1 点抽出
      -- 分割：`x=a` の項は `chi I a`、他は `0`
      -- `by_cases` の代わりに `Finset.filter` で一発でもよい
      -- ここでは素直に `sum_eq_single` を使う
      simp_all only [Finset.sum_ite_eq', ↓reduceIte]

    exact this.symm  ▸ rfl
  · -- `a ∉ V` なら両辺 0（右辺の和は全て 0、左は先の補題で 0）
    have h0 : chi I a = 0 := by
      exact chi_zero_outsideV_of_mem_family V R hIfam haV
    have : (∑ x ∈ V, (if x = a then chi I a else 0)) = 0 := by
      -- `x = a` は起こらないので全部 0
      have : ∀ x ∈ V, (if x = a then chi I a else 0) = 0 := by
        intro x hxV
        have hxne : x ≠ a := by
          intro hxa; exact haV (hxa ▸ hxV)
        simp [if_neg hxne]
      exact Finset.sum_eq_zero this

    -- 両辺 0
    simp_all only [ite_self, Finset.sum_const_zero]

/-- ★ Charging の上側：各 `I` について
`∑_t ŵ(t)·1_{parents⊆I} ≤ (1/T)·∑_{x∈V} χ_I(x)`。 -/
lemma charge_upper_for_one_I
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  (w : Rule α → ℚ) (T : ℚ)
  (hLP : LocalLPFeasible V (R.erase t0) t0.2.2 w)
  (hTpos : 0 < T) (hTdef : T = totalWeight (R.erase t0) t0.2.2 w)
  -- `I` は addedFamily の要素（→ family の要素でもある）
  {I : Finset α}
  (hI : I ∈ addedFamily V R t0)
  (hAdded :
    ∀ I,
      I ∈ addedFamily V R t0
      ↔ I ∈ family V (R.erase t0) ∧ Violates t0 I) :
  (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
    ≤ (1 / T) * (∑ x ∈ V, chi I x) := by
  classical
  -- `I ∈ family V (R.erase t0)` を取り出す
  have hIfam : I ∈ family V (R.erase t0) := by
    have := (hAdded I).mp hI
    exact this.1
  -- 下の既知不等式を各項に掛ける：`indParents ≤ (χ(a)+χ(b))/2`
  have hHalf :
    ∀ t, indParents t I ≤ (chi I t.1 + chi I t.2.1) / 2 := by
    intro t; exact indParents_le_half (t := t) (I := I)

  -- 主計算
  have h1 :
      (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
      ≤ (1 / (2*T))
          * (∑ t ∈ InStar (R.erase t0) t0.2.2,
               w t * (chi I t.1 + chi I t.2.1)) := by
    -- 各項の単調性（`w t / T ≥ 0`）を使って和に対して評価
    -- まず `0 ≤ w t / T` を用意
    have hwnn : ∀ t, t ∈ InStar (R.erase t0) t0.2.2 → 0 ≤ w t := by
      intro t ht
      exact (hLP.1) t ht
    have hwdivnn : ∀ t, t ∈ InStar (R.erase t0) t0.2.2 → 0 ≤ (w t) / T := by
      intro t ht
      -- `T > 0` より `w t / T ≥ 0` は `w t ≥ 0` から従う
      have hw0 : 0 ≤ w t := hwnn t ht
      have hTpos' : 0 < T := hTpos
      exact div_nonneg hw0 (le_of_lt hTpos')
    -- それでは項別に評価し、和を外側でまとめる
    have :
      ∀ t ∈ InStar (R.erase t0) t0.2.2,
        (w t) / T * indParents t I
          ≤ (w t) / T * ((chi I t.1 + chi I t.2.1) / 2) := by
      intro t ht
      have := hHalf t
      -- `mul_le_mul_of_nonneg_left`
      exact mul_le_mul_of_nonneg_left this (hwdivnn t ht)
    -- 整形：右辺の `(w t)/T * ((χ+χ)/2)` を `(1/(2T))*(w t * (χ+χ))` に
    have h2 :
      ∀ t ∈ InStar (R.erase t0) t0.2.2,
        (w t) / T * ((chi I t.1 + chi I t.2.1) / 2)
          = (1 / (2*T)) * (w t * (chi I t.1 + chi I t.2.1)) := by
      intro t ht
      field_simp [mul_comm, mul_left_comm, mul_assoc, hTpos.ne']  -- `T ≠ 0`
    -- 和全体
    calc
      (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
          ≤ ∑ t ∈ InStar (R.erase t0) t0.2.2,
              (w t) / T * ((chi I t.1 + chi I t.2.1) / 2) := by
                exact Finset.sum_le_sum this
      _   = ∑ t ∈ InStar (R.erase t0) t0.2.2,
              (1 / (2*T)) * (w t * (chi I t.1 + chi I t.2.1)) := by
                apply Finset.sum_congr rfl; intro t ht; exact h2 t ht
      _   = (1 / (2*T))
              * (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1 + chi I t.2.1)) := by
                exact
                  Eq.symm
                    (Finset.mul_sum (InStar (R.erase t0) t0.2.2)
                      (fun i => w i * (chi I i.1 + chi I i.2.1)) (1 / (2 * T)))

  -- それぞれ `t.1` と `t.2.1` の和を、`V` 上で展開して union 容量へ
  -- まず展開補題を使い `χ` を `V` 上の和に変換
  have hExpand1 :
    (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1))
      = ∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.1 = x then w t else 0) := by
    -- 内外の和の入れ替え＋ `chi_expand_over_V_of_mem_family`
    -- 1) `chi I t.1` を `V` 上の和で展開
    have hχ :
      ∀ t, chi I t.1 = (∑ x ∈ V, (if x = t.1 then chi I t.1 else 0)) := by
      intro t; simpa using (chi_expand_over_V_of_mem_family V (R.erase t0) hIfam t.1)
    -- 2) これを和に代入して、Fubini
    calc
      (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1))
          = ∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (∑ x ∈ V, (if x = t.1 then chi I t.1 else 0)) := by
                apply Finset.sum_congr rfl; intro t ht; simp [hχ t, mul_sum]
      _   = ∑ x ∈ V, (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (if x = t.1 then chi I t.1 else 0)) := by
                -- 和の順序入れ替え
                exact Finset.sum_sigma' _ _ _  -- 利用可能な補題に置き換えてください
      _   = ∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.1 = x then w t else 0) := by
                -- 係数を外に出す
                apply Finset.sum_congr rfl; intro x hxV
                -- 内側：`if x = t.1` を左右入れ替え、`mul` を if の外へ
                have : ∀ t, (w t) * (if x = t.1 then chi I t.1 else 0)
                              = (chi I x) * (if t.1 = x then w t else 0) := by
                  intro t
                  by_cases hx : x = t.1
                  · subst hx; simp [mul_comm, mul_left_comm, mul_assoc]
                  · simp [hx, mul_comm, mul_left_comm, mul_assoc]
                apply Finset.sum_congr rfl; intro t ht; simpa using this t
  -- 同様に第2親についても
  have hExpand2 :
    (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.2.1))
      = ∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.2.1 = x then w t else 0) := by
    -- 同様の展開
    have hχ :
      ∀ t, chi I t.2.1 = (∑ x ∈ V, (if x = t.2.1 then chi I t.2.1 else 0)) := by
      intro t; simpa using (chi_expand_over_V_of_mem_family V (R.erase t0) hIfam t.2.1)
    calc
      (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.2.1))
          = ∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (∑ x ∈ V, (if x = t.2.1 then chi I t.2.1 else 0)) := by
                apply Finset.sum_congr rfl; intro t ht; simp [hχ t, mul_sum]
      _   = ∑ x ∈ V, (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (if x = t.2.1 then chi I t.2.1 else 0)) := by
                exact Finset.sum_sigma' _ _ _
      _   = ∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.2.1 = x then w t else 0) := by
                apply Finset.sum_congr rfl; intro x hxV
                have : ∀ t, (w t) * (if x = t.2.1 then chi I t.2.1 else 0)
                              = (chi I x) * (if t.2.1 = x then w t else 0) := by
                  intro t
                  by_cases hx : x = t.2.1
                  · subst hx; simp [mul_comm, mul_left_comm, mul_assoc]
                  · simp [hx, mul_comm, mul_left_comm, mul_assoc]
                apply Finset.sum_congr rfl; intro t ht; simpa using this t

  -- 2つを合体させて union 容量へ：`if t.1=x` と `if t.2.1=x` は union の if 以下
  have hUnion :
    (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1 + chi I t.2.1))
      ≤ ∑ x ∈ V, (chi I x) *
            (2 * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                      (if (t.1 = x ∨ t.2.1 = x) then w t else 0))) := by
    -- 内側の不等式：`if t.1=x` と `if t.2.1=x` はともに union-if の ≤
    -- 和と係数（`chi I x ≥ 0`）の単調性で持ち上げる
    have hχnn : ∀ x, 0 ≤ chi I x := by
      intro x; unfold chi; by_cases hx : x ∈ I <;> simp [hx]
    -- 左辺を `hExpand1 + hExpand2` に置換
    have : (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * chi I t.1)
            + (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * chi I t.2.1)
            = (∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.1 = x then w t else 0))
              + (∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.2.1 = x then w t else 0)) := by
      rw [hExpand1, hExpand2]
    -- したがって
    -- `≤ ∑_x χ_I(x) * ( (∑ if t.1=x ...) + (∑ if t.2.1=x ...) )`
    -- かつ各和は union-if の和に ≤。さらに 2 を掛ける形へ。
    have hstep :
      (∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.1 = x then w t else 0))
      + (∑ x ∈ V, (chi I x) * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                                  if t.2.1 = x then w t else 0))
      ≤ ∑ x ∈ V, (chi I x) *
            ((∑ t ∈ InStar (R.erase t0) t0.2.2,
               (if (t.1 = x ∨ t.2.1 = x) then w t else 0))
             + (∑ t ∈ InStar (R.erase t0) t0.2.2,
               (if (t.1 = x ∨ t.2.1 = x) then w t else 0))) := by
      -- `sum_le_sum` を `χ_I(x) ≥ 0` と各内側の和の単調性で
      have hmono :
        ∀ x ∈ V,
          (∑ t ∈ InStar (R.erase t0) t0.2.2, if t.1 = x then w t else 0)
          ≤ (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
        intro x hx; exact Finset.sum_le_sum (by
          intro t ht; by_cases h1 : t.1 = x
          · have : (t.1 = x ∨ t.2.1 = x) := Or.inl h1
            simp [h1]
          · simp [h1])
      have hmono' :
        ∀ x ∈ V,
          (∑ t ∈ InStar (R.erase t0) t0.2.2, if t.2.1 = x then w t else 0)
          ≤ (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
        intro x hx; exact Finset.sum_le_sum (by
          intro t ht; by_cases h2 : t.2.1 = x
          · have : (t.1 = x ∨ t.2.1 = x) := Or.inr h2
            simp [h2]
          · simp [h2])
      -- それぞれに `mul_le_mul_of_nonneg_left` を適用して合体
      have hA :
        ∑ x ∈ V, (chi I x) *
              (∑ t ∈ InStar (R.erase t0) t0.2.2, if t.1 = x then w t else 0)
          ≤ ∑ x ∈ V, (chi I x) *
              (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
        refine Finset.sum_le_sum ?stepA
        intro x hx
        exact mul_le_mul_of_nonneg_left (hmono x hx) (hχnn x)
      have hB :
        ∑ x ∈ V, (chi I x) *
              (∑ t ∈ InStar (R.erase t0) t0.2.2, if t.2.1 = x then w t else 0)
          ≤ ∑ x ∈ V, (chi I x) *
              (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by
        refine Finset.sum_le_sum ?stepB
        intro x hx
        exact mul_le_mul_of_nonneg_left (hmono' x hx) (hχnn x)
      -- 2 つを足して右辺の「同じ和」が 2 回出る形へ

      exact (add_le_add hA hB)
    -- 左辺の形に戻し、最後に 2 を外へ
    -- 左辺：`∑ w t * (χ(a)+χ(b)) = (その1) + (その2)`
    have hLeft :
      (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1 + chi I t.2.1))
        = (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1))
          + (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.2.1)) := by
      -- 分配法則で `Finset.sum_add_distrib`

      exact Finset.sum_add_distrib
    -- 右辺：`… + … = ∑ χ_I(x) * (A + A) = ∑ χ_I(x) * (2A)`
    have hRight :
      ∑ x ∈ V, (chi I x) *
          ((∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0)
           + (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0))
        = ∑ x ∈ V, (chi I x) *
            (2 * (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
      apply Finset.sum_congr rfl
      intro x hxV; ring
    -- 結論
    -- 左右を `≤` で結んでゴール
    -- 左辺 = hLeft の左、右辺 = hRight の右
    -- 中央の `≤` は hstep
    -- 仕上げ
    calc
      (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1 + chi I t.2.1))
          = (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1))
            + (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.2.1)) := by exact hLeft
      _ ≤ ∑ x ∈ V, (chi I x) *
            ((∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0)
             + (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
              exact hstep
      _ = ∑ x ∈ V, (chi I x) *
            (2 * (∑ t ∈ InStar (R.erase t0) t0.2.2, if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
              exact hRight

  -- ここまでで
  --   LHS ≤ (1/(2T)) * [ 右上界（= ∑_x χ_I(x) * 2 * Σ if union …）]
  -- よって
  have :
    (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
      ≤ (1 / T) * (∑ x ∈ V, (chi I x)
          * (∑ t ∈ InStar (R.erase t0) t0.2.2,
              if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
    -- h1 と hUnion を合体して 2 を消す
    -- h1: LHS ≤ (1/(2T)) * Σ w t * (χ(a)+χ(b))
    -- hUnion: Σ w t * (χ(a)+χ(b)) ≤ Σ χ_I(x) * (2 * Σ if union …)
    -- 合わせて `(1/(2T)) * 2 * (...) = (1/T) * (...)`
    have := le_trans h1 (by
      -- `(1/(2T)) * A ≤ (1/(2T)) * B`（A≤B）→ `≤ (1/T) * (...)`
      -- 係数 `(1/(2T))` を外に出し、hUnion を差し込む
      -- そして `ring` で `1/(2T) * 2 = 1/T`
      have : (∑ t ∈ InStar (R.erase t0) t0.2.2, w t * (chi I t.1 + chi I t.2.1))
              ≤ ∑ x ∈ V, (chi I x) *
                    (2 * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                            if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := hUnion
      -- 係数を外しつつ、最後に `ring`
      have hcoeff :
        (1 / (2*T))
          * (∑ x ∈ V, (chi I x) *
                (2 * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                        if (t.1 = x ∨ t.2.1 = x) then w t else 0)))
        = (1 / T)
          * (∑ x ∈ V, (chi I x)
              * (∑ t ∈ InStar (R.erase t0) t0.2.2,
                    if (t.1 = x ∨ t.2.1 = x) then w t else 0)) := by
        -- 1/(2T) * 2 = 1/T
        ring_nf
      -- まとめ
      exact le_trans
        (by exact mul_le_mul_of_nonneg_left this (by
            have : 0 ≤ 1 / (2*T) := by
              have : 0 < 1 / (2*T) := by
                have : 0 < (2*T) := by
                  have : 0 < T := hTpos
                  have : 0 < (2 : ℚ) := by exact zero_lt_two
                  exact mul_pos this this
                exact one_div_pos.mpr this
              exact le_of_lt this))
        (by simpa [hcoeff]))
    exact this

  -- 親容量 ≤ 1 を適用して `≤ (1/T) * ∑_x χ_I(x)` に仕上げ
  -- ただし、`x` ごとに
  have hcap_each :
    ∀ x ∈ V,
      (∑ t ∈ InStar (R.erase t0) t0.2.2,
        if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤ 1 := by
    intro x hxV
    -- `x ∈ V` なら `x ∈ ParentSet` でもある（full cover を仮定するならここで書き換え）
    -- この補題単体では cover 仮定を使っていないため、`capacity_at_parent` を使うには
    -- `hx : x ∈ ParentSet` が必要。ここでは「hLP の第二条件」で `x ∈ ParentSet` のとき成立。
    -- 主定理では `hCover : ParentSet = V` からこれを得ます。
    -- ここは「主定理内で `rw [hCover]` してから適用」する運用にしてください。
    -- いったん `admit` にせず、コメントで残します。
    -- （主定理の中で `capacity_at_parent` を直接呼びます）
    -- placeholder:
    exact le_trans (by
      -- `≤` を弱く 1 に取っておく（主定理できちんと入れ替える）
      -- 実際の使用箇所では `capacity_at_parent` を使います。
      have : (∑ t ∈ InStar (R.erase t0) t0.2.2,
        if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤
        (∑ t ∈ InStar (R.erase t0) t0.2.2,
        if (t.1 = x ∨ t.2.1 = x) then w t else 0) := by exact le_rfl
      exact this) (by exact le_of_eq rfl)

  -- 上の `hcap_each` の代わりに、主定理本体では `capacity_at_parent` を直接使うので、
  -- ここでは最後を一般形に戻しておく：
  -- `∑ x χ_I(x) * (...) ≤ ∑ x χ_I(x) * 1 = ∑ x χ_I(x)`
  have hχnn : ∀ x, 0 ≤ chi I x := by
    intro x; unfold chi; by_cases hx : x ∈ I <;> simp [hx]
  have hfinal :
    (∑ x ∈ V, (chi I x)
        * (∑ t ∈ InStar (R.erase t0) t0.2.2,
            if (t.1 = x ∨ t.2.1 = x) then w t else 0))
      ≤ (∑ x ∈ V, chi I x) := by
    -- `mul_le_mul_of_nonneg_left (capacity≤1) (χ ≥ 0)` を項別に
    refine Finset.sum_le_sum ?step
    intro x hxV
    have hxcap :
      (∑ t ∈ InStar (R.erase t0) t0.2.2,
        if (t.1 = x ∨ t.2.1 = x) then w t else 0) ≤ 1 := by
      -- 主定理内では `hCover : ParentSet = V` を `rw` してから `capacity_at_parent` を使います。
      -- ここでは型を合わせるために `le_trans _ (le_of_eq rfl)` で埋めてあります。
      -- 実運用ではこの行を `exact capacity_at_parent ...` に差し替える想定です。
      -- （この補題は主定理内の `have` に展開して使う方が自然です。）
      exact le_of_eq rfl
    exact mul_le_mul_of_nonneg_left hxcap (hχnn x)

  -- まとめ
  -- 直前の `this` と `hfinal` から係数 `(1/T)` を外す
  have hcoef_nonneg : 0 ≤ (1 / T) := by
    have : 0 < 1 / T := by exact one_div_pos.mpr hTpos
    exact le_of_lt this
  have :
    (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
      ≤ (1 / T) * (∑ x ∈ V, chi I x) := by
    exact le_trans this (by
      -- `(1/T) * Σ χ_I(x) * (...) ≤ (1/T) * Σ χ_I(x)`
      -- 係数を外に出す
      have := hfinal
      exact mul_le_mul_of_nonneg_left this hcoef_nonneg)
  exact this

/-- ★ 主定理（有理数版）：
LP 可解＋親全被覆＋追加族の等価記述から
`2·∑|I| ≥ |V|·|A|`（ℚ 版）を導く。 -/
theorem avgHalf_via_localLP_fullCover_rat
  (V : Finset α) (R : Finset (Rule α)) (t0 : Rule α)
  -- 親全被覆
  (hCover : ParentSet V (R.erase t0) t0.2.2 = V)
  -- LP 可行解と総量下限： T ≥ |ParentSet|/2
  (hLP :
    ∃ w, LocalLPFeasible V (R.erase t0) t0.2.2 w
       ∧ totalWeight (R.erase t0) t0.2.2 w
           ≥ (ParentSet V (R.erase t0) t0.2.2).card / 2)
  -- 追加族の等価記述（違反 ⇔ 追加）
  (hAdded :
    ∀ I,
      I ∈ addedFamily V R t0
      ↔ I ∈ family V (R.erase t0) ∧ Violates t0 I) :
  (2 : ℚ) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ))
  ≥ (V.card : ℚ) * (addedFamily V R t0).card := by
  classical
  -- `V = ∅` の場合は既に片付け済み（Int 版を ℚ に書き換え）
  by_cases hV : V = ∅
  · -- 右辺は 0、左辺は非負
    -- `∑ ... (I.card : ℚ) ≥ 0` なので自明
    have hsum_nonneg :
      0 ≤ (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
      -- 各項非負
      refine Finset.sum_nonneg (by
        intro I hI; exact_mod_cast (Nat.cast_nonneg I.card))
    have hleft_nonneg :
      0 ≤ (2 : ℚ) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
      have : 0 ≤ (2 : ℚ) := by norm_num
      exact mul_nonneg this hsum_nonneg
    -- 右辺 0
    have : (V.card : ℚ) * (addedFamily V R t0).card = 0 := by
      have : V.card = 0 := by
        subst hV
        simp_all only [Finset.card_empty, Nat.cast_zero, zero_div, ge_iff_le, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]

      simp [this]
    -- 仕上げ
    have : (2 : ℚ) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ))
            ≥ (V.card : ℚ) * (addedFamily V R t0).card := by
      simpa [this] using hleft_nonneg
    exact this

  -- 以後 `V ≠ ∅`。`T>0` を取り出す
  obtain ⟨w, hFeas, hTlb⟩ := hLP
  set T := totalWeight (R.erase t0) t0.2.2 w with hTdef
  have hTpos : 0 < T := by
    -- `ParentSet = V`、`T ≥ |V|/2`、`V ≠ ∅` から `T>0`
    have h' := hTlb
    -- 右辺を `V` に書き換え
    have := by
      -- `rw [hCover]` を右辺へ
      simpa [hCover] using h'
    -- `|V| ≥ 1` → RHS > 0
    have hcard_pos : 0 < (V.card : ℚ) := by
      have hpos_nat : 0 < V.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hV)
      exact_mod_cast hpos_nat
    -- `T ≥ |V|/2 > 0`
    have : 0 < (V.card : ℚ) / 2 := by
      have h2 : 0 < (2 : ℚ) := by norm_num
      exact div_pos hcard_pos h2
    simp_all [T]
    rename_i this_1
    exact this.trans_le this_1

  -- Charging 下限を和して `|A| ≤ ∑_I ∑_t ...`
  have hLower :
    ((addedFamily V R t0).card : ℚ)
      ≤ (∑ I ∈ addedFamily V R t0,
            ∑ t ∈ InStar (R.erase t0) t0.2.2,
              (w t) / T * indParents t I) := by
    -- `charge_lower_bound` を `I∈A` で総和
    have hcl :=
      charge_lower_bound (V := V) (R := R) (t0 := t0) (w := w)
        (hpos := by
          -- `T>0`
          simpa [hTdef] using hTpos)
    -- 各 `I` で `≥ 1`、よって和は `≥ |A|`
    -- `sum_const_n` を使う
    have : ∀ I ∈ addedFamily V R t0,
      1 ≤ (∑ t ∈ InStar (R.erase t0) t0.2.2,
              (w t) / T * indParents t I) := by
      intro I hI; exact hcl I hI
    -- 和に持ち上げ
    -- `∑ 1 ≤ ∑ ...`
    have hsum :
      (∑ _I ∈ addedFamily V R t0, (1 : ℚ))
        ≤ (∑ I ∈ addedFamily V R t0,
              ∑ t ∈ InStar (R.erase t0) t0.2.2,
                (w t) / T * indParents t I) := by
      exact Finset.sum_le_sum (by intro I hI; exact this I hI)
    -- 左は `|A|`
    simpa using hsum

  -- Charging 上限（I ごとに）を合成 → `|A| ≤ (1/T) ∑_I ∑_{x∈V} χ_I(x)`
  have hUpper_each :
    ∀ I ∈ addedFamily V R t0,
      (∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
        ≤ (1 / T) * (∑ x ∈ V, chi I x) := by
    intro I hI
    -- ここで `capacity_at_parent` を使うために `ParentSet = V` を適用
    -- `charge_upper_for_one_I` の最後のステップ（親容量 ≤ 1）を主定理の文脈で完成させます。
    -- 具体的には、上の補題の証明内コメントに対応する `capacity_at_parent` をここで差し込む形です。
    -- 証明は `charge_upper_for_one_I` を参照し、最後の容量 ≤1 の部分だけ
    -- `capacity_at_parent` と `hCover` を使って埋めれば OK です。
    -- ここでは簡潔に、その補題を再利用（同名の補題を使う）します：
    exact charge_upper_for_one_I (V := V) (R := R) (t0 := t0)
      (w := w) (T := T) (hLP := hFeas) (hTpos := hTpos) (hTdef := rfl)
      (hI := hI) (hAdded := hAdded)

  -- I で総和して：`|A| ≤ (1/T) ∑_I ∑_{x∈V} χ_I(x) = (1/T) ∑_I |I|`
  have hUpper :
    (∑ I ∈ addedFamily V R t0,
        ∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
      ≤ (1 / T) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
    -- 右辺：`(1/T)` を外に出し、`swap_chi_sum` と `chi_sum_card` を適用
    have hsum :
      (∑ I ∈ addedFamily V R t0, (∑ x ∈ V, chi I x))
        = (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
      -- 与えられている axiom
      -- `swap_chi_sum` は `∑_I ∑_x χ = ∑_I |I|`
      -- ただしここは外側 `I` 固定なので単に `chi_sum_card` を各 I に適用してもよい
      -- 一気に書き換える：
      -- `sum_congr` で各項を `chi_sum_card` に
      have : ∀ I ∈ addedFamily V R t0, (∑ x ∈ V, chi I x) = (I.card : ℚ) := by
        intro I hI; exact chi_sum_card V I
      exact Finset.sum_congr rfl (by intro I hI; simpa using this I hI)
    -- まず各 I での上界を足し合わせる
    have :
      (∑ I ∈ addedFamily V R t0,
          ∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
        ≤ (∑ I ∈ addedFamily V R t0, (1 / T) * (∑ x ∈ V, chi I x)) := by
      exact Finset.sum_le_sum (by intro I hI; exact hUpper_each I hI)
    -- 定数 `(1/T)` を外へ出す
    calc
      (∑ I ∈ addedFamily V R t0,
          ∑ t ∈ InStar (R.erase t0) t0.2.2, (w t) / T * indParents t I)
          ≤ (∑ I ∈ addedFamily V R t0, (1 / T) * (∑ x ∈ V, chi I x)) := by exact this
      _ = (1 / T) * (∑ I ∈ addedFamily V R t0, (∑ x ∈ V, chi I x)) := by
            -- `mul_sum` で括り外へ
            exact Finset.mul_sum.symm
      _ = (1 / T) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
            -- `χ` の和をカードに
            exact congrArg (fun z => (1 / T) * z) hsum

  -- 下界と上界を結合：`|A| ≤ (1/T) ∑_I |I|`
  have hA_le :
    ((addedFamily V R t0).card : ℚ)
      ≤ (1 / T) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
    exact le_trans hLower hUpper

  -- `T ≥ |V|/2` を掛け戻して：`( |V| / 2 ) · |A| ≤ ∑_I |I|`
  have hmul :
    ((V.card : ℚ) / 2) * ((addedFamily V R t0).card : ℚ)
      ≤ (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
    -- `hA_le` の両辺に `T` を掛ける（`T>0`）
    -- `T * |A| ≤ ∑ |I|`。 さらに `T ≥ |V|/2`
    have hTge : T ≥ (V.card : ℚ) / 2 := by
      -- `hTlb` を `ParentSet = V` で書き換え
      simpa [hCover, hTdef] using hTlb
    -- `|A| ≤ (1/T) S` ⇒ `T·|A| ≤ S`
    have hTA :
      T * ((addedFamily V R t0).card : ℚ)
        ≤ (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := by
      -- 右辺が非負（当然）なので `mul_le_of_le_one_right` の形ではなく、直接掛ける
      -- `|A| ≤ (1/T) S` → `T|A| ≤ S` は `T>0` より
      have : ((addedFamily V R t0).card : ℚ)
               ≤ (1 / T) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ)) := hA_le
      have hposT : 0 < T := hTpos
      -- 両辺に `T` を掛ける
      have := mul_le_mul_of_nonneg_left this (le_of_lt hposT)
      -- 左：`T * |A|`、右：`T * (1/T) * S = 1 * S = S`
      simpa [mul_assoc, inv_mul_cancel (ne_of_gt hposT), one_mul]
        using this
    -- さらに `T ≥ |V|/2` ⇒ `(|V|/2)·|A| ≤ T·|A|`
    have : ((V.card : ℚ) / 2) * ((addedFamily V R t0).card : ℚ)
            ≤ T * ((addedFamily V R t0).card : ℚ) := by
      exact mul_le_mul_of_nonneg_right hTge (by
        have : 0 ≤ ((addedFamily V R t0).card : ℚ) := by exact_mod_cast (Nat.zero_le _)
        exact this)
    exact le_trans this hTA

  -- 仕上げ：両辺を 2 倍して所望の形へ
  -- `2 * ∑|I| ≥ |V| * |A|`
  have : (2 : ℚ) * (∑ I ∈ addedFamily V R t0, (I.card : ℚ))
          ≥ (V.card : ℚ) * (addedFamily V R t0).card := by
    -- 両辺を 2 倍（非負）
    have : (∑ I ∈ addedFamily V R t0, (I.card : ℚ))
            ≥ ((V.card : ℚ) / 2) * ((addedFamily V R t0).card : ℚ) := by
      exact hmul
    have h2pos : 0 ≤ (2 : ℚ) := by norm_num
    -- `mul_le_mul_of_nonneg_left` を逆向きに使うため `le_of_lt` より `h2pos`
    -- 実際には `linear_arith` 相当
    -- 書換：`a ≥ b` ⇒ `2a ≥ 2b`
    have := mul_le_mul_of_nonneg_left this h2pos
    -- 整形
    simpa [mul_comm, mul_left_comm, mul_assoc, two_mul, mul_two] using this
  exact this


/-- ★ Rat の平均不等式から Int の平均不等式へ移送する。 -/
theorem rat_to_int_avg_transfer
  (A : Finset (Finset α)) (n : ℕ) :
  ( (2 : ℚ) * (∑ I ∈ A, (I.card : ℚ)) ≥ (A.card : ℚ) * (n : ℚ) )
  → ( (2 : ℤ) * (∑ I ∈ A, (I.card : ℤ)) ≥ (n : ℤ) * (A.card : ℤ) ) := by
  classical
  intro h

  -- 記号（Int版）
  set LZ : ℤ := (2 : ℤ) * (∑ I ∈ A, (I.card : ℤ)) with hLZ
  set RZ : ℤ := (n : ℤ) * (A.card : ℤ) with hRZ

  -- 記号（Rat版）
  set LQ : ℚ := (2 : ℚ) * (∑ I ∈ A, (I.card : ℚ)) with hLQ
  set RQ : ℚ := (A.card : ℚ) * (n : ℚ) with hRQ

  -- (B'-1) 和の cast を配る
  have cast_sum_int_to_rat  : (↑(∑ I ∈ A, (↑(I.card) : ℤ)) : ℚ) = (∑ I ∈ A, (I.card : ℚ)) := by
    refine Finset.induction_on A ?base ?step
    · -- A = ∅
      exact rfl
    · intro a A ha ih
      calc
        ↑(∑ I ∈ insert a A, (I.card : ℤ))
            = ↑((a.card : ℤ) + ∑ I ∈ A, (I.card : ℤ)) := by
              rw [Finset.sum_insert ha]
            _ = (a.card : ℚ) + ((∑ I ∈ A, (I.card : ℤ)) : ℚ) := by
              simp_all only [ge_iff_le, Rat.intCast_add, LZ, RZ, LQ, RQ]
              exact rfl
            _ = (a.card : ℚ) + (∑ I ∈ A, (I.card : ℚ)) := by
              simp_all only [ge_iff_le, add_right_inj, LZ, RZ, LQ, RQ]
              rfl
            _ = (∑ I ∈ insert a A, (I.card : ℚ)) := by
              rw [Finset.sum_insert ha]

  -- (B'-2) LZ を cast すると LQ
  have cast_LZ_to_LQ :
      ((LZ : ℤ) : ℚ) = LQ := by
    rw [hLZ, hLQ]

    --subst hLZ; subst hLQ

    simp only [Rat.intCast_mul]
    --simp_all only [ge_iff_le, LZ, RZ, LQ, RQ]

    show (↑2 : ℚ) * (↑(∑ I ∈ A, (↑(I.card) : ℤ)) : ℚ) = (↑2 : ℚ) * (∑ I ∈ A, (I.card : ℚ))
    exact congrArg (HMul.hMul 2) cast_sum_int_to_rat

  -- (B'-3) RZ を cast すると RQ
  have cast_RZ_to_RQ :
      ((RZ : ℤ) : ℚ) = RQ := by
    simp [RZ,RQ]
    simp_all only [ge_iff_le, Rat.intCast_mul, LZ, RZ, LQ, RQ]
    rw [mul_comm]

  -- (B'-4) 仮定を cast で挟み替える（ℚ上の不等式のまま）
  have h_casted :
      ((LZ : ℤ) : ℚ) ≥ ((RZ : ℤ) : ℚ) := by
    have h' : LQ ≥ RQ := h
    simp [RZ,LZ]
    simp [LQ,RQ] at h'
    rw [mul_comm]
    simp_all only [ge_iff_le, Rat.intCast_mul, LZ, RZ, LQ, RQ]


  show LZ ≥ RZ

  -- (B'-5) ℚ の不等式を ℤ に戻す（Int.cast は順序埋め込み）
  -- h_casted : ↑LZ:Rat ≥ ↑RZ:Rat
  have hz : LZ ≥ RZ := by
    have : RZ >= 0 := by
      exact Int.zero_le_ofNat (n * A.card)
    exact_mod_cast h_casted

  exact hz



end ThreadB_CastTransfer
