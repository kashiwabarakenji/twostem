import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Int
import Twostem.General
import Twostem.Basic
import Twostem.ProblemCC
import Twostem.ProblemC
import LeanCopilot

--このファイルの方針は良くないようで、別のアプローチを試みる。古いアプローチ。

open scoped BigOperators
open ThreadC_Fiber
universe u
variable {α : Type u} [DecidableEq α]


lemma B_mem_familyRep_iff_isClosed_R1
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) {B : Finset α} :
  B ∈ familyRep (V := V) (R := R) (Q := Q)
  ↔ B ⊆ Rep (Q := Q) ∧ isClosed (R1 (V := V) (R := R) (Q := Q)) B := by
  classical
  -- familyRep := (Rep Q).powerset.filter (isClosed R1)
  unfold familyRep
  -- powerset.filter の会員条件：B ⊆ Rep ∧ isClosed R1 B
  constructor
  · intro h
    have hb := Finset.mem_filter.mp h
    have hps := Finset.mem_powerset.mp hb.1
    exact ⟨hps, hb.2⟩
  · intro h
    rcases h with ⟨hsub, hcl⟩
    have : B ∈ (Rep (Q := Q)).powerset := by
      exact Finset.mem_powerset.mpr hsub
    exact Finset.mem_filter.mpr ⟨this, hcl⟩

private lemma sum_const_int {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (c : Int) :
  ∑ _ ∈ s, c = (s.card : Int) * c := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hnot : a ∉ s := ha
    have hsum :
      ∑ x ∈ insert a s, c
        = c + ∑ x ∈ s, c := by
      exact Finset.sum_insert ha

    have hcard :
      (Finset.card (insert a s) : Int)
        = (s.card : Int) + 1 := by
      have := Finset.card_insert_of_notMem hnot
      simp_all only [not_false_eq_true, Finset.sum_const, Int.nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, Finset.card_insert_of_notMem]

    calc
      ∑ _ ∈ insert a s, c
          = c + ∑ _ ∈ s, c := hsum
      _   = c + (s.card : Int) * c := by exact congrArg (HAdd.hAdd c) ih
      _   = ((s.card : Int) + 1) * c := by
            have := (Int.add_mul (s.card : Int) 1 c).symm
            -- (s+1)*c = s*c + 1*c
            -- よって c + s*c = (s+1)*c
            -- ここは置換で合わせる
            calc
              c + (s.card : Int) * c
                  = (s.card : Int) * c + c := by exact add_comm _ _
              _   = (s.card : Int) * c + 1 * c := by
                simp_all only [not_false_eq_true, Finset.sum_const, Int.nsmul_eq_mul, Finset.card_insert_of_notMem, Nat.cast_add,Nat.cast_one, one_mul]
              _   = ((s.card : Int) + 1) * c := by exact this
      _   = (Finset.card (insert a s) : Int) * c := by
            rw [hcard]

lemma sum_debt_split_by_familyRep
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  ∑ B ∈ (Rep (Q := Q)).powerset, Debt (V := V) (R := R) (Q := Q) B
  =
  ∑ B ∈ familyRep (V := V) (R := R) (Q := Q), Debt (V := V) (R := R) (Q := Q) B
  + ∑ B ∈ ((Rep (Q := Q)).powerset.filter
            (fun B => B ∉ familyRep (V := V) (R := R) (Q := Q))),
      Debt (V := V) (R := R) (Q := Q) B := by
  classical
  -- 記号短縮
  set S : Finset (Finset α) := (Rep (Q := Q)).powerset
  set P : Finset (Finset α) := familyRep (V := V) (R := R) (Q := Q)
  have hUnion : S.filter (fun B => B ∈ P) ∪ S.filter (fun B => B ∉ P) = S := by
    ext B; constructor
    · intro h
      rcases Finset.mem_union.mp h with h1 | h2
      · exact (Finset.mem_filter.mp h1).1
      · exact (Finset.mem_filter.mp h2).1
    · intro hB
      by_cases hmem : B ∈ P
      · have : B ∈ S.filter (fun B => B ∈ P) := by exact Finset.mem_filter.mpr ⟨hB, hmem⟩
        exact Finset.mem_union.mpr (Or.inl this)
      · have : B ∈ S.filter (fun B => B ∉ P) := by exact Finset.mem_filter.mpr ⟨hB, hmem⟩
        exact Finset.mem_union.mpr (Or.inr this)
  have hDj :
    Disjoint (S.filter (fun B => B ∈ P)) (S.filter (fun B => B ∉ P)) := by
    -- 交わりなし
    refine Finset.disjoint_left.mpr ?_
    intro B h1 h2
    have hmem1 : B ∈ P := (Finset.mem_filter.mp h1).2
    have hmem2 : B ∉ P := (Finset.mem_filter.mp h2).2
    exact hmem2 hmem1
  -- 和の分割：sum over union = sum + sum
  have hSplitSum :
    ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B
      =
    ∑ B ∈ S.filter (fun B => B ∈ P), Debt (V := V) (R := R) (Q := Q) B
    + ∑ B ∈ S.filter (fun B => B ∉ P), Debt (V := V) (R := R) (Q := Q) B := by
    have := Finset.sum_union hDj
      (s₁ := S.filter (fun B => B ∈ P))
      (s₂ := S.filter (fun B => B ∉ P))
      (f := fun B => Debt (V := V) (R := R) (Q := Q) B)
    -- sum_union は「添字集合の和」であり、我々は「∑ B ∈ …」の形なので、
    -- `sum_union` をそのまま使うため、メンバ制限なし版に一旦移し替える。
    -- ここでは `sum_union` を「通常の `sum`」に適用し、その後 `sum_filter` の形に戻す。
    -- よって、まず `sum_union` を適用し、その後 `hUnion` で S を復元。
    -- 詳細な `rw` 展開：
    -- sum over S = sum over (filter P ∪ filter ¬P)
    --            = sum over filter P + sum over filter ¬P
    -- これを「∈」付きに書きなおした現在の等式に一致させる。
    -- 実際の mathlib では `sum_filter_add_sum_filter_not_eq` 相当があるが、ここでは手作業で同型化します。
    -- （省略：`Finset.sum_filter` の等式で両辺を一致させる）
    -- ここでは短く `exact` で置き換え（詳細展開は環境の標準補題を使って良い）。
    exact by
      -- 「∈」付きの表記に合わせるための標準書換を使う
      -- 具体的には `Finset.sum_filter` の恒等式 `∑ x ∈ S, f x = ∑ x in S.filter p, f x + ∑ x in S.filter (¬p), f x`
      -- を再現している。
      -- 証明の詳細は既知の等式群から機械的に構成できるため省略。
      -- この行を `rw`・`simp` で丁寧に展開して頂いても OK です。
      simp_all only [P, S]
  -- 右辺第一項の `S.filter (∈ P)` はちょうど `P`（P ⊆ S なので）
  have hFilterIn :
    S.filter (fun B => B ∈ P) = P := by
    -- P ⊆ S は familyRep ⊆ Rep.powerset（定義から）
    -- よって S.filter (∈P) は P 自身
    ext B; constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro hBP
      have hBS : B ∈ S := by
        -- B ∈ P ⇒ B ⊆ Rep ⇒ B ∈ Rep.powerset = S
        rcases (B_mem_familyRep_iff_isClosed_R1 V R Q).mp hBP with ⟨hsub, _⟩
        exact (Finset.mem_powerset.mpr hsub)
      exact Finset.mem_filter.mpr ⟨hBS, hBP⟩
  -- まとめ
  calc
    ∑ B ∈ (Rep (Q := Q)).powerset, Debt (V := V) (R := R) (Q := Q) B
        = ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := by rfl
    _   = ∑ B ∈ S.filter (fun B => B ∈ P), Debt (V := V) (R := R) (Q := Q) B
          + ∑ B ∈ S.filter (fun B => B ∉ P), Debt (V := V) (R := R) (Q := Q) B := hSplitSum
    _   = ∑ B ∈ P, Debt (V := V) (R := R) (Q := Q) B
          + ∑ B ∈ S.filter (fun B => B ∉ P), Debt (V := V) (R := R) (Q := Q) B := by
          rw [hFilterIn]
    _   = ∑ B ∈ familyRep (V := V) (R := R) (Q := Q), Debt (V := V) (R := R) (Q := Q) B
          + ∑ B ∈ ((Rep (Q := Q)).powerset.filter (fun B => B ∉ familyRep (V := V) (R := R) (Q := Q))),
                Debt (V := V) (R := R) (Q := Q) B := by
          rfl



private lemma sum_mul_const_left
  {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (c : Int) (f : ι → Int) :
  ∑ i ∈ s, c * f i = c * (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hnot : a ∉ s := ha
    have hsum :
      ∑ i ∈ insert a s, c * f i
        = c * f a + ∑ i ∈ s, c * f i := by
      simp [Finset.sum_insert, hnot]
    calc
      ∑ i ∈ insert a s, c * f i
          = c * f a + ∑ i ∈ s, c * f i := hsum
      _   = c * f a + c * (∑ i ∈ s, f i) := by
            exact congrArg (fun t => c * f a + t) ih
      _   = c * (f a + ∑ i ∈ s, f i) := by
            -- 左分配法則
            have := Int.mul_add c (f a) (∑ i ∈ s, f i)
            exact this.symm
      _   = c * (∑ i ∈ insert a s, f i) := by
            simp [Finset.sum_insert, hnot]

lemma sum_fiber_bounds_to_debt_sum
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (nonemp : (Free (Q := Q)).Nonempty) :
  NDS2 V (family V R)
  ≤ (2 : Int) ^ (Free (Q := Q)).card
        * (∑ B ∈ (Rep (Q := Q)).powerset, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
    + ∑ B ∈ (Rep (Q := Q)).powerset, Debt (V := V) (R := R) (Q := Q) B := by
  classical
  -- fiber 分割恒等式で左辺を展開
  have hpart := NDS2_family_partition_over_fibers (V := V) (R := R) (Q := Q)
  -- 各 B での点別上界を用意
  have hpoint :
    ∀ {B}, B ∈ (Rep (Q := Q)).powerset →
      ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
          - (V.card : Int) * (fiber V R Q B).card )
      ≤
      ( (2 : Int) ^ (Free (Q := Q)).card
          * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
        + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    intro B hB
    have hBsub : B ⊆ Rep (Q := Q) := by
      exact Finset.mem_powerset.mp hB
    exact fiber_nds2_le_rep_term_with_debt
            (V := V) (R := R) (Q := Q) (B := B) hBsub nonemp
  -- 総和の単調性で束ねる（既出：finset_sum_le_finset_sum）
  have hsum :
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (fiber V R Q B).card )
    ≤
    ∑ B ∈ (Rep (Q := Q)).powerset,
        ( (2 : Int) ^ (Free (Q := Q)).card
            * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
          + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := by
    refine finset_sum_le_finset_sum ?ineq
    intro B hB
    exact hpoint hB
  -- 左辺を NDS2 に戻す
  have hL :
    NDS2 V (family V R)
      = ∑ B ∈ (Rep (Q := Q)).powerset,
          ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
            - (V.card : Int) * (fiber V R Q B).card ) := by
    exact hpart
  -- 右辺の最終整理：定数因子の前取り＋ Debt の定義
  --（1）定数因子の前取り
  have hconst :
    ∑ B ∈ (Rep (Q := Q)).powerset,
      ( (2 : Int) ^ (Free (Q := Q)).card
          * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) )
      =
    (2 : Int) ^ (Free (Q := Q)).card
      * (∑ B ∈ (Rep (Q := Q)).powerset,
            ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) := by
    -- 自作補題で左因子を前に出す

    let smcl := (sum_mul_const_left
      (s := (Rep (Q := Q)).powerset)
      (c := (2 : Int) ^ (Free (Q := Q)).card)
      (f := fun B => ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))).symm
    exact id (Eq.symm smcl)
  --（2）Debt の定義で置換
  have hDebt :
    ∑ B ∈ (Rep (Q := Q)).powerset,
      ( ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
          * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) )
    =
    ∑ B ∈ (Rep (Q := Q)).powerset, Debt (V := V) (R := R) (Q := Q) B := by
    -- 定義を書き戻すだけ
    -- `rw [Debt]` を各項に適用するには `Finset.sum_congr` を用いる
    refine Finset.sum_congr rfl ?step
    intro B hB
    rfl
  -- まとめ
  calc
    NDS2 V (family V R)
        = ∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) * (∑ I ∈ fiber V R Q B, (I.card : Int))
              - (V.card : Int) * (fiber V R Q B).card ) := hL
    _   ≤ ∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) ^ (Free (Q := Q)).card
                * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card )
              + ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
                * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) ) := hsum
    _   =
        (∑ B ∈ (Rep (Q := Q)).powerset,
            ( (2 : Int) ^ (Free (Q := Q)).card
                * ( (2 : Int) * (B.card : Int) - (Rep (Q := Q)).card ) ))
        + (∑ B ∈ (Rep (Q := Q)).powerset,
            ( ( ((2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
                * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) )) := by
          exact Finset.sum_add_distrib
    _   =
        (2 : Int) ^ (Free (Q := Q)).card
          * (∑ B ∈ (Rep (Q := Q)).powerset,
                ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        + ∑ B ∈ (Rep (Q := Q)).powerset, Debt (V := V) (R := R) (Q := Q) B := by
          -- 左項を hconst、右項を hDebt
          rw [hconst, hDebt]

private lemma sum_split_by_filter
  {ι : Type*} [DecidableEq ι]
  (S : Finset ι) (P : ι → Prop) [DecidablePred P] (f : ι → Int) :
  ∑ x ∈ S, f x
    =
  ∑ x ∈ S.filter (fun a => P a), f x
  + ∑ x ∈ S.filter (fun a => ¬ P a), f x := by
  classical
  -- 帰納法で S を走査
  refine Finset.induction_on S ?base ?step
  · -- 空集合
    simp
  · intro a s ha ih
    have hnot : a ∉ s := ha
    -- 目的の等式を insert 版で示す
    -- 左辺
    have hL : ∑ x ∈ insert a s, f x
              = f a + ∑ x ∈ s, f x := by
      simp [Finset.sum_insert, hnot]
    -- 右辺：filter 側の分割
    have hR_yes :
      ∑ x ∈ (insert a s).filter (fun a => P a), f x
        =
      (if P a then f a else 0) + ∑ x ∈ s.filter (fun a => P a), f x := by
      by_cases hPa : P a
      · -- a は yes 側に入る
        have : (insert a s).filter (fun a => P a)
                = insert a (s.filter (fun a => P a)) := by
          ext x; constructor
          · intro hx
            have hx₁ : x ∈ insert a s := (Finset.mem_filter.mp hx).1
            have hx₂ : P x := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_insert.mp hx₁ with hx | hx
            · subst hx; simp [hPa]
            · have : x ∈ s := hx
              have : x ∈ s.filter (fun a => P a) := by
                exact Finset.mem_filter.mpr ⟨this, hx₂⟩
              exact by
                simp [this]
          · intro hx
            rcases Finset.mem_insert.mp hx with hx | hx
            · subst hx; exact Finset.mem_filter.mpr ⟨by simp, hPa⟩
            · have hx' : x ∈ s.filter (fun a => P a) := hx
              have hx_s : x ∈ s := (Finset.mem_filter.mp hx').1
              have hxP : P x := (Finset.mem_filter.mp hx').2
              exact Finset.mem_filter.mpr ⟨by simp [hx_s], hxP⟩
        have hdis : a ∉ s.filter (fun a => P a) := by
          exact fun h => hnot ((Finset.mem_filter.mp h).1)
        simp [this, Finset.sum_insert, hdis, hPa]
      · -- a は no 側なので filter(yes) には入らない
        have : (insert a s).filter (fun a => P a) = s.filter (fun a => P a) := by
          ext x; constructor
          · intro hx
            have hx₁ : x ∈ insert a s := (Finset.mem_filter.mp hx).1
            have hx₂ : P x := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_insert.mp hx₁ with hx | hx
            · subst hx; exact False.elim (hPa hx₂)
            · exact Finset.mem_filter.mpr ⟨hx, hx₂⟩
          · intro hx; exact by
              have hx_s : x ∈ s := (Finset.mem_filter.mp hx).1
              have hxP : P x := (Finset.mem_filter.mp hx).2
              apply Finset.mem_filter.mpr ⟨by simp [hx_s], hxP⟩

        simp [this, hPa]
    have hR_no :
      ∑ x ∈ (insert a s).filter (fun a => ¬ P a), f x
        =
      (if P a then 0 else f a) + ∑ x ∈ s.filter (fun a => ¬ P a), f x := by
      -- 上と同様（¬P）側
      by_cases hPa : P a
      ·
        have : (insert a s).filter (fun a => ¬ P a) = s.filter (fun a => ¬ P a) := by
          ext x; constructor
          · intro hx
            have hx₁ : x ∈ insert a s := (Finset.mem_filter.mp hx).1
            have hx₂ : ¬ P x := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_insert.mp hx₁ with hx | hx
            · subst hx; exact (hx₂ hPa).elim
            · exact Finset.mem_filter.mpr ⟨hx, hx₂⟩
          · intro hx; exact by
              have hx_s : x ∈ s := (Finset.mem_filter.mp hx).1
              have hxP : ¬ P x := (Finset.mem_filter.mp hx).2
              exact Finset.mem_filter.mpr ⟨by simp [hx_s], hxP⟩
        simp [this, hPa]
      ·
        have : (insert a s).filter (fun a => ¬ P a)
                = insert a (s.filter (fun a => ¬ P a)) := by
          ext x; constructor
          · intro hx
            have hx₁ : x ∈ insert a s := (Finset.mem_filter.mp hx).1
            have hx₂ : ¬ P x := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_insert.mp hx₁ with hx | hx
            · subst hx; simp [hPa]
            · have : x ∈ s := hx
              have : x ∈ s.filter (fun a => ¬ P a) := by
                exact Finset.mem_filter.mpr ⟨this, hx₂⟩
              exact by simp [this]
          · intro hx
            rcases Finset.mem_insert.mp hx with hx | hx
            · subst hx; exact Finset.mem_filter.mpr ⟨by simp, by exact hPa⟩
            · have hx' : x ∈ s.filter (fun a => ¬ P a) := hx
              have hx_s : x ∈ s := (Finset.mem_filter.mp hx').1
              have hxP : ¬ P x := (Finset.mem_filter.mp hx').2
              exact Finset.mem_filter.mpr ⟨by simp [hx_s], hxP⟩
        have hdis : a ∉ s.filter (fun a => ¬ P a) := by
          exact fun h => hnot ((Finset.mem_filter.mp h).1)
        simp [this, Finset.sum_insert, hdis, hPa]
    -- 以上を合体：左右をそれぞれ分解し、帰納法の仮定を使って等式を得る
    calc
      ∑ x ∈ insert a s, f x
          = f a + ∑ x ∈ s, f x := hL
      _ = f a + ( ∑ x ∈ s.filter (fun a => P a), f x
                  + ∑ x ∈ s.filter (fun a => ¬ P a), f x ) := by
            exact congrArg (fun t => f a + t) ih
      _ = ( (if P a then f a else 0) + ∑ x ∈ s.filter (fun a => P a), f x )
          + ( (if P a then 0 else f a) + ∑ x ∈ s.filter (fun a => ¬ P a), f x ) := by
            by_cases hPa : P a <;> simp [hPa, add_comm, add_left_comm, add_assoc]
      _ = ∑ x ∈ (insert a s).filter (fun a => P a), f x
          + ∑ x ∈ (insert a s).filter (fun a => ¬ P a), f x := by
            -- hR_yes, hR_no を戻す
            rw [hR_yes, hR_no]

-- 直方体＝拡張の全射性（fiber の像が Free.powerset を尽くすこと）使われている。
private lemma fiber_surj_diff_of_isClosedR1
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α} (hB : B ⊆ Rep (Q := Q))
  (hClosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B) :
  (Free (Q := Q)).powerset ⊆ (fiber V R Q B).image (fun I : Finset α => I \ B) := by
  -- ポイント：任意の S ⊆ Free に対し I := B ∪ S が family V R に入り、trace が B。
  -- 既にあなたの因数分解証明で使っている構成（自由部分の直方体）をそのまま明示化する。
  -- 詳細は下の本体で呼び出します。
  admit

-- 逆向き：full cube（像が Free.powerset）なら isClosed R₁ B 使われている。
private lemma isClosedR1_of_fiber_surj_diff
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α} (hB : B ⊆ Rep (Q := Q))
  (hSurj :
    (Free (Q := Q)).powerset ⊆ (fiber V R Q B).image (fun I : Finset α => I \ B)) :
  isClosed (R1 (V := V) (R := R) (Q := Q)) B := by
  -- ポイント：像が全域 ⇒ 任意の S ⊆ Free に対し B∪S が fiber の元として取れる
  -- ⇒ family V R にあるので、縮約前の閉包で全 S が許される
  -- ⇒ 縮約後に B が閉。
  admit

lemma card_of_equiv (A B : Finset α): A ⊆ B → A.card = B.card → A = B := by
  intro h_sub h_card
  have hdiff : (B \ A).card = 0 := by
    rw [ Finset.card_sdiff h_sub, h_card]
    ring_nf
    exact Nat.sub_self B.card
  have hempty : B \ A = ∅ := Finset.card_eq_zero.1 hdiff
  simp_all only [Finset.card_empty, Finset.sdiff_eq_empty_iff_subset]
  exact le_antisymm h_sub hempty

lemma fiber_fullCube_iff_B_mem_familyRep
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α} (hB : B ⊆ Rep (Q := Q)) :
  (fiber V R Q B).card = (2 : Nat) ^ (Free (Q := Q)).card
  ↔ B ∈ familyRep (V := V) (R := R) (Q := Q) := by
  classical
  -- 記号短縮
  set F  := Free (Q := Q)
  set φ  := (fun I : Finset α => I \ B)
  set Im := (fiber V R Q B).image φ

  have hIm_sub : Im ⊆ F.powerset := by
    -- 既存：image_diff_subset_powerset_free
    simpa [Im, φ, F] using
      (image_diff_subset_powerset_free (V := V) (R := R) (Q := Q) (B := B) hB)

  have hInj :
    ∀ {I} (_ : I ∈ fiber V R Q B) {J} (_ : J ∈ fiber V R Q B), φ I = φ J → I = J := by
    -- 既存：fiber_inj_on_diff
    intro I hI J hJ hEq
    have := (fiber_inj_on_diff (V := V) (R := R) (Q := Q) (B := B) hB) hI hJ
    -- 置換
    simpa [φ] using this hEq

  -- 単射 ⇒ |image| = |fiber|
  have hCard_image_eq :
      (Im.card : Nat) = (fiber V R Q B).card := by
    -- 標準事実：Finset の像のカード＝元集合のカード（単射時）
    -- mathlib の `card_image_...` 系を使うか、「≤ 両向き」から等号を作る。
    -- ここでは「≤ と ≥」を手で作って等号にします。

    -- (1) ≤ は一般に成り立つ（像は縮む可能性がある）
    have hle : Im.card ≤ (fiber V R Q B).card := by
      -- 単射性から `card (image) = card (source)` を直接出せる補題があるならそれを使って構いません。
      -- ここでは下で等号に上げるので一旦保留。
      -- 実際の実装では `Finset.card_image_...` を使ってください。
      simp_all only [Im, φ, F]
      exact Finset.card_image_le

    -- (2) ≥ は、単射性と「像から元へ戻す」関数の構成で得られます。
    have hge : (fiber V R Q B).card ≤ Im.card := by
      -- 単射 ⇒ `image` と `source` の要素数は一致。詳細は上と同様、標準補題で処理可。
      simp_all only [Im, φ, F]
      rwa [Finset.card_image_of_injOn]

    simp_all only [Im, φ, F]
    symm
    rwa [Finset.card_image_of_injOn]


  -- 2^|Free| は Free.powerset の濃度
  have hCard_pow : F.powerset.card = (2 : Nat) ^ F.card := by
    -- 既存：card_powerset_pow
    exact card_powerset_pow (S := F)

  -- ここから equivalence
  constructor
  · -- (→) `|fiber| = 2^{|Free|}` ⇒ `B ∈ familyRep`
    intro hCard
    -- 像と全体の冪集合が等濃度
    have hCardIm :
      Im.card = F.powerset.card := by
      -- |Im| = |fiber| = 2^{|Free|} = |F.powerset|
      have := congrArg (fun n : Nat => n) hCard
      -- 補助等式の挿入
      -- |Im| = |fiber|
      have h₁ : Im.card = (fiber V R Q B).card := by
        exact hCard_image_eq
      -- 連結
      calc
        Im.card = (fiber V R Q B).card := h₁
        _       = (2 : Nat) ^ F.card   := by simpa [F] using hCard
        _       = F.powerset.card      := hCard_pow.symm
    -- 包含＋等濃度 ⇒ 等集合
    have hIm_eq : Im = F.powerset := by

      exact card_of_equiv Im F.powerset hIm_sub hCardIm--(by exact le_of_eq hCardIm) --(by exact ge_of_eq hCardIm)
      -- 上の行は「包含＋カードの等号」から等集合を得るための一行。環境に応じて
      -- `Finset.card_eq_iff_eq_of_subset` 相当の補題で置き換えてください。

    -- したがって、任意の S ⊆ Free について、S ∈ Im。
    have hSurj :
      F.powerset ⊆ Im := by
      exact Finset.subset_of_eq (id (Eq.symm hIm_eq))

    -- 像が全域 ⇒ 「全ての S ⊆ Free に対して fiber に I がある（I\B = S）」
    -- これから isClosed R₁ B を得る
    have hClosed : isClosed (R1 (V := V) (R := R) (Q := Q)) B :=
      isClosedR1_of_fiber_surj_diff (V := V) (R := R) (Q := Q) hB hSurj

    -- familyRep の定義に戻す
    -- B ⊆ Rep は仮定 hB。よって B ∈ (Rep).powerset
    have hSubRep : B ∈ (Rep (Q := Q)).powerset := by
      exact Finset.mem_powerset.mpr hB
    -- `familyRep = powerset.filter (isClosed R₁)`
    -- よって B ∈ familyRep
    exact Finset.mem_filter.mpr ⟨hSubRep, hClosed⟩

  · -- (←) `B ∈ familyRep` ⇒ `|fiber| = 2^{|Free|}`
    intro hBmem
    -- 定義展開で isClosed R₁ B を得る
    rcases (B_mem_familyRep_iff_isClosed_R1 V R Q).mp hBmem with ⟨hB', hClosed⟩
    -- 仮定の hB と familyRep 側の hB' は一致する（以後 hB を使う）
    -- 像の包含は既知：Im ⊆ Free.powerset（上で hIm_sub）
    -- 逆包含（全射）を isClosed R₁ から得る
    have hSurj :
      F.powerset ⊆ Im :=
      fiber_surj_diff_of_isClosedR1 (V := V) (R := R) (Q := Q) hB hClosed
    -- よって Im = F.powerset
    have hIm_eq : Im = F.powerset := by
      apply Finset.Subset.antisymm_iff.mpr ⟨hIm_sub, hSurj⟩
    -- カード等式へ
    have : (fiber V R Q B).card
            = (Im.card : Nat) := by
      exact (hCard_image_eq.symm)
    calc
      (fiber V R Q B).card
          = Im.card := by exact this
      _   = F.powerset.card := by exact congrArg Finset.card hIm_eq
      _   = (2 : Nat) ^ F.card := by exact hCard_pow


lemma Debt_eq_zero_of_mem_familyRep
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  {B : Finset α}
  (hBmem : B ∈ familyRep (V := V) (R := R) (Q := Q)) :
  Debt (V := V) (R := R) (Q := Q) B = 0 := by
  classical
  -- familyRep の定義から B ⊆ Rep と isClosed(R₁) を取り出す
  rcases (B_mem_familyRep_iff_isClosed_R1 V R Q).mp hBmem with ⟨hBsub, _hClosedR1⟩
  -- A1（「→」向き）：B ∈ familyRep ⇒ fiber は full cube（濃度 = 2^{|Free|}）
  have hfull :
    (fiber V R Q B).card = (2 : Nat) ^ (Free (Q := Q)).card :=
    (fiber_fullCube_iff_B_mem_familyRep (V := V) (R := R) (Q := Q) hBsub).mpr hBmem

  -- Debt を展開して左因子が 0 であることを示す
  unfold Debt
  -- 左因子 ((2^|Free| : Int) - |fiber|) = 0 を作る（両辺を Int キャストして差が 0）
  have hLeft :
      (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
        - (fiber V R Q B).card) = 0 := by
    -- 型を合わせるために右の card を Int に持ち上げる
    change
      (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
        - ((fiber V R Q B).card : Int)) = 0
    -- hfull を Int に持ち上げる
    have hcast :
      (( (2 : Nat) ^ (Free (Q := Q)).card : Int)
        = ((fiber V R Q B).card : Int)) := by
      simp_all only [R1, Nat.cast_ofNat, Nat.cast_pow]

    -- 差が 0
    rw [hcast, sub_self]

  -- 積の一因子が 0 なので全体が 0
  calc
    ( (( (2 : Nat) ^ (Free (Q := Q)).card : Int) - (fiber V R Q B).card )
        * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) )
        = 0 * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
            rw [hLeft]
    _   = 0 := by
            simp


lemma sum_debt_on_familyRep_is_zero
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R) :
  ∑ B ∈ familyRep (V := V) (R := R) (Q := Q), Debt (V := V) (R := R) (Q := Q) B = 0 := by
  classical
  have hterm :
    ∀ {B}, B ∈ familyRep (V := V) (R := R) (Q := Q) →
      Debt (V := V) (R := R) (Q := Q) B = 0 := by
    intro B hB
    rcases (B_mem_familyRep_iff_isClosed_R1 V R Q).mp hB with ⟨hsub, _⟩
    exact Debt_eq_zero_of_mem_familyRep V R Q hB
  have : ∑ B ∈ familyRep (V := V) (R := R) (Q := Q), Debt (V := V) (R := R) (Q := Q) B
        = ∑ _ ∈ familyRep (V := V) (R := R) (Q := Q), (0 : Int) := by
    refine Finset.sum_congr rfl ?step
    intro B hB
    exact hterm hB
  calc
    ∑ B ∈ familyRep (V := V) (R := R) (Q := Q), Debt (V := V) (R := R) (Q := Q) B
        = ∑ _ ∈ familyRep (V := V) (R := R) (Q := Q), (0 : Int) := this
    _   = ((familyRep (V := V) (R := R) (Q := Q)).card : Int) * 0 := by
          exact sum_const_int (familyRep (V := V) (R := R) (Q := Q)) 0
    _   = 0 := by
          simp

lemma debt_remainder_absorbed_by_R1_with_const
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hSign :
    ∀ {B}, B ∈ ((Rep (Q := Q)).powerset.filter
                  (fun B => B ∉ familyRep (V := V) (R := R) (Q := Q))) →
            0 ≤ (V.card : Int) - (2 : Int) * (B.card : Int)) :
  ∑ B ∈ ((Rep (Q := Q)).powerset.filter (fun B => B ∉ familyRep (V := V) (R := R) (Q := Q))),
      Debt (V := V) (R := R) (Q := Q) B
  ≤ (2 : Int) ^ (Free (Q := Q)).card
        * (∑ B ∈ familyRep (V := V) (R := R) (Q := Q),
              ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
      + ((2 : Int) ^ (Free (Q := Q)).card) * (Free (Q := Q)).card
          * (((Rep (Q := Q)).powerset.filter
                (fun B => B ∉ familyRep (V := V) (R := R) (Q := Q))).card : Int) := by
  classical
  -- 記号の短縮
  set A  : Int := ( ((2 : Nat) ^ (Free (Q := Q)).card : Nat) : Int )
  set Rc : Int := Int.ofNat ((Rep (Q := Q)).card)
  set Fc : Int :=  Int.ofNat (Free (Q := Q)).card
  set P  : Finset (Finset α) := familyRep (V := V) (R := R) (Q := Q)
  set S  : Finset (Finset α) := (Rep (Q := Q)).powerset
  set NCL : Finset (Finset α) := S.filter (fun B => B ∉ P)

  have hDebt_le_A :
    ∀ {B}, B ∈ NCL →
      Debt (V := V) (R := R) (Q := Q) B ≤ A * ((V.card : Int) - (2 : Int) * (B.card : Int)) := by
    intro B hB
    -- Debt = (A - |fiber_B|) * (|V| - 2|B|)
    -- 非負仮定 hSign と |fiber_B| ≥ 0 から、(A - |fiber_B|) ≤ A かつ右因子 ≥ 0
    -- よって Debt ≤ A * (|V| - 2|B|)
    have hR : 0 ≤ (V.card : Int) - (2 : Int) * (B.card : Int) := by
      exact hSign hB
    -- |fiber_B| は自然数（Int 化）なので 0 ≤ |fiber_B|
    have hL : (0 : Int) ≤ ((fiber V R Q B).card : Int) := by
      exact Int.natCast_nonneg _
    -- よって (A - |fiber_B|) ≤ A
    have hcoeff : ( ((A - ((fiber V R Q B).card : Int)) : Int) )
                    ≤ A := by
      have : ((A - ((fiber V R Q B).card : Int)) : Int)
              = A + (- ((fiber V R Q B).card : Int)) := by ring
      have : A + (- ((fiber V R Q B).card : Int)) ≤ A + 0 := by
        -- 右辺非減単調性と -|fiber| ≤ 0
        have hneg : - ((fiber V R Q B).card : Int) ≤ 0 := by
          have := hL
          -- 0 ≤ |fiber| ⇒ -|fiber| ≤ 0
          exact (neg_nonpos.mpr this)
        exact add_le_add_left hneg _
      exact this
    -- 積の単調性（右因子非負）で結論
    have := Int.mul_le_mul_of_nonneg_right hcoeff hR
    -- 左辺は Debt、右辺は A * (|V| - 2|B|)
    -- Debt の定義で書換
    -- A は (2^|Free|) の Int 埋め込み
    -- ここは `rw [Debt]` 相当の展開をする
    have hDebt_def :
      Debt (V := V) (R := R) (Q := Q) B
        = (A - ((fiber V R Q B).card : Int))
            * ( (V.card : Int) - (2 : Int) * (B.card : Int) ) := by
      -- A の定義に合わせて、`Debt` の左因子 ((2^|Free| : Int) - |fiber|)
      -- を `rfl` で一致させる
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Int.sub_nonneg, and_imp, not_false_eq_true, Nat.cast_nonneg,
        Nat.cast_pow, Nat.cast_ofNat, tsub_le_iff_right, le_add_iff_nonneg_right, NCL, P, S, A]
      obtain ⟨left, right⟩ := hB
      rfl

    simpa [hDebt_def] using this

  -- 非閉側での和に hDebt_le_A を項別適用して上界
  have hSum_le_A :
    ∑ B ∈ NCL, Debt (V := V) (R := R) (Q := Q) B
      ≤ ∑ B ∈ NCL, A * ((V.card : Int) - (2 : Int) * (B.card : Int)) := by
    refine finset_sum_le_finset_sum ?ineq
    intro B hB
    exact hDebt_le_A hB

  -- 右辺の和は A を前に出せる
  have hPull :
    ∑ B ∈ NCL, A * ((V.card : Int) - (2 : Int) * (B.card : Int))
      = A * (∑ B ∈ NCL, ((V.card : Int) - (2 : Int) * (B.card : Int))) := by
    -- 左因子定数の引き出し
    -- 先に示した補題と同様の書換（sum_mul_const_left）
    -- ここは簡単のため同等の書換を `Finset.induction_on` で実装してもよい
    -- 以降の整理では値 A と和の分配だけを使う
    -- 省略を避けるため、適宜あなたの環境の補題を使用してください
    -- （この行を適切な補題の `rw` で置き換え）
    --Aをそとに出しているだけ？
    rw [@Finset.mul_sum]

  -- 和の中身を |Free| と (2|B| - |Rep|) に分解：
  -- (|V| - 2|B|) = |Free| - (2|B| - |Rep|)
  have hDecomp :
    ∀ {B}, B ∈ NCL →
      ((V.card : Int) - (2 : Int) * (B.card : Int))
        = Fc - ((2 : Int) * (B.card : Int) - Rc) := by
    intro B hB
    -- |V| = |Rep| + |Free|（既存補題 21）
    have hVRF : (V.card : Int) = Rc + Fc := by
      -- `cardV_as_Rep_plus_Free`
      -- そのまま `rw` で使える形に（環境に合わせて）
      exact cardV_as_Rep_plus_Free (V := V) (R := R) (Q := Q)
    calc
      (V.card : Int) - (2 : Int) * (B.card : Int)
          = (Rc + Fc) - (2 : Int) * (B.card : Int) := by
                exact congrArg (fun t => t - (2 : Int) * (B.card : Int)) hVRF
      _   = Fc - ( (2 : Int) * (B.card : Int) - Rc ) := by
                ring

  -- よって
  have hSumDecomp :
    ∑ B ∈ NCL, ((V.card : Int) - (2 : Int) * (B.card : Int))
      = (NCL.card : Int) * Fc
        - ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc) := by
    -- 左は ∑(Fc) - ∑(2|B| - Rc) = |NCL|*Fc - …
    -- 定数和の補題（sum_const_int）を使う
    have h1 :
      ∑ B ∈ NCL, Fc = (NCL.card : Int) * Fc := by
      exact sum_const_int (s := NCL) (c := Fc)
    have h2 :
      ∑ B ∈ NCL, ((V.card : Int) - (2 : Int) * (B.card : Int))
        = ∑ B ∈ NCL, (Fc - ((2 : Int) * (B.card : Int) - Rc)) := by
      refine Finset.sum_congr rfl ?step
      intro B hB
      exact hDecomp hB
    calc
      ∑ B ∈ NCL, ((V.card : Int) - (2 : Int) * (B.card : Int))
          = ∑ B ∈ NCL, (Fc - ((2 : Int) * (B.card : Int) - Rc)) := h2
      _   = (∑ B ∈ NCL, Fc) - ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc) := by
            -- 線形性
            simp [Finset.sum_sub_distrib]
      _   = (NCL.card : Int) * Fc
            - ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc) := by
            rw [h1]

  -- 非閉側の主和を閉側へ移す（全体和=0）
  have hMainZero :
    ∑ B ∈ S, ((2 : Int) * (B.card : Int) - Rc) = 0 := by
    -- 既存：sum_main_over_powerset_eq_zero
    exact sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
  have hSplitMain :
    ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc)
      = - ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) := by
    -- S = P ⊔ NCL、全体和 0
    -- よって 非閉 = - 閉
    -- C1 で分割（和の分解）→ C2 で閉側 Debt が 0 だが今回は main 和の話なので、
    -- ここは sum の分配と filter 分割の基本恒等式を使えば機械的に落ちます。
    have :S = P ⊔ NCL := by
      -- `Finset.union_eq_sdiff_union_filter` 相当の補題を使う
      -- ここでは直接書く
      ext B; constructor
      · intro hB
        have hB1 : B ∈ S := hB
        have hB2 : B ∉ P ∨ B ∈ P := by
          simp_all [NCL, P, S, Fc, Rc, A]
          tauto
        rcases hB2 with hB2 | hB2
        · have : B ∈ NCL := by
            exact Finset.mem_filter.mpr ⟨hB1, hB2⟩
          exact Finset.mem_union_right _ this
        · have : B ∈ P := hB2
          exact Finset.mem_union_left _ this
      · intro hB
        rcases Finset.mem_union.mp hB with hB | hB
        · have : B ∈ S := by
            exact Finset.mem_of_mem_filter B hB
          exact this
        · have : B ∈ S := by
            exact Finset.mem_of_mem_filter B hB
          exact this
    rw [this] at hMainZero
    have : ∑ B ∈ P ⊔ NCL, ((2 : Int) * (B.card : Int) - Rc) = 0 := hMainZero
    have : ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc)
            + ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc) = 0 := by
      have disj: Disjoint P NCL := by
        dsimp [NCL]
        by_contra h
        simp at h
        rw [Finset.not_disjoint_iff_nonempty_inter] at h
        obtain ⟨x, hx⟩ := h
        simp at hx
        exact hx.2.2 hx.1

      let fs := @Finset.sum_union _ Int _ _ _ (fun B:(Finset α) => ((2 : Int) * (@Nat.cast ℤ instNatCastInt B.card) - Rc)) _ disj

      --ring_nf at fs
      --rw [fs] at this
      have disj : Disjoint P NCL := by
        dsimp [NCL]
        by_contra h
        simp at h
        rw [Finset.not_disjoint_iff_nonempty_inter] at h
        obtain ⟨x, hx⟩ := h
        simp at hx
        exact hx.2.2 hx.1
      simp at fs
      have :∑ x ∈ P ∪ NCL, (2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc) =
         ∑ x ∈ P, (2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc) + ∑ x ∈ NCL, (2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc) := by
        rw [Finset.sum_union (Finset.disjoint_val.mp ?_)]
        (expose_names; exact Finset.disjoint_val.mpr disj_1)

      /- 以下の長い証明が2行になった。Deepseek。
        have :∑ x ∈ P ∪ NCL, (2 * @Nat.cast ℤ instNatCastInt x.card - Rc) = ∑ x ∈ P ∪ NCL, 2 * (@Nat.cast ℤ instNatCastInt x.card) - ∑ x ∈ P ∪ NCL, Rc := by
          apply Finset.sum_sub_distrib
        rw [this]
        have : ∑ x ∈ P ∪ NCL, Rc = (P ∪ NCL).card * Rc := by
          exact Finset.sum_const (s := P ∪ NCL) (b := Rc)
        rw [this]
        rw [fs]
        ring_nf
        have sign: ∑ x ∈ P, ((@Nat.cast ℤ instNatCastInt x.card) * 2) + (-((@Nat.cast ℤ instNatCastInt P.card) * Rc)- Rc * (@Nat.cast ℤ instNatCastInt NCL.card)) = ∑ x ∈ P, ((@Nat.cast ℤ instNatCastInt x.card) * 2) -((@Nat.cast ℤ instNatCastInt P.card) * Rc)- Rc * (@Nat.cast ℤ instNatCastInt NCL.card) := by
          --apply Finset.sum_congr rfl (fun x hx => Int.sub_eq_add_neg)
          rw [Int.sub_eq_add_neg]
          rw [Int.sub_eq_add_neg]
          rw [Int.sub_eq_add_neg]
          exact Eq.symm (Int.add_assoc (∑ x ∈ P, ↑x.card * 2) (-(↑P.card * Rc)) (-(Rc * ↑NCL.card)))
        rw [sign]
        --以降はPだけの等号、NCLだけの等号を作って足し合わせる
        have hP: ∑ x ∈ P, (2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc) = ∑ x ∈ P, 2 * (@Nat.cast ℤ instNatCastInt x.card) - ∑ x ∈ P, Rc := by
          apply Finset.sum_sub_distrib
        have hNCL: ∑ x ∈ NCL, (2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc) = ∑ x ∈ NCL, 2 * (@Nat.cast ℤ instNatCastInt x.card) - ∑ x ∈ NCL, Rc := by
          apply Finset.sum_sub_distrib
        have : ∀ x ∈ P, 2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc = -Rc + (@Nat.cast ℤ instNatCastInt x.card)*2 := by
          intro x hx
          ring

        let fsc := Finset.sum_congr rfl (fun x hx => this x hx)
        rw [←fsc]
        rw [hP]
        have : ∀ x ∈ NCL, 2 * (@Nat.cast ℤ instNatCastInt x.card) - Rc = -Rc + (@Nat.cast ℤ instNatCastInt x.card)*2 := by
          intro x hx
          ring
        let fsc2 := Finset.sum_congr rfl (fun x hx => this x hx)
        rw [←fsc2]
        rw [hNCL]
        have : ∀ x ∈ P, 2 * (@Nat.cast ℤ instNatCastInt x.card) = (@Nat.cast ℤ instNatCastInt x.card)*2 := by
          intro x hx
          ring
        let fsc3 := Finset.sum_congr rfl (fun x hx => this x hx)
        rw [←fsc3]

        --have :(-( (@Nat.cast ℤ instNatCastInt P.card) * Rc) - Rc * (@Nat.cast ℤ instNatCastInt NCL.card)) + ∑ x ∈ NCL, (@Nat.cast ℤ instNatCastInt x.card) * 2 = - ∑ x ∈ P, Rc + (∑ x ∈ NCL, 2 * (@Nat.cast ℤ instNatCastInt x.card) - ∑ x ∈ NCL, Rc) := by
        rw [Finset.sum_const]
        rw [Finset.sum_const]
        ring_nf
      -/

      rw [←this]
      exact hMainZero

    exact Eq.symm (Int.neg_eq_of_add_eq_zero this)

  -- 以上を合体
  have :
    ∑ B ∈ NCL, Debt (V := V) (R := R) (Q := Q) B
      ≤ A * ( (NCL.card : Int) * Fc
              - ( - ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) ) := by
    calc
      ∑ B ∈ NCL, Debt (V := V) (R := R) (Q := Q) B
          ≤ ∑ B ∈ NCL, A * ((V.card : Int) - (2 : Int) * (B.card : Int)) := hSum_le_A
      _   = A * (∑ B ∈ NCL, ((V.card : Int) - (2 : Int) * (B.card : Int))) := hPull
      _   = A * ( (NCL.card : Int) * Fc
                  - ∑ B ∈ NCL, ((2 : Int) * (B.card : Int) - Rc) ) := by
            rw [hSumDecomp]
      _   = A * ( (NCL.card : Int) * Fc
                  - ( - ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) ) := by
            -- 非閉の主和を閉側へ移す
            rw [hSplitMain]

  -- 右辺を目的の形へ配列
  -- A * ((NCL.card : Int) * Fc) + A * (∑_{P} (2|B| - Rc))
  have : ∑ B ∈ NCL, Debt (V := V) (R := R) (Q := Q) B
        ≤ A * (∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc))
          + A * Fc * (NCL.card : Int) := by
    -- 展開・結合
    -- A * (X - (-Y)) = A * (X + Y) = A*Y + A*X
    -- さらに A*X = A*Fc*(|NCL|) に等しい
    -- `ring` 不使用で逐次書換
    have h1 :
      A * ( (NCL.card : Int) * Fc
            - ( - ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) )
        = A * ( (NCL.card : Int) * Fc )
          + A * ( ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) := by
      calc
        A * ( (NCL.card : Int) * Fc - ( - ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) )
            = A * ( (NCL.card : Int) * Fc + ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) := by
                ring
        _   = A * ( (NCL.card : Int) * Fc )
              + A * ( ∑ B ∈ P, ((2 : Int) * (B.card : Int) - Rc) ) := by
                exact (Int.mul_add A _ _)
    -- 置換
    exact le_trans this (by
      rw [h1]
      rw [Int.mul_comm NCL.card Fc]
      rw [Int.mul_assoc A Fc (NCL.card : Int)]
      rw [Int.add_comm (A * (Fc * NCL.card : Int)) (A * ∑ B ∈ P, (2 * ↑B.card - Rc))]
      )

  -- 表記を戻して完成
  -- 右辺の第一項は R₁ 因数式と一致、第二項が残差（Free × 個数）項
  -- 目的の不等式はちょうどこの形
  -- ここで A, Fc, P, NCL の定義を戻す
  -- `rfl` と `simp` で仕上げ
  simp_all only [Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, and_self, Int.ofNat_eq_coe, Int.sub_nonneg,
    tsub_le_iff_right, and_imp, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_sub_distrib, Finset.sum_const,
    Int.nsmul_eq_mul, Finset.card_powerset, neg_sub, NCL, P, S, Fc, Rc, A]

--そのままでは成り立たないようで、方針転換。これはProblem Cのaxiomとして残っている。
lemma nds_nondec_contractRules
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α)) (Q : SCCQuot α V R)
  (hV : supportedOn V R) (nonemp : (Free (Q := Q)).Nonempty) :
  NDS2 V (family V R) ≤ NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) := by
  classical
  -- 記号短縮
  set S  : Finset (Finset α) := (Rep (Q := Q)).powerset
  set P  : Finset (Finset α) := familyRep (V := V) (R := R) (Q := Q)
  set NC : Finset (Finset α) := S.filter (fun B => B ∉ P)

  -- D2：R 側の大域上界
  have hD2 :=
    sum_fiber_bounds_to_debt_sum (V := V) (R := R) (Q := Q) nonemp
  -- Σ_main を 0 にする
  have hMain0 :
    ( (2 : Int) ^ (Free (Q := Q)).card
        * (∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) )
      = 0 := by
    have h := sum_main_over_powerset_eq_zero (V := V) (R := R) (Q := Q)
    -- `∑ … = 0` を左の因子で掛ける
    -- （掛け算の前取りを書換えで反映）
    exact by
      -- h : ∑_{B∈S} (...) = 0
      -- よって左辺 = (2^|Free|) * 0
      -- 以下は逐次 `rw` で
      -- まず和の部分を書き換える
      -- ここは関数等式 `congrArg` でまとめて置換しても良い
      have : ∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card) = 0 := h
      -- 置換
      -- (a) * (∑ …) = (a) * 0
      -- 仕上げに `mul_zero`
      exact (by
        rw [this]
        exact (by rw [Int.mul_zero]))
  -- よって D2 の右辺は Σ Debt のみに縮約
  have hStep_toDebt :
      ( (2 : Int) ^ (Free (Q := Q)).card
          * (∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        + ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B )
      = ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := by
    -- 0 + ΣDebt = ΣDebt
    -- 直前の hMain0 を使う
    -- 加法の第1項を 0 に
    -- 逐次 `rw` と `simp`
    have : ( (2 : Int) ^ (Free (Q := Q)).card
              * (∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) )
            = 0 := hMain0
    calc
      ( (2 : Int) ^ (Free (Q := Q)).card
          * (∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
        + ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B )
          = 0 + ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := by
                rw [this]
      _   = ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := by
                simp

  -- D2 の不等式の右辺を書換え：NDS2 ≤ Σ Debt
  have hA :
    NDS2 V (family V R) ≤ ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := by
    -- hD2 の右辺を `hStep_toDebt` で置換
    -- まず hD2 を展開
    -- NDS2 ≤ (2^|Free|)*Σ_main + Σ_Debt
    -- = Σ_Debt
    -- 最後に ≤ の右辺を書換え（等式置換で OK）
    -- `refine` と `rw` で段階的に
    have := hD2
    -- 右辺を等式で置換
    -- `rw` はゴール側で使うため、`calc` で明示化
    calc
      NDS2 V (family V R)
          ≤ ( (2 : Int) ^ (Free (Q := Q)).card
                * (∑ B ∈ S, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card))
              + ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B ) := this
      _   = ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := hStep_toDebt

  -- S 上の Debt を（閉＋非閉）に分解（C1）
  have hSplitDebt :
    ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B
      =
    ∑ B ∈ P,  Debt (V := V) (R := R) (Q := Q) B
    + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B := by
    -- 既証明の分割補題
    -- `sum_debt_split_by_familyRep`
    have := sum_debt_split_by_familyRep (V := V) (R := R) (Q := Q)
    -- S, P, NC の定義に合わせて `rfl`
    -- 右辺はちょうどこの形
    exact this

  -- 閉側は 0（既証明：sum_debt_on_familyRep_is_zero）
  have hFamZero :
    ∑ B ∈ P, Debt (V := V) (R := R) (Q := Q) B = 0 := by
    exact sum_debt_on_familyRep_is_zero (V := V) (R := R) (Q := Q)

  -- よって NDS2 ≤ 非閉側の Debt 総和
  have hB :
    NDS2 V (family V R) ≤ ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B := by
    -- hA の右辺を hSplitDebt で分解し、閉側 0 を代入
    have := hA
    -- 等式で右辺を書換え
    have : NDS2 V (family V R)
            ≤ ( ∑ B ∈ P, Debt (V := V) (R := R) (Q := Q) B
                + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B ) := by
      -- 置換だけ
      -- （等式で右辺を入れ替える）
      -- `calc` を使う
      calc
        NDS2 V (family V R)
            ≤ ∑ B ∈ S, Debt (V := V) (R := R) (Q := Q) B := hA
        _   = ( ∑ B ∈ P, Debt (V := V) (R := R) (Q := Q) B
                + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B ) := hSplitDebt
    -- 右辺の第1項（閉側）を 0 にする
    -- `have` を `rw` で反映
    -- ∑_P Debt = 0
    -- よって NDS2 ≤ 0 + ∑_NC Debt = ∑_NC Debt
    have := this
    -- 置換
    -- まず右辺の `∑_P Debt` を 0 に置換
    -- その後 `zero_add`
    -- 逐次 `rw` と `simp`
    have : NDS2 V (family V R)
            ≤ 0 + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B := by
      -- もとの不等式の右辺を書換え
      -- `rw [hFamZero]` を使う
      -- ただし `rw` はゴール右辺の内部に入るため、`conv` を使う方法もある
      -- ここでは `calc` をスキップして `rw` 直書き
      -- tactic 的に：
      --   have := this;
      --   exact ?_ ; (不等式はそのままなので `rw` が適用される)
      -- 直接：
      --   `rw [hFamZero] at this`
      -- ここでは段階的な calc にせず、`rw` を this に当ててから `exact` でも良いですが、
      -- そのまま書き換えを結果へ反映します。
      -- （簡潔のため、下で this を書き換えてから `exact` しています）
      exact by
        -- 上の this（不等式）に書換えを適用
        -- Lean では `have` を更新できないため、改めて記述
        -- ここは `calc` で書きます
        calc
          NDS2 V (family V R)
              ≤ ( ∑ B ∈ P, Debt (V := V) (R := R) (Q := Q) B
                  + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B ) := by
                    exact this
          _   = 0 + ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B := by
                    rw [hFamZero]
    -- 仕上げ
    -- 0 + t = t
    -- これで目標形になる
    exact by
      -- from: NDS2 ≤ 0 + Σ_NC Debt
      -- to:   NDS2 ≤ Σ_NC Debt
      have := this
      -- 書換
      -- `zero_add` を使う
      simpa using this

  -- 非閉 Debt の総和を R₁ の因数式で抑える（D3）
  have hAbsorb :
    ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B
      ≤ (2 : Int) ^ (Free (Q := Q)).card
            * (∑ B ∈ P, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) := by
    -- 既証明：debt_remainder_absorbed_by_R1_factorized ではない。
    sorry
    --exact debt_remainder_absorbed_by_R1_factorized (V := V) (R := R) (Q := Q)

  -- R₁ 側の因数式
  have hR1 :
    NDS2 V (family V (R1 (V := V) (R := R) (Q := Q)))
      = (2 : Int) ^ (Free (Q := Q)).card
          * (∑ B ∈ P, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) := by
    exact ThreadC.NDS2_family_contractRules_factorized (V := V) (R := R) (Q := Q) hV

  -- 連鎖して結論
  calc
    NDS2 V (family V R)
        ≤ ∑ B ∈ NC, Debt (V := V) (R := R) (Q := Q) B := hB
    _   ≤ (2 : Int) ^ (Free (Q := Q)).card
            * (∑ B ∈ P, ((2 : Int) * (B.card : Int) - (Rep (Q := Q)).card)) := hAbsorb
    _   = NDS2 V (family V (R1 (V := V) (R := R) (Q := Q))) := by
            -- 右辺を因数式で置換
            -- 等式の左右を入れ替えるために `symm` を使わず、calc で右辺に hR1 を適用
            -- ここは `rw [hR1]` でもよい
            -- 明示に `rw` で
            -- 書換
            -- hR1: NDS2 V (family V R1) = ...
            -- 逆向きで使うため `symm`
            have := hR1.symm
            exact this
