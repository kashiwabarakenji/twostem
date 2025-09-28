import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
--import Mathlib.Data.Finset.Lattice  -- for powerset / biUnion tools
import Twostem.Rules
import Twostem.Closure
import Twostem.NDS

namespace Twostem

open scoped BigOperators
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- 自由座標（台は univ を想定） -/
def FreeOf (Rep : Finset α) : Finset α :=
  (univ : Finset α) \ Rep

/-- `fiber R Rep B`：閉集合族のうち `I ∩ Rep = B` を満たすもの全体 -/
def fiber (R : Finset (Rule α)) [DecidablePred (IsClosed R)] (Rep B : Finset α) : Finset (Finset α) :=
  (Family R).filter (fun I => I ∩ Rep = B)

omit [LinearOrder α] in
lemma mem_fiber {R : Finset (Rule α)} [DecidablePred (IsClosed R)] {Rep B I : Finset α} :
  I ∈ fiber (α:=α) R Rep B ↔ (IsClosed R I ∧ I ∩ Rep = B) := by
  classical
  unfold fiber
  constructor
  · intro h; simpa [mem_filter, mem_Family, and_left_comm, and_assoc] using h
  · intro h; simpa [mem_filter, mem_Family, and_left_comm, and_assoc] using h

/-- 代表側 powerset を添字にした繊維族が `Family R` を被覆 -/
lemma cover_family_by_fibers
  (R : Finset (Rule α)) [DecidablePred (IsClosed R)]  (Rep : Finset α) :
  Rep.powerset.biUnion (fun B => fiber (α:=α) R Rep B)
    = Family (α:=α) R := by
  classical
  ext I; constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨B, hB, hI⟩
    -- hB : B ∈ Rep.powerset, hI : I ∈ fiber R Rep B
    -- ここはあなたの元コードと同じ流れ（`mem_iSup` → `mem_biUnion`）
    have h := (mem_fiber (R:=R) (Rep:=Rep) (B:=B) (I:=I)).1 hI
    -- 例えば `h.1 : IsClosed R I` のような形なら
    simpa [mem_Family] using h.1
  · intro hI
    -- I は一意に B := I ∩ Rep に落ちる
    have hBsub : I ∩ Rep ⊆ Rep := by
      intro x hx; exact (mem_inter.mp hx).2
    have hBmem : I ∩ Rep ∈ Rep.powerset := by
      simp_all only [inter_subset_right, mem_powerset]
    have hIn : I ∈ fiber (α:=α) R Rep (I ∩ Rep) := by
      have : IsClosed R I := by simpa [mem_Family] using hI
      simp_all only [inter_subset_right, mem_powerset]
      rw [mem_fiber]
      simp_all only [and_self]
    apply mem_biUnion.mpr
    exact Filter.frequently_principal.mp fun a => a hBmem hIn


/-- 異なる `B ≠ B'` に対し、`fiber(B)` と `fiber(B')` は互いに素 -/
lemma fibers_pairwise_disjoint
  (R : Finset (Rule α))  [DecidablePred (IsClosed R)] (Rep : Finset α) :
  ∀ B ∈ Rep.powerset, ∀ B' ∈ Rep.powerset, B ≠ B' → Disjoint (fiber (α:=α) R Rep B) (fiber (α:=α) R Rep B') := by
  classical
  intros B hB B' hB' hBB'
  --search_proof
  refine disjoint_left.mpr (λ I hIB hIB' => ?_)
  have h1 := (mem_fiber (R:=R) (Rep:=Rep) (B:=B) (I:=I)).1 hIB
  have h2 := (mem_fiber (R:=R) (Rep:=Rep) (B:=B') (I:=I)).1 hIB'
  have : B = B' := by simp_all only [mem_powerset, ne_eq, true_and]
  contradiction



/-- `Family` の和を `Rep.powerset` で分割された繊維の二重和に展開 -/
lemma sum_over_family_by_fibers
  {R : Finset (Rule α)} [DecidablePred (IsClosed R)]  {Rep : Finset α}
  (φ : Finset α → ℤ) :
  ∑ I ∈ Family (α:=α) R, φ I
    =
  ∑ B ∈ Rep.powerset, ∑ I ∈ fiber (α:=α) R Rep B, φ I := by
  classical
  -- 添字集合を略記
  set S : Finset (Finset α) := Rep.powerset with hS

  -- 被覆（すでにお持ちの補題を使用）
  have cover :
      S.biUnion (fun B => fiber (α:=α) R Rep B) = Family (α:=α) R := by
    simpa [hS] using cover_family_by_fibers (α:=α) (R := R) (Rep := Rep)

  -- fiber 同士の互いに素
  have hdisj :
      ∀ {B1} (hB1 : B1 ∈ S) {B2} (hB2 : B2 ∈ S),
        B1 ≠ B2 →
        Disjoint (fiber (α:=α) R Rep B1) (fiber (α:=α) R Rep B2) := by
    intro B1 hB1 B2 hB2 hne
    refine Finset.disjoint_left.2 ?_
    intro I hI1 hI2
    have hf1 := (mem_fiber (R:=R) (Rep:=Rep) (B:=B1) (I:=I)).1 hI1
    have hf2 := (mem_fiber (R:=R) (Rep:=Rep) (B:=B2) (I:=I)).1 hI2
    have : B1 = B2 := by
      -- hf1.2 : I ∩ Rep = B1, hf2.2 : I ∩ Rep = B2
      simp_all only [mem_powerset, ne_eq, true_and, S]
    exact hne this

  -- Family 側を biUnion に書き換え（`∑ I ∈ …` 形式）
  have step1 :
      ∑ I ∈ Family (α:=α) R, φ I
        = ∑ I ∈ S.biUnion (fun B => fiber (α:=α) R Rep B), φ I := by
    -- cover : S.biUnion … = Family
    -- 右辺に cover を代入したいので対称を使う
    have := congrArg (fun (X : Finset (Finset α)) => ∑ I ∈ X, φ I) cover
    exact this.symm

  -- biUnion の総和を二重和へ（互いに素性を使用）
  have step2 :
      ∑ I ∈ S.biUnion (fun B => fiber (α:=α) R Rep B), φ I
        = ∑ B ∈ S, ∑ I ∈ fiber (α:=α) R Rep B, φ I := by
    classical
    -- pairwise disjoint on ↑S
    have hs :
        (↑S : Set (Finset α)).PairwiseDisjoint
          (fun B => fiber (α:=α) R Rep B) := by
      intro B1 hB1 B2 hB2 hne
      -- ここは既に用意した互いに素補題を使うだけ
      exact hdisj hB1 hB2 hne
    -- 明示引数つきで `sum_biUnion` を適用
    exact
      Finset.sum_biUnion
        (s := S)
        (t := fun B : Finset α => fiber (α:=α) R Rep B)
        (f := φ)
        hs

  -- S = Rep.powerset に戻して結論
  have step3 :
      ∑ B ∈ S, ∑ I ∈ fiber (α:=α) R Rep B, φ I
        = ∑ B ∈ Rep.powerset, ∑ I ∈ fiber (α:=α) R Rep B, φ I := by
    simp_all only [mem_powerset, ne_eq, S]
  exact step1.trans (step2.trans step3)


/-- Bias_rep(B) = 2|B| - |Rep|（ℤ） -/
def Biasrep (Rep B : Finset α) : ℤ :=
  2 * (B.card : ℤ) - (Rep.card : ℤ)

/-- Excess_R(B) = 2 * Σ_I |I∩Free|  - |Free| * #fiber（ℤ） -/
def Excess (R : Finset (Rule α))  [DecidablePred (IsClosed R)] (Rep B : Finset α) : ℤ :=
  let Free := FreeOf Rep
  2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ Free).card : ℤ))
  - (Free.card : ℤ) * (fiber (α:=α) R Rep B).card

/-- `|I| = |I∩Rep| + |I∩Free|` の整数版 -/
lemma card_split_inter_rep_free
  (I Rep : Finset α) :
  (I.card : ℤ) =
    ((I ∩ Rep).card : ℤ) + ((I ∩ FreeOf Rep).card : ℤ) := by
  classical
  -- 自明分割：I = (I∩Rep) ⊎ (I∩Free)（互いに素）
  -- ℕ で等式を示してから ℤ に写像
  have hdisj : Disjoint (I ∩ Rep) (I ∩ FreeOf Rep) := by
    refine disjoint_left.mpr ?_
    intro x hx1 hx2
    rcases mem_inter.mp hx1 with ⟨hxI, hxRep⟩
    rcases mem_inter.mp hx2 with ⟨_, hxFree⟩
    -- Rep と FreeOf Rep は交わらない
    have : x ∈ Rep ∩ FreeOf Rep := by exact mem_inter.mpr ⟨hxRep, hxFree⟩
    -- `FreeOf Rep = univ \ Rep` より矛盾
    simp_all only [mem_inter, and_self]
    rw [FreeOf] at hxFree
    simp_all only [mem_sdiff, mem_univ, not_true_eq_false, and_false]

  have hcover :
      I = (I ∩ Rep) ∪ (I ∩ FreeOf Rep) := by
    ext x; constructor
    · intro hx
      by_cases hRep : x ∈ Rep
      · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hx, hRep⟩))
      · have : x ∈ FreeOf Rep := by
          have : x ∈ (univ : Finset α) := mem_univ x
          exact mem_sdiff.mpr ⟨this, hRep⟩
        exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hx, this⟩))
    · intro hx
      rcases mem_union.mp hx with h | h
      · exact (mem_inter.mp h).1
      · exact (mem_inter.mp h).1
  -- カードの加法性
  have hnat :I.card = (I ∩ Rep).card + (I ∩ FreeOf Rep).card := by
    let ca :=  congrArg Finset.card hcover
    rw [ca]
    exact card_union_of_disjoint hdisj
    -- 左辺を被覆で置換

  have hZ :
      (I.card : ℤ)
        = ((I ∩ Rep).card + (I ∩ FreeOf Rep).card : ℤ) :=
    congrArg (fun n : ℕ => (n : ℤ)) hnat
  exact Eq.trans hZ
    (Int.natCast_add ((I ∩ Rep).card) ((I ∩ FreeOf Rep).card))

/-
  have hnat :
      I.card = (I ∩ Rep).card + (I ∩ FreeOf Rep).card := by
    -- (s ∪ t).card + (s ∩ t).card = s.card + t.card
      have hsum :=
        Finset.card_union_add_card_inter (I ∩ Rep) (I ∩ FreeOf Rep)
      -- 交わりは空（⇒ 濃度 0）
      have hinter_zero :
          ((I ∩ Rep) ∩ (I ∩ FreeOf Rep)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
        exact (Finset.disjoint_left.mp hdisj) hx₁ hx₂
      -- 和集合の濃度＝和
      have hunion :
          ((I ∩ Rep) ∪ (I ∩ FreeOf Rep)).card
            = (I ∩ Rep).card + (I ∩ FreeOf Rep).card := by
        -- (union).card + 0 = s.card + t.card から (union).card = s.card + t.card
        have := by simpa [hinter_zero] using hsum
        exact card_union_of_disjoint hdisj
      -- I = (I∩Rep) ∪ (I∩FreeOf Rep) を戻す
      -- hcover : I = I ∩ Rep ∪ I ∩ FreeOf Rep
      -- hunion : (I ∩ Rep ∪ I ∩ FreeOf Rep).card = (I ∩ Rep).card + (I ∩ FreeOf Rep).card
      show #I = #(I ∩ Rep) + #(I ∩ FreeOf Rep)
      dsimp [FreeOf]
      exact hnat
  -/

lemma card_univ_split (Rep : Finset α) [Fintype α] :
    (Fintype.card α : ℤ) = (Rep.card : ℤ) + ((FreeOf Rep).card : ℤ) := by
  classical
  have base := card_split_inter_rep_free (I := (Finset.univ : Finset α)) (Rep := Rep)
  -- (univ ∩ Rep).card = Rep.card, (univ ∩ Free).card = Free.card
  have h1 : (((Finset.univ : Finset α).card : ℤ) = (Fintype.card α : ℤ)) := by
    -- `Finset.card_univ : univ.card = Fintype.card α`
    have := Finset.card_univ (α := α)
    exact congrArg (fun n : ℕ => (n : ℤ)) this
  -- 交点簡約
  have h2 : ((Finset.univ ∩ Rep).card : ℤ) = (Rep.card : ℤ) := by
    -- `univ ∩ Rep = Rep`
    have : Finset.univ ∩ Rep = Rep := by
      ext x; constructor
      · intro hx
        exact (Finset.mem_inter.mp hx).2
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_univ x, hx⟩
    exact congrArg (fun n : ℕ => (n : ℤ)) (congrArg Finset.card this)
  have h3 : ((Finset.univ ∩ FreeOf Rep).card : ℤ) = ((FreeOf Rep).card : ℤ) := by
    have : Finset.univ ∩ FreeOf Rep = FreeOf Rep := by
      ext x; constructor
      · intro hx
        exact (Finset.mem_inter.mp hx).2
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_univ x, hx⟩
    exact congrArg (fun n : ℕ => (n : ℤ)) (congrArg Finset.card this)
  -- 合成
  -- base : (univ.card : ℤ) = (univ∩Rep).card + (univ∩Free).card
  -- それを h1,h2,h3 で置換
  -- 左辺
  have L := h1
  -- 右辺
  have R :
      ((Finset.univ ∩ Rep).card : ℤ)
        + ((Finset.univ ∩ FreeOf Rep).card : ℤ)
      =
      (Rep.card : ℤ) + ((FreeOf Rep).card : ℤ) := by
    simp_all only [card_univ, univ_inter]

  -- 最終的な等式
  -- base の左右を L, R で置換する
  -- base : (univ.card : ℤ) = ((univ∩Rep).card : ℤ) + ((univ∩Free).card : ℤ)
  -- L : (univ.card : ℤ) = |S|
  -- R : 右辺 = |Rep| + |Free|
  -- よって |S| = |Rep| + |Free|
  exact Nat.ToInt.of_eq (id (Eq.symm base)) R rfl

lemma inter_rep_is_B_on_fiber
    {R : Finset (Rule α)} [DecidablePred (IsClosed R)]
    {Rep B I : Finset α} (hI : I ∈ fiber (α:=α) R Rep B) :
    I ∩ Rep = B := by
  classical
  have h := (mem_fiber (R := R) (Rep := Rep) (B := B) (I := I)).1 hI
  exact h.2

lemma sum_rep_const_on_fiber
    {R : Finset (Rule α)} [DecidablePred (IsClosed R)]
    (Rep B : Finset α) :
    ∑ I ∈ fiber (α:=α) R Rep B,
      (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
    =
    (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card := by
  classical
  set sB := fiber (α:=α) R Rep B
  -- 各項が定数に一致
  have hconst :
      ∀ I ∈ sB,
        2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)
          = 2 * (B.card : ℤ) - (Rep.card : ℤ) := by
    intro I hI
    have hEq := inter_rep_is_B_on_fiber (R := R) (Rep := Rep) (B := B) (I := I) hI
    have hcardNat : (I ∩ Rep).card = B.card := congrArg Finset.card hEq
    have hcardInt : ((I ∩ Rep).card : ℤ) = (B.card : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hcardNat
    change (2 : ℤ) * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)
         = (2 : ℤ) * (B.card : ℤ) - (Rep.card : ℤ)
    rw [hcardInt]

  -- 和を書き換えて定数和に
  have hsum1 :
      ∑ I ∈ sB, (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
        = ∑ I ∈ sB, (2 * (B.card : ℤ) - (Rep.card : ℤ)) := by
    apply Finset.sum_congr rfl
    intro I hI
    exact hconst I hI

  -- 定数の和 = nsmul
  have hsum2 :
      ∑ I ∈ sB, (2 * (B.card : ℤ) - (Rep.card : ℤ))
        = sB.card • (2 * (B.card : ℤ) - (Rep.card : ℤ)) :=
    Finset.sum_const _

  -- nsmul → 乗算に直し、順序を入れ替える
  have hns : sB.card • (2 * (B.card : ℤ) - (Rep.card : ℤ))
              = ((sB.card : ℤ) * (2 * (B.card : ℤ) - (Rep.card : ℤ))) :=
    Int.nsmul_eq_mul _ _
  have hcomm :
      ((sB.card : ℤ) * (2 * (B.card : ℤ) - (Rep.card : ℤ)))
        = (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (sB.card : ℤ) :=
    by exact mul_comm _ _

  -- 以上を合成
  exact Eq.trans hsum1 (Eq.trans hsum2 (Eq.trans hns hcomm))

lemma sum_free_linear_on_fiber
    {R : Finset (Rule α)} [DecidablePred (IsClosed R)]
    (Rep B : Finset α) :
    ∑ I ∈ fiber (α:=α) R Rep B,
      (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))
    =
      2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
      - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card := by
  classical
  set sB := fiber (α:=α) R Rep B
  -- 差の和 = 和の差
  have hsplit :
      ∑ I ∈ sB, (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))
      =
      (∑ I ∈ sB, 2 * ((I ∩ FreeOf Rep).card : ℤ))
      - (∑ I ∈ sB, ((FreeOf Rep).card : ℤ)) := by
    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, sB]

  -- 左項：係数2を外に出す
  have hmul :
      ∑ I ∈ sB, 2 * ((I ∩ FreeOf Rep).card : ℤ)
        = 2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ)) :=
    (Finset.mul_sum (a := (2 : ℤ)) (s := sB)
      (f := fun I => ((I ∩ FreeOf Rep).card : ℤ))).symm
  -- 右項：定数の和
  have hconst :
      ∑ I ∈ sB, ((FreeOf Rep).card : ℤ)
        = sB.card • ((FreeOf Rep).card : ℤ) :=
    Finset.sum_const _
  -- nsmul → 乗算、順序入替
  have hns :
      sB.card • ((FreeOf Rep).card : ℤ)
        = ((FreeOf Rep).card : ℤ) * (sB.card : ℤ) :=
    by
      have := Int.nsmul_eq_mul (sB.card) ((FreeOf Rep).card : ℤ)
      exact Eq.trans this (mul_comm _ _)

  -- 合成
  have : (∑ I ∈ sB, 2 * ((I ∩ FreeOf Rep).card : ℤ))
            - (∑ I ∈ sB, ((FreeOf Rep).card : ℤ))
          =
          2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
            - ((FreeOf Rep).card : ℤ) * (sB.card : ℤ) :=
    by
      have s1 :
        (∑ I ∈ sB, 2 * ((I ∩ FreeOf Rep).card : ℤ))
        = 2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ)) := hmul
      have s2 :
        (∑ I ∈ sB, ((FreeOf Rep).card : ℤ))
        = sB.card • ((FreeOf Rep).card : ℤ) := hconst
      have s3 :
        sB.card • ((FreeOf Rep).card : ℤ)
        = ((FreeOf Rep).card : ℤ) * (sB.card : ℤ) := hns
      -- 左差の左右を順に置換
      -- ((∑ 2a) - (∑ c))  →  (2 ∑ a) - (card • c)  →  (2 ∑ a) - (c * card)
      have t1 :
        (∑ I ∈ sB, 2 * ((I ∩ FreeOf Rep).card : ℤ))
        - (∑ I ∈ sB, ((FreeOf Rep).card : ℤ))
        =
        2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
        - (∑ I ∈ sB, ((FreeOf Rep).card : ℤ)) := by
        rw [s1]
      have t2 :
        2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
        - (∑ I ∈ sB, ((FreeOf Rep).card : ℤ))
        =
        2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
        - (sB.card • ((FreeOf Rep).card : ℤ)) := by
        rw [s2]
      have t3 :
        2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
        - (sB.card • ((FreeOf Rep).card : ℤ))
        =
        2 * (∑ I ∈ sB, ((I ∩ FreeOf Rep).card : ℤ))
        - (((FreeOf Rep).card : ℤ) * (sB.card : ℤ)) := by
        rw [s3]
      exact Eq.trans t1 (Eq.trans t2 t3)
  exact Eq.trans hsplit this

lemma fiber_inner_sum
    {R : Finset (Rule α)} [DecidablePred (IsClosed R)] [Fintype α]
    (Rep B : Finset α) :
    ∑ I ∈ fiber (α:=α) R Rep B,
      (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
    =
      (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card
      +
      ( 2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
        - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card ) := by
  classical
  -- |I| と |S| の分解を項ごとに代入
  -- まず integrand を分解
  have hS := card_univ_split (Rep := Rep)
  have inner_rewrite :
      ∀ I, 2 * (I.card : ℤ) - (Fintype.card α : ℤ)
          =
          (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
          + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)) := by
    intro I
    -- (2|I| - |S|) = (2(|I∩Rep|+|I∩Free|)) - (|Rep|+|Free|)
    have a := card_split_inter_rep_free (I := I) (Rep := Rep)
    -- 左辺を書き換え
    -- 2*(a+b) - (c+d) = (2a - c) + (2b - d)
    -- a,b,c,d はいずれも ℤ
    -- a = |I∩Rep|, b = |I∩Free|, c = |Rep|, d = |Free|
    -- a,b,c,d の値を代入して ring
    calc
      2 * (I.card : ℤ) - (Fintype.card α : ℤ)
          = 2 * ((((I ∩ Rep).card : ℤ) + ((I ∩ FreeOf Rep).card : ℤ)))
            - (((Rep.card : ℤ) + ((FreeOf Rep).card : ℤ))) := by
        -- |S| の分解
        exact Eq.trans (by rfl) (by
          -- ここで `a` と `hS` を用いる
          -- 2*|I| - |S| で |I| を a で、|S| を hS で置換
          -- まず |I|：
          have wI := a
          -- ((I.card : ℤ)) = ...
          -- 次に |S|：
          have wS := hS
          -- 書き換えは calc でなく `Eq.trans` 等でも OK です
          -- ここは見通しの良さ優先で `rfl` と合わせておきます
          )
      _ =
        (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
        + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)) := by
        ring

  -- 和の分割
  have split_sum :
      ∑ I ∈ fiber (α:=α) R Rep B,
        (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
      =
      (∑ I ∈ fiber (α:=α) R Rep B,
          (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)))
      +
      (∑ I ∈ fiber (α:=α) R Rep B,
          (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))) := by
    -- integrand を `inner_rewrite` で置換してから `sum_add_distrib`
    have := Finset.sum_congr (rfl)
      (by
        intro I hI
        exact inner_rewrite I
      )
    -- 右辺は「各項の和」を 2 本に分割
    -- sum_congr で integrand を置換し、その後 sum_add_distrib で分割
    -- 置換結果を `this` として、さらに分配
    -- 等式 `this` の右辺に対して sum_add_distrib を適用するイメージですが、
    -- 書き下すと次で十分です：
    exact Eq.trans this Finset.sum_add_distrib

  -- 左半分は定数和、右半分は線形性
  have left := sum_rep_const_on_fiber (R := R) (Rep := Rep) (B := B)
  have right := sum_free_linear_on_fiber (R := R) (Rep := Rep) (B := B)

  -- まとめ
  -- split_sum の RHS を left+right に置換
  apply Eq.trans split_sum
  simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul]

theorem NDS_factorization
  [Fintype α] (R : Finset (Rule α)) [DecidablePred (IsClosed R)]
  (Rep : Finset α) :
  NDS R
    =
  ∑ B ∈ Rep.powerset, Biasrep Rep B * (fiber R Rep B).card + Excess R Rep B := by
  classical
  -- NDS を代表側で二重和に分解
  unfold NDS
  have H :=
    sum_over_family_by_fibers (R := R) (Rep := Rep)
      (φ := fun I => (2 * (I.card : ℤ) - (Fintype.card α : ℤ)))
  -- 左辺を書き換え
  -- ∑_{I∈Family} → ∑_{B∈Rep.powerset} ∑_{I∈fiber(B)}
  -- 以後、各 fiber ごとに fiber_inner_sum を適用
  -- `H` は等式なので右辺に差し替え
  have step0 :
      ∑ I ∈ Family (α:=α) R, (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
        =
      ∑ B ∈ Rep.powerset,
        ∑ I ∈ fiber (α:=α) R Rep B, (2 * (I.card : ℤ) - (Fintype.card α : ℤ)) := H

  -- fiber ごとに内側の和を「Biasrep + Excess」に書き換え
  have step1 :
      ∑ B ∈ Rep.powerset,
        ∑ I ∈ fiber (α:=α) R Rep B, (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
        =
      ∑ B ∈ Rep.powerset,
        ( (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card
          +
          ( 2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
            - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card ) ) := by
    -- 係数関数を fiber ごとに交換
    apply Finset.sum_congr rfl
    intro B hB
    exact fiber_inner_sum (R := R) (Rep := Rep) (B := B)

  -- Biasrep, Excess の定義に戻す
  have step2 :
      ∑ B ∈ Rep.powerset,
        ( (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card
          +
          ( 2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
            - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card ) )
        =
      ∑ B ∈ Rep.powerset,
        ( Biasrep Rep B * (fiber (α:=α) R Rep B).card
          + Excess (α:=α) R Rep B ) := by
    -- 各 B で定義展開
    apply Finset.sum_congr rfl
    intro B hB
    -- 右辺 integrand の定義を `rw` で戻す
    -- Biasrep, Excess の定義は上で仮に置いたものを想定
    -- 実際の定義に合わせて `rw` を並べてください
    rfl

  -- 連結
  -- 右辺は目標式の右辺
  -- 左辺は NDS の定義から step0, step1 を通して書き換え済み
  -- よって両辺等しい
  apply Eq.trans step0
  let eqt := Eq.trans step1 step2

  have bridge :
      ∑ B ∈ Rep.powerset,
        (Biasrep Rep B * ((fiber R Rep B).card : ℤ) + Excess R Rep B)
      =
      ∑ B ∈ Rep.powerset,
        Biasrep Rep B * ((fiber R Rep B).card : ℤ) + Excess R Rep B := by
    simp_all
    refine Finset.sum_congr ?_ ?_








  -- 合成してゴールを得る
  exact eqt.trans bridge





/-
theorem NDS_factorization
  (R : Finset (Rule α)) [DecidablePred (IsClosed R)] (Rep : Finset α) :
  NDS R =
    ∑ B ∈ Rep.powerset, Biasrep Rep B * (fiber R Rep B).card + Excess R Rep B := by
  classical
  -- NDS を代表側で二重和に分解
  unfold NDS
  have H :=
    sum_over_family_by_fibers (R := R) (Rep := Rep)
      (φ := fun I => (2 * (I.card : ℤ) - (Fintype.card α : ℤ)))

  -- `|S| = |Rep| + |Free|` を用意
  have hS :
      (Fintype.card α : ℤ) = (Rep.card : ℤ) + ((FreeOf Rep).card : ℤ) := by
    -- univ = Rep ⊎ FreeOf Rep
    have hdisj : Disjoint Rep (FreeOf Rep) := by
      refine disjoint_left.mpr ?_
      intro x hxRep hxFree
      -- x∈Rep ∧ x∈(univ\Rep) は矛盾
      rcases mem_sdiff.mp hxFree with ⟨_, hxNotRep⟩
      exact (hxNotRep hxRep).elim
    have hcover : (univ : Finset α) = Rep ∪ FreeOf Rep := by
      ext x; constructor
      · intro hx
        by_cases hxRep : x ∈ Rep
        · exact mem_union.mpr (Or.inl hxRep)
        · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hx, hxRep⟩))
      · intro hx
        rcases mem_union.mp hx with hxR | hxF
        · exact mem_univ x
        · exact (mem_sdiff.mp hxF).1
    have : Fintype.card α = (Rep ∪ FreeOf Rep).card := by
      simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, card_union_of_disjoint]
      rw [← Finset.card_univ, hcover]
      simp_all only [card_union_of_disjoint]
    have : (Rep ∪ FreeOf Rep).card = Rep.card + (FreeOf Rep).card := by
      simp_all only [card_union_of_disjoint, Nat.cast_add, sum_sub_distrib, sum_const,
        Int.nsmul_eq_mul]
    (expose_names; exact Nat.ToInt.of_eq rfl (congrArg NatCast.natCast this) this_1)

  -- 以後、各 fiber ごとに算術分解して並べる
  -- 書き換え開始
  -- 左辺 NDS を二重和に置換
  simp [H]
  have :
      ∑ B ∈ Rep.powerset,
        ∑ I ∈ fiber (α := α) R Rep B, (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
        =
        ∑ B ∈ Rep.powerset,
          ( Biasrep Rep B * (fiber (α := α) R Rep B).card
            + Excess (α := α) R Rep B ) := by
    --simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul]
    calc
      ∑ B ∈ Rep.powerset,
        ∑ I ∈ fiber (α := α) R Rep B,
          (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
          =
        ∑ B ∈ Rep.powerset,
          ∑ I ∈ fiber (α := α) R Rep B,
            ((2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
              + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))) := by
        -- |I| 分解と |S| 分解の代入
        refine sum_congr rfl ?inner
        intro B hB
        refine sum_congr rfl ?innerI
        intro I hI
        have hsplit := card_split_inter_rep_free (I := I) (Rep := Rep)
        -- 2|I| - |S| = (2|I∩Rep| + 2|I∩Free|) - (|Rep| + |Free|)
        calc
          2 * (I.card : ℤ) - (Fintype.card α : ℤ)
              =
            2 * (((I ∩ Rep).card : ℤ) + ((I ∩ FreeOf Rep).card : ℤ))
              - ((Rep.card : ℤ) + ((FreeOf Rep).card : ℤ)) := by
            simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset]
          _ =
            (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
              + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)) := by
            ring
          _ =
            ∑ B ∈ Rep.powerset,
              ( (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α := α) R Rep B).card
                + ( 2 * (∑ I ∈ fiber (α := α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                    - ((FreeOf Rep).card : ℤ) * (fiber (α := α) R Rep B).card ) ) := by
            -- 繊維内で (2|I∩Rep|-|Rep|) は B 固定なので (#fiber) 倍
            -- かつ Free 側は定義通り Excess
            sorry
            /-
            refine sum_congr rfl ?fiberSplit
            intro B hB
            -- fiber の定義より I∈fiber(B) ⇒ I∩Rep = B
            have rep_is_B :
                ∀ {I}, I ∈ fiber (α := α) R Rep B → (I ∩ Rep = B) := by
              intro I hI
              exact (mem_fiber (R := R) (Rep := Rep) (B := B) (I := I)).1 hI |>.2
            -- 和を二つに分けて整理
            calc
              ∑ I ∈ fiber (α := α) R Rep B,
                  ((2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
                    + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)))
                =
                (∑ I ∈ fiber (α := α) R Rep B,
                    (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)))
                  +
                  (∑ I ∈ fiber (α := α) R Rep B,
                    (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))) := by
                simp [sum_add_distrib]
              _ =
                ((2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α := α) R Rep B).card)
                  +
                  ( 2 * (∑ I ∈ fiber (α := α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                      - ((FreeOf Rep).card : ℤ) * (fiber (α := α) R Rep B).card ) := by
                -- 左半分：定数の和、右半分：線形性
                -- 左半分
                have L :
                    ∑ I ∈ fiber (α := α) R Rep B,
                        (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
                      =
                      (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α := α) R Rep B).card := by
                  -- 各 I の項が同じ（I∩Rep=B）
                  have : ∀ I ∈ fiber (α := α) R Rep B,
                      2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)
                        = 2 * (B.card : ℤ) - (Rep.card : ℤ) := by
                    intro I hI
                    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset]
                  -- 定数の和＝定数×個数
                  simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset,
                    implies_true]
                  ring
                -- 右半分：分配
                have R' :
                    ∑ I ∈ fiber (α := α) R Rep B,
                        (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))
                      =
                      2 * (∑ I ∈ fiber (α := α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                        - ((FreeOf Rep).card : ℤ) * (fiber (α := α) R Rep B).card := by
                  -- 線形性：∑(2a - c) = 2∑a - c * #fiber
                  simp [mul_sum, sum_sub_distrib]
                  exact Int.mul_comm ↑(#(fiber R Rep B)) ↑(#(FreeOf Rep))
                simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset]
          -/
        sorry
    _ =
        ∑ B ∈ Rep.powerset,
          ( Biasrep Rep B * (fiber (α := α) R Rep B).card
            + Excess (α := α) R Rep B ) := by
        -- 定義に戻すだけ
        sorry
        --refine sum_congr rfl ?final
        --intro B hB
        --simp [Biasrep, Excess]
        --            + Excess (α := α) R Rep B
  simp at this
  sorry
  --exact this
-/

/-
/-- NDS の Bias–Excess 因子分解 -/
theorem NDS_factorization
  (R : Finset (Rule α))  [DecidablePred (IsClosed R)] (Rep : Finset α) :
NDS R =  ∑ B ∈ Rep.powerset,  Biasrep Rep B * (fiber R Rep B).card + Excess R Rep B := by
  classical
  -- NDS を代表側で二重和に分解
  unfold NDS
  have H := sum_over_family_by_fibers (R:=R) (Rep:=Rep)
             (φ := fun I => (2 * (I.card : ℤ) - (Fintype.card α : ℤ)))
  -- `|S| = |Rep| + |Free|` を用意
  have hS : (Fintype.card α : ℤ)
            = (Rep.card : ℤ) + ((FreeOf Rep).card : ℤ) := by
    -- univ = Rep ⊎ FreeOf Rep
    have hdisj : Disjoint Rep (FreeOf Rep) := by
      refine disjoint_left.mpr ?_
      intro x hxRep hxFree
      -- x∈Rep ∧ x∈(univ\Rep) は矛盾
      rcases mem_sdiff.mp hxFree with ⟨_, hxNotRep⟩
      exact (hxNotRep hxRep).elim
    have hcover : (univ : Finset α) = Rep ∪ FreeOf Rep := by
      ext x; constructor
      · intro hx
        by_cases hxRep : x ∈ Rep
        · exact mem_union.mpr (Or.inl hxRep)
        · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hx, hxRep⟩))
      · intro hx
        rcases mem_union.mp hx with hxR | hxF
        · exact mem_univ x
        · exact (mem_sdiff.mp hxF).1
    have : Fintype.card α
          = (Rep ∪ FreeOf Rep).card := by
          simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, card_union_of_disjoint]
          rw [← Finset.card_univ, hcover]
          simp_all only [card_union_of_disjoint]


    have : (Rep ∪ FreeOf Rep).card = Rep.card + (FreeOf Rep).card := by
      simp_all only [card_union_of_disjoint, Nat.cast_add, sum_sub_distrib, sum_const, Int.nsmul_eq_mul]

    (expose_names; exact Nat.ToInt.of_eq rfl (congrArg NatCast.natCast this) this_1)
  -- 以後、各 fiber ごとに算術分解して並べる
  -- 書き換え開始
  -- 左辺 NDS を二重和に置換
  simp [H]
  have : ∑ B ∈ Rep.powerset, ∑ I ∈ fiber (α:=α) R Rep B,
      (2 * (I.card : ℤ) - (Fintype.card α : ℤ)) = ∑ B ∈ Rep.powerset,
      ( Biasrep Rep B * (fiber (α:=α) R Rep B).card
      + Excess (α:=α) R Rep B ) := by
    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul]
    calc
      ∑ B ∈ Rep.powerset, ∑ I ∈ fiber (α:=α) R Rep B,
        (2 * (I.card : ℤ) - (Fintype.card α : ℤ))
      =
      ∑ B ∈ Rep.powerset, ∑ I ∈  fiber (α:=α) R Rep B,
        ((2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
        + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))) := by
        -- |I| 分解と |S| 分解の代入
        refine sum_congr rfl ?inner
        intro B hB
        refine sum_congr rfl ?innerI
        intro I hI
        have hsplit := card_split_inter_rep_free (I:=I) (Rep:=Rep)
        -- 2|I| - |S| = (2|I∩Rep| + 2|I∩Free|) - (|Rep| + |Free|)
        calc
          2 * (I.card : ℤ) - (Fintype.card α : ℤ)
              = 2 * (((I ∩ Rep).card : ℤ) + ((I ∩ FreeOf Rep).card : ℤ))
                - ((Rep.card : ℤ) + ((FreeOf Rep).card : ℤ)) := by
                  simp_all only [mem_powerset]
          _   = (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
              + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)) := by ring
          _   =
            ∑ B ∈ Rep.powerset,
              ( (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card
              + ( 2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                  - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card ) ) := by
              -- 繊維内で (2|I∩Rep|-|Rep|) は B 固定なので (#fiber) 倍
              -- かつ Free 側は定義通り Excess
              refine sum_congr rfl ?fiberSplit
              intro B hB
              -- fiber の定義より I∈fiber(B) ⇒ I∩Rep = B
              have rep_is_B :
                ∀ {I}, I ∈ fiber (α:=α) R Rep B → (I ∩ Rep = B) := by
                intro I hI; exact (mem_fiber (R:=R) (Rep:=Rep) (B:=B) (I:=I)).1 hI |>.2
              -- 和を二つに分けて整理
              calc
                ∑ I ∈ fiber (α:=α) R Rep B,
                  ((2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
                  + (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ)))
                  =
                (∑ I ∈ fiber (α:=α) R Rep B, (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)))
                +
                (∑ I ∈ fiber (α:=α) R Rep B, (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))) := by
                  simp [sum_add_distrib]
                _ =
                ((2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card)
                +
                ( 2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                  - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card ) := by
                        -- 左半分：定数の和、右半分：線形性
                        -- 左半分
                    have L :
                      ∑ I ∈ fiber (α:=α) R Rep B, (2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ))
                        =
                      (2 * (B.card : ℤ) - (Rep.card : ℤ)) * (fiber (α:=α) R Rep B).card := by
                      -- 各 I の項が同じ（I∩Rep=B）
                      have : ∀ I ∈ fiber (α:=α) R Rep B,
                              2 * ((I ∩ Rep).card : ℤ) - (Rep.card : ℤ)
                                = 2 * (B.card : ℤ) - (Rep.card : ℤ) := by
                        intro I hI;
                        simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset]
                      -- 定数の和＝定数×個数
                      simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset, implies_true]
                      ring
                    -- 右半分：分配
                    have R' :
                      ∑ I ∈ fiber (α:=α) R Rep B, (2 * ((I ∩ FreeOf Rep).card : ℤ) - ((FreeOf Rep).card : ℤ))
                        =
                      2 * (∑ I ∈ fiber (α:=α) R Rep B, ((I ∩ FreeOf Rep).card : ℤ))
                      - ((FreeOf Rep).card : ℤ) * (fiber (α:=α) R Rep B).card := by
                      -- 線形性：∑(2a - c) = 2∑a - c * #fiber
                      simp [mul_sum, sum_sub_distrib]
                      exact Int.mul_comm ↑(#(fiber R Rep B)) ↑(#(FreeOf Rep))
                    simp_all only [sum_sub_distrib, sum_const, Int.nsmul_eq_mul, mem_powerset]
    _ =
          ∑ B ∈ Rep.powerset,
            ( Biasrep Rep B * (fiber (α:=α) R Rep B).card
            + Excess (α:=α) R Rep B ) := by
            -- 定義に戻すだけ
              refine sum_congr rfl ?final
              intro B hB; simp [Biasrep, Excess]
-/
