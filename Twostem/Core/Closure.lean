import Twostem.Core.Rules
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

import Twostem.Core.Iteration
import LeanCopilot

namespace Core
open Classical

variable {α : Type _} [DecidableEq α]

/-- R-閉（1ステップで固定） -/
def IsClosed (R : Finset (Rule α)) (A : Finset α) : Prop :=
  stepPar R A ⊆ A

/-- 反復閉包：有限回で安定化（単調増加列の停留） -/
def syncCl (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  -- α の有限性を仮定しない設計でも、Finset の増加は card の停留で止まる。
  -- ここでは「十分大きい打ち切り」を入れて安定点を取る（safe 上界）。
  let bound := R.card.succ * (I.card.succ) * 2
  parIter R I bound

/-- 反復列は単調：X_k ⊆ X_{k+1} -/
lemma parIter_mono_in_k (R : Finset (Rule α)) (I : Finset α) :
  ∀ k, parIter R I k ⊆ parIter R I (k+1) := by
  intro k
  induction k with
  | zero =>
      -- I ⊆ stepPar R I
      simp [parIter, stepPar, Finset.subset_union_left]
  | succ k ih =>
      -- parIter R I (k+1) ⊆ parIter R I (k+2)
      -- つまり stepPar R (parIter R I k) ⊆ stepPar R (stepPar R (parIter R I k))
      simp only [parIter, stepPar]
      exact Finset.subset_union_left

/-- bound 以内に停留点が存在する補題 -/
lemma exists_stable_within_bound (R : Finset (Rule α)) (I : Finset α) :
  ∃ m ≤ I.card + R.card, parIter R I m = parIter R I (m+1) := by
  let B := I.card + R.card
  let f : Nat → Nat := fun k => (parIter R I k).card
  have mono : ∀ k, f k ≤ f (k+1) := fun k =>
    Finset.card_le_card (parIter_mono_in_k R I k)
  have hsubset : ∀ k, parIter R I k ⊆ I ∪ heads R := by
    intro k
    induction k with
    | zero =>
        intro x hx
        exact Finset.mem_union_left (heads R) hx
    | succ k ih =>
        intro x hx
        -- parIter (k+1) = parIter k ∪ image head (fires R (parIter k))
        have hx' :
            x ∈ parIter R I k ∪ (fires R (parIter R I k)).image (fun r => r.head) := by
          simpa [parIter, stepPar, heads] using hx
        rcases Finset.mem_union.mp hx' with hL | hR
        · exact ih hL
        · rcases Finset.mem_image.mp hR with ⟨t, ht, rfl⟩
          -- fires は filter なので R の部分集合
          have htR : t ∈ R := (Finset.mem_filter.mp ht).1
          simp
          exact Or.inr (Finset.mem_image.mpr ⟨t, htR, rfl⟩)

  -- 一様上界： |parIter k| ≤ |I ∪ heads R| ≤ I.card + R.card
  have bounded : ∀ k, f k ≤ B := by
    intro k
    have h1 : (parIter R I k).card ≤ (I ∪ heads R).card := by
      exact Finset.card_le_card (hsubset k)
    have h2 : (I ∪ heads R).card ≤ I.card + (heads R).card :=
      Finset.card_union_le _ _
    have h3 : (heads R).card ≤ R.card := by
      exact Finset.card_image_le
    exact h1.trans (h2.trans (Nat.add_le_add_left h3 _))

  -- 「単調かつ上界付き ⇒ どこかで停滞」の一般事実
  -- 反証法で：全て m ≤ B で f m < f (m+1) なら f (B+1) ≥ B+1 だが bounded と矛盾
  by_contra h
  have strict : ∀ m ≤ B, f m < f (m+1) := by
    intro m hm
    have hle := mono m
    have hne : f m ≠ f (m+1) := by
      -- h : ¬ ∃ m ≤ B, f m = f (m+1)
      refine fun heq => h ⟨m, hm, ?_⟩
      dsimp [f] at heq
      have :parIter R I m ⊆ parIter R I (m + 1):= by
        exact parIter_mono_in_k R I m
      have hrev :
    (parIter R I (m+1)).card ≤ (parIter R I m).card := by
       simp [heq]
      exact Finset.eq_of_subset_of_card_le this hrev
    exact lt_of_le_of_ne hle hne
  -- f 0 + i ≤ f i （i ≤ B+1）を示す
  have grow : ∀ i ≤ B + 1, f 0 + i ≤ f i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hi' : i ≤ B := Nat.le_of_lt_succ hi
        have step : f i + 1 ≤ f (i+1) := Nat.succ_le_of_lt (strict i hi')
        have ih' : f 0 + i + 1 ≤ f i + 1 := by
          apply Nat.add_le_add_right
          simp_all [f, B]
          omega

        -- 整形： f 0 + (i+1) ≤ f (i+1)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih'.trans step
  have big : B + 1 ≤ f (B + 1) := by
    have := grow (B + 1) (le_rfl)
    -- f 0 ≥ 0 を使って 0 + (B+1) ≤ f (B+1)
    have : 0 + (B + 1) ≤ f (B + 1) := by
      simp
      exact Nat.le_of_add_left_le this
    simpa using this
  have small : f (B + 1) ≤ B := bounded (B + 1)
  exact Nat.not_succ_le_self B (big.trans small)


/-- 停留補題：有限列の card が増え続けないので，ある段で同値になる -/
lemma parIter_stabilizes
  (R : Finset (Rule α)) (I : Finset α) :
  ∃ m, parIter R I m = parIter R I (m+1) :=
  let ⟨m, _, hm⟩ := exists_stable_within_bound R I
  ⟨m, hm⟩

/-- parIter が安定すれば不動点 -/
lemma parIter_stable_iff_closed {R : Finset (Rule α)} {I X : Finset α} {k : Nat} :
  parIter R I k = X → (parIter R I (k+1) = X ↔ IsClosed R X) := by
  intro hk
  constructor
  · intro hk1
    have hfix : stepPar R X = X := by
      simpa [parIter, hk] using hk1
    -- X ∪ heads(fires R X) = X から heads(fires R X) ⊆ X
    have hsub : heads (fires R X) ⊆ X := by
      have : X ∪ heads (fires R X) = X := by simpa [stepPar] using hfix
      exact (Finset.union_eq_left.mp this)
    -- IsClosed を示す
    intros r hr_R
    by_contra hnot
    simp_all only

  · intro hclosed
    rw [parIter, hk]
    unfold stepPar at hclosed ⊢
    have : X ∪ heads (fires R X) ⊆ X := by
      apply Finset.union_subset (Finset.Subset.refl X)
      exact Finset.union_subset_right hclosed

    apply Finset.eq_of_subset_of_card_le
    exact hclosed
    apply Finset.card_le_card
    exact Finset.subset_union_left

/-- syncCl は閉集合 -/
lemma syncCl_closed (R : Finset (Rule α)) (I : Finset α) :
  IsClosed R (syncCl R I) := by
  unfold syncCl
  let bound := R.card.succ * I.card.succ * 2
  -- bound 以内に停留点が存在
  obtain ⟨m, hm_bound, hm_stable⟩ := exists_stable_within_bound R I
  -- bound ≥ m なので、安定性を利用
  have bound_ge : bound ≥ m := by
    simp only [bound]
    have h_sum_le_bound : I.card + R.card ≤ R.card.succ * I.card.succ * 2 := by
  -- (1) I+R ≤ 2*(I+R+1)
      have h0 : I.card + R.card ≤ 2 * (I.card + R.card + 1) := by
        calc
          I.card + R.card
              ≤ (I.card + R.card) + (I.card + R.card + 1) := Nat.le_add_right _ _
          _ ≤ (I.card + R.card + 1) + (I.card + R.card + 1) := by
              exact Nat.add_le_add_right (Nat.le_succ (I.card + R.card)) _
          _ = 2 * (I.card + R.card + 1) := by
              have := two_mul (I.card + R.card + 1)  -- 2*(n) = n+n
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
      -- (2) 2*(I+R+1) ≤ 2*(I+1)*(R+1) = (R+1)*(I+1)*2
      have h1' : I.card + R.card + 1 ≤ I.card.succ * R.card.succ := by
        -- (I+1)(R+1) = I*R + (I+R+1) ≥ (I+R+1)
        have : I.card + R.card + 1 ≤ (I.card + R.card + 1) + I.card * R.card :=
          Nat.le_add_right _ _
        simp [Nat.succ_mul, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

      have h1 : 2 * (I.card + R.card + 1) ≤ R.card.succ * I.card.succ * 2 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.mul_le_mul_left 2 h1')
      -- 合成
      exact h0.trans h1

    -- 仕上げ： m ≤ I.card + R.card ≤ R.card.succ * I.card.succ * 2
    have : m ≤ R.card.succ * I.card.succ * 2 := hm_bound.trans h_sum_le_bound
    exact this

  -- m 以降は全て等しい（単調性と停留性から）
  have stable_after_m : ∀ n ≥ m, parIter R I n = parIter R I m := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n _ ih =>
      -- n ≥ m ならば parIter R I n = parIter R I m (帰納法の仮定)
      -- parIter R I (m+1) = parIter R I m (停留性)
      -- parIter R I (n+1) = stepPar R (parIter R I n) = stepPar R (parIter R I m)
      --                   = parIter R I (m+1) = parIter R I m
      rw [parIter, ih, ← parIter, hm_stable]
  -- bound での値は m での値と等しく、安定している
  have eq_at_bound : parIter R I bound = parIter R I m := stable_after_m bound bound_ge
  rw [eq_at_bound]
  exact (parIter_stable_iff_closed rfl).mp hm_stable.symm

/-- inflation：I ⊆ syncCl R I -/
lemma syncCl_infl (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ syncCl R I := by
  unfold syncCl
  -- parIter R I 0 = I なので、I ⊆ parIter R I bound
  have h0 : I = parIter R I 0 := by rfl
  rw [h0]
  -- 単調性より parIter R I 0 ⊆ parIter R I bound
  clear h0
  let bound := R.card.succ * I.card.succ * 2
  change parIter R I 0 ⊆ parIter R I bound
  induction bound  with
  | zero =>
    simp

  | succ n ih =>
    dsimp [parIter]
    intro x hx
    simp [stepPar, ih hx]


/-- parIter の各ステップで閉集合 X からはみ出ない -/
lemma parIter_subset_of_closed (R : Finset (Rule α)) {I X : Finset α}
  (hX : IsClosed R X) (hI : I ⊆ X) :
  ∀ k, parIter R I k ⊆ X := by
  intro k
  induction k with
  | zero => simp only [parIter]; exact hI
  | succ k ih =>
    rw [parIter]
    -- stepPar R (parIter R I k) ⊆ X を示す
    -- parIter R I k ⊆ X (帰納法の仮定)
    -- stepPar は単調なので stepPar R (parIter R I k) ⊆ stepPar R X
    unfold IsClosed stepPar at hX
    calc stepPar R (parIter R I k)
        = parIter R I k ∪ heads (fires R (parIter R I k)) := rfl
      _ ⊆ X ∪ heads (fires R X) := by
          apply Finset.union_subset
          · exact ih.trans Finset.subset_union_left
          · unfold heads fires
            intro x hx
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
            have hr' := Finset.mem_filter.mp hr
            obtain ⟨hr_R, hr_prem, _⟩ := hr'
            have prem_in_X : r.prem ⊆ X := Finset.Subset.trans hr_prem ih
            by_cases h : r.head ∈ X
            · exact Finset.mem_union_left _ h
            · apply Finset.mem_union_right
              apply Finset.mem_image.mpr
              use r
              constructor
              · apply Finset.mem_filter.mpr
                exact ⟨hr_R, prem_in_X, h⟩
              · rfl
      _ ⊆ X := hX

/-- 最小性：X が閉で I ⊆ X なら，syncCl R I ⊆ X -/
lemma syncCl_min (R : Finset (Rule α)) {I X : Finset α}
  (hX : IsClosed R X) (hI : I ⊆ X) :
  syncCl R I ⊆ X := by
  unfold syncCl
  exact parIter_subset_of_closed R hX hI _

/-- 閉集合は不動点 -/
lemma syncCl_id_of_closed (R : Finset (Rule α)) {A : Finset α}
  (hA : IsClosed R A) : syncCl R A = A := by
  -- 両側の包含を示す
  apply Finset.Subset.antisymm
  · -- syncCl R A ⊆ A (最小性から)
    exact syncCl_min R hA (Finset.Subset.refl A)
  · -- A ⊆ syncCl R A (inflation から)
    exact syncCl_infl R A

/-- Family：閉集合族の全列挙（Fintype α が必要） -/
noncomputable def Family [Fintype α] (R : Finset (Rule α)) : Finset (Finset α) :=
  (Finset.univ : Finset (Finset α)).filter (fun A => IsClosed R A)

lemma mem_Family_iff [Fintype α]
  {R : Finset (Rule α)} {A : Finset α} :
  A ∈ Family (α:=α) R ↔ IsClosed R A := by
  simp [Family]

end Core
