import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card

set_option autoImplicit true

namespace Core

variable {α : Type _} [DecidableEq α]

structure Rule (α : Type _) where
  prem : Finset α
  head : α
deriving DecidableEq

structure RuleOrder (α : Type _) where
  ruleIndex : Rule α → Nat

def UC (R : Finset (Rule α)) : Prop :=
  ∀ a : α, (R.filter (fun t => t.head = a)).card ≤ 1

def UniqueChild {α : Type _} (R : Finset (Rule α)) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ R → t₂ ∈ R → t₁.head = t₂.head → t₁ = t₂

lemma UniqueChild_iff_UC
  [DecidableEq α] [DecidableEq (Rule α)]
  (R : Finset (Rule α)) :
  UniqueChild R ↔ UC R := by
  classical
  constructor
  · -- UniqueChild → UC
    intro h a
    refine Finset.card_le_one.mpr ?_

    intro t₁ ht₁ t₂ ht₂
    rcases Finset.mem_filter.mp ht₁ with ⟨h₁R, h₁head⟩
    rcases Finset.mem_filter.mp ht₂ with ⟨h₂R, h₂head⟩
    exact h h₁R h₂R (h₁head.trans h₂head.symm)
  · -- UC → UniqueChild
    intro h
    dsimp [UniqueChild]
    intro t₁ t₂ ht₁ ht₂ hhead
    have h_le : (R.filter (fun t => t.head = t₁.head)).card ≤ 1 := h t₁.head
    have ht₁s : t₁ ∈ R.filter (fun t => t.head = t₁.head) :=
      Finset.mem_filter.mpr ⟨ht₁, rfl⟩
    have ht₂s : t₂ ∈ R.filter (fun t => t.head = t₁.head) := by
      exact Finset.mem_filter.mpr ⟨ht₂, hhead.symm⟩

    apply  (Finset.card_le_one.mp h_le)
    exact ht₁s
    exact ht₂s

def fires (R : Finset (Rule α)) (I : Finset α) : Finset (Rule α) :=
  R.filter (fun r => r.prem ⊆ I ∧ r.head ∉ I)

def NoTwoFreshHeads (R : Finset (Rule α)) : Prop :=
  ∀ I : Finset α, (fires R I).card ≤ 1

end Core
