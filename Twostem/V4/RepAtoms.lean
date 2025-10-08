import Twostem.Core.Rules
import LeanCopilot

namespace V4
open Core
variable {α : Type _} [DecidableEq α]

def RepAtoms (R : Finset (Rule α)) : Finset α :=
  R.image (fun r => r.head)

def base (R : Finset (Rule α)) (A : Finset α) : Finset α :=
  A ∩ RepAtoms R

def free (R : Finset (Rule α)) (A : Finset α) : Finset α :=
  A \ base R A

@[simp] lemma mem_RepAtoms {R : Finset (Rule α)} {x : α} :
  x ∈ RepAtoms R ↔ ∃ r ∈ R, r.head = x := by
  simp [RepAtoms]

@[simp] lemma base_union_free (R : Finset (Rule α)) (A : Finset α) :
  base R A ∪ free R A = A := by
  -- (A ∩ S) ∪ (A \ (A ∩ S)) = A
  simp [base, free]
  -- ↑ ここは必要に応じて rewrite を追加
  dsimp [RepAtoms]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with h₁ | h₂
    · exact (Finset.mem_inter.mp h₁).1
    · exact (Finset.mem_sdiff.mp h₂).1
  · intro hxA
    by_cases hxH : x ∈ R.image (·.head)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxA, hxH⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxA, hxH⟩))


@[simp] lemma base_inter_free (R : Finset (Rule α)) (A : Finset α) :
  base R A ∩ free R A = ∅ := by
  -- 交わりは空
  simp [base, free]
  -- 場合によっては、構成的に `Finset.ext` で詰めるのも可


end V4
