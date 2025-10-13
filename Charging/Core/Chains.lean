import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic
import LeanCopilot

/-!
# Core.Chains
鎖分割と prefix の定義。
-/

namespace Charging

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- 1 本の鎖。重複なしの列（線形順序をこの列で固定）。 -/
structure Chain (V : Type u) [DecidableEq V] where
  carrier : List V
  nodup   : carrier.Nodup

namespace Chain

variable (P : Chain V)

def length : Nat := P.carrier.length

/-- 鎖の全集合（Finset）。 -/
def asFinset : Finset V := P.carrier.toFinset

/-- 先頭から `k` 個の prefix を Finset として。`k > length` でも安全。 -/
def pref (k : Nat) : Finset V :=
  (P.carrier.take k).toFinset

omit [Fintype V] in
/-- `pref k ⊆ asFinset` -/
lemma pref_subset (k : Nat) : P.pref k ⊆ P.asFinset := by
  intro x hx
  simp [Chain.pref, Chain.asFinset] at hx ⊢
  exact List.mem_of_mem_take hx

omit [Fintype V] in
/-- `pref 0 = ∅` -/
@[simp] lemma pref_zero : P.pref 0 = (∅ : Finset V) := by
  simp [Chain.pref]

omit [Fintype V] in
/-- `pref (length) = asFinset`（NoDup により） -/
lemma pref_length_eq_asFinset : P.pref P.length = P.asFinset := by
  -- `take length = carrier`
  have : P.carrier.take P.length = P.carrier := by
    simp [Chain.length]
  simp [Chain.pref, Chain.asFinset, this]

  omit [Fintype V] in
@[simp] lemma mem_pref {x : V} {k : ℕ} :
  x ∈ P.pref k ↔ x ∈ P.carrier.take k := by
  classical
  -- こちらも List.mem_toFinset でOK
  simp [Chain.pref]

 omit [Fintype V] in
lemma asFinset_card_eq_length :
  (P.asFinset).card = P.length := by
  classical
  -- NoDup リストの toFinset の card は length に等しい
  simpa [Chain.asFinset, Chain.length] using
    List.toFinset_card_of_nodup (l := P.carrier) P.nodup

omit [Fintype V] in
lemma pref_card (k : ℕ) :
  (P.pref k).card = Nat.min k P.length := by
  classical
  -- take k も NoDup、toFinset の card = length (take k) = min k (length)
  have hnd : (P.carrier.take k).Nodup := P.nodup.take
  have hk :
      ((P.carrier.take k).toFinset).card = (P.carrier.take k).length :=
    List.toFinset_card_of_nodup (l := P.carrier.take k) hnd
  simpa [Chain.pref, Chain.length, List.length_take, Nat.min_comm, Nat.min_left_comm] using hk



end Chain

/-- 鎖分割：有限個の鎖で V を互いに素に被覆。 -/
structure ChainDecomp (V : Type u) [DecidableEq V] [Fintype V] where
  ι        : Type u
  [fintype : Fintype ι]
  chains   : ι → Chain V
  pairwise_disjoint :
    (Set.Pairwise (Set.univ : Set ι) fun i j => Disjoint (chains i).asFinset (chains j).asFinset)
  cover    : (Finset.univ : Finset V) =
               (Finset.univ : Finset ι).biUnion (fun i => (chains i).asFinset)

attribute [instance] ChainDecomp.fintype

namespace ChainDecomp

variable (D : ChainDecomp V)

def P (i : D.ι) : Finset V := (D.chains i).asFinset
def ℓ (i : D.ι) : Nat := (D.chains i).length
def Pref (i : D.ι) (k : Nat) : Finset V := (D.chains i).pref k

@[simp] lemma Pref_zero (i) : D.Pref i 0 = ∅ := by simp [ChainDecomp.Pref, Chain.pref_zero]

lemma Pref_subset_P (i) (k) : D.Pref i k ⊆ D.P i := by
  simpa [ChainDecomp.P, ChainDecomp.Pref] using (D.chains i).pref_subset k

lemma Pref_top (i) : D.Pref i (D.ℓ i) = D.P i := by
  simpa [ChainDecomp.Pref, ChainDecomp.P, ChainDecomp.ℓ] using
    (D.chains i).pref_length_eq_asFinset

-- 既存の pairwise_disjoint を i≠j 専用の形で使いやすく
lemma disjoint_P_of_ne {i j : D.ι} (hij : i ≠ j) :
  Disjoint (D.P i) (D.P j) := by
  classical
  -- Set.Pairwise on univ から取り出し
  have h := D.pairwise_disjoint
  have hi : (i : D.ι) ∈ (Set.univ : Set D.ι) := by simp
  have hj : (j : D.ι) ∈ (Set.univ : Set D.ι) := by simp
  exact h hi hj hij

-- 被覆等式をそのまま名前付きで使えるように
@[simp] lemma cover_biUnion :
  (Finset.univ : Finset V) =
    (Finset.univ : Finset D.ι).biUnion (fun i => D.P i) :=
  D.cover

end ChainDecomp

end Charging
