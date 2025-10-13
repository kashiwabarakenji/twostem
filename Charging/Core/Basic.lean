/-
  Core.Basic:
  - ルール（Horn 規則）
  - 閉集合 / 閉集合族 L(R)
-/
--import Mathlib
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Powerset
import LeanCopilot

namespace Charging

universe u

/- 頂点集合 -/
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Horn ルール。`prem` は有限集合（空も可）、`head` は結論頂点。 -/
structure Rule (V : Type u) [DecidableEq V] where
  prem : Finset V
  head : V

instance {V : Type u} [DecidableEq V] : DecidableEq (Rule V) :=
fun r s => match r, s with
| ⟨p1, h1⟩, ⟨p2, h2⟩ =>
  if hp : p1 = p2 then
    if hh : h1 = h2 then isTrue (by rw [hp, hh])
    else isFalse (fun contra => by injection contra with _ hh'; exact hh hh')
  else isFalse (fun contra => by injection contra with hp' _; exact hp hp')

/-- 規則系（有限集合）。 -/
structure RuleSystem (V : Type u) [DecidableEq V] [Fintype V] where
  (rules : Finset (Rule V))

instance {V : Type u} [DecidableEq V] [Fintype V] : DecidableEq (RuleSystem V) :=
  fun s t =>
    if h : s.rules = t.rules then
      isTrue (by cases s; cases t; congr)
    else
      isFalse (fun contra => by cases s; cases t; injection contra with h'; exact h h')

namespace RuleSystem

variable (R : RuleSystem V)

def edges : Finset (V × V) :=
  R.rules.biUnion (fun t =>
    t.prem.image (fun u => (u, t.head))
  )

@[simp] lemma mem_edges {uv : V × V} :
  uv ∈ R.edges ↔ ∃ t ∈ R.rules, uv.1 ∈ t.prem ∧ uv.2 = t.head := by
  classical
  rcases uv with ⟨u, v⟩
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨t, ht, hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨u', hu', huv⟩
    -- `huv : (u', t.head) = (u, v)` から `u'=u, t.head=v`
    rcases Prod.ext_iff.mp huv with ⟨hu_eq, hv_eq⟩
    subst hu_eq; subst hv_eq
    exact ⟨t, ht, hu', rfl⟩
  · rintro ⟨t, ht, hu, rfl⟩
    -- 右向きは `biUnion` に入れるだけ
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨t, ht, ?_⟩
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

/-- （将来のための）DAG であることの述語。実際の有向閉路非存在は上位で証明予定。 -/
def IsDAG : Prop := True
-- ここでは Core なので「定義の置き場」。実証は上位で扱う。

/-- `C` が閉集合（ルール閉包）であるとは：
  ∀t∈R, prem(t)⊆C ⇒ head(t)∈C。 -/
def Closed (C : Finset V) : Prop :=
  ∀ t ∈ R.rules, t.prem ⊆ C → t.head ∈ C


noncomputable instance decidableClosed (C : Finset V) : Decidable (R.Closed C) :=
  Classical.dec _

/-- 閉集合族 `L(R)` を有限集合として与える：全冪集合から filter。 -/
noncomputable def closedFamily : Finset (Finset V) :=
  (Finset.powerset (Finset.univ : Finset V)).filter (fun C => R.Closed C)

@[simp] lemma mem_closedFamily {C : Finset V} :
  C ∈ R.closedFamily ↔ R.Closed C := by
  unfold RuleSystem.closedFamily
  -- `C` は powerset(univ) に必ず入る（有限・全域）
  -- filter の述語が `Closed` そのもの
  constructor
  · intro h
    have : C ⊆ (Finset.univ : Finset V) := by
      exact Finset.subset_univ _
    -- `mem_filter` から述語部分を取り出す
    simpa [Finset.mem_filter] using h
  · intro hC
    have hCU : C ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
    have : C ∈ Finset.powerset (Finset.univ : Finset V) := Finset.mem_powerset.mpr hCU
    simpa [Finset.mem_filter] using And.intro this hC

/-- `univ ∈ L(R)`。 -/
lemma univ_mem_closedFamily : (Finset.univ : Finset V) ∈ R.closedFamily := by
  simp [mem_closedFamily]
  dsimp [Closed]
  intro t ht hsub
  simp_all only [Finset.subset_univ, Finset.mem_univ]

/-- `Closed C ↔ C ∈ L(R)`（便利な両向き形）。 -/
lemma closed_iff_mem_closedFamily {C : Finset V} :
  R.Closed C ↔ C ∈ R.closedFamily := by simp [mem_closedFamily]


/-- `Closed (univ)` は自明。 -/
@[simp] lemma closed_univ : R.Closed (Finset.univ : Finset V) := by
  classical
  intro t ht hsub
  simp

/-- 閉集合の交わりは閉。 -/
lemma Closed.inter {C D : Finset V}
  (hC : R.Closed C) (hD : R.Closed D) : R.Closed (C ∩ D) := by
  classical
  intro t ht hsub
  -- `prem ⊆ C ∩ D` なら `prem ⊆ C` かつ `prem ⊆ D`
  have hC' : t.prem ⊆ C := by
    intro x hx;
    exact Finset.mem_of_mem_filter x (hsub hx)
  have hD' : t.prem ⊆ D := by
    intro x hx;
    exact Finset.mem_of_mem_inter_right (hsub hx)
  have hxC := hC t ht hC'
  have hxD := hD t ht hD'
  exact Finset.mem_inter.mpr ⟨hxC, hxD⟩

@[simp] lemma closed_empty :
  R.Closed (∅ : Finset V) ↔ (∀ t ∈ R.rules, t.prem ≠ ∅) := by
  classical
  constructor
  · intro h t ht hprem
    -- `prem ⊆ ∅` なら `prem = ∅`。ここで `Closed` 条件から `head ∈ ∅` が必要になるが矛盾。
    have hsub : t.prem ⊆ (∅ : Finset V) := by
      intro x hx; exfalso;
      simp_all only [Finset.notMem_empty]

    have : t.head ∈ (∅ : Finset V) := h t ht hsub
    exact (List.mem_nil_iff t.head).mp (h t ht hsub)
  · intro h t ht hsub
    -- `prem ⊆ ∅` なら `prem = ∅` に反するので到達不能、従って任意の結論が言える
    have : t.prem = (∅ : Finset V) := Finset.subset_empty.mp hsub
    have hne := h t ht
    exact False.elim (hne this)

end RuleSystem


end Charging
