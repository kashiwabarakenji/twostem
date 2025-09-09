-- Thread C に置く（∈ 使用、simpa using 不使用）
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Twostem.Basic
import Twostem.General
import LeanCopilot

--open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

/-- 親→子の有向辺（V 上） -/
def Edge (R : Finset (Rule α)) (x y : α) : Prop :=
  ∃ t ∈ R, ((t.1 = x ∨ t.2.1 = x) ∧ t.2.2 = y)

/-- V 上に制限した辺 -/
def EdgeV (V : Finset α) (R : Finset (Rule α)) (x y : {a // a ∈ V}) : Prop :=
  Edge R x.1 y.1

/-- 到達可能性（反射推移閉包） -/
def Reach (V : Finset α) (R : Finset (Rule α))
  (x y : {a // a ∈ V}) : Prop :=
  Relation.ReflTransGen (EdgeV V R) x y

/-- 強連結（相互到達可能） -/
def SCRel (V : Finset α) (R : Finset (Rule α))
  (x y : {a // a ∈ V}) : Prop :=
  Reach V R x y ∧ Reach V R y x

/-- 強連結の同値関係（Setoid） -/
def SCSetoid (V : Finset α) (R : Finset (Rule α)) : Setoid {a // a ∈ V} :=
{ r := SCRel V R,
  iseqv :=
  by
    -- reflexive / symmetric / transitive を `Relation.ReflTransGen` の性質から組み立て
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x; exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    · intro x y h; exact ⟨h.2, h.1⟩
    · intro x y z hxy hyz
      -- ReflTransGen の合成で Reach の推移性を作り、ペアで持つ
      -- （細部は定石。必要になれば補題化）
      refine ⟨?r1, ?r2⟩
      · exact Relation.ReflTransGen.trans hxy.1 hyz.1
      · exact Relation.ReflTransGen.trans hyz.2 hxy.2 }

/-- Thread C で使う SCC の具体ビルダー -/
noncomputable def buildSCCQuot
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hneR : R ≠ ∅) :
  SCCQuot α V R := by
  classical
  -- まず `∃ x, x ∈ V` を作る（`supportedOn` と `R ≠ ∅` から）
  have hxV : ∃ x, x ∈ V := by
    -- R から 1 本取り、その親 t.1 ∈ V を使う
    have hRn : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hneR
    rcases hRn with ⟨t, ht⟩
    have h := hV (t := t) ht
    exact ⟨t.1, h.1⟩
  -- 代表を choice で取り出す
  let x0 : α := Classical.choose hxV
  have hx0 : x0 ∈ V := Classical.choose_spec hxV
  let someV : {a // a ∈ V} := ⟨x0, hx0⟩

  -- 商型 β と代表抽出
  let β := Quot (SCSetoid V R)
  have βdec : DecidableEq β := Classical.decEq _
  let rep : β → {a // a ∈ V} := fun b => Classical.choose (Quot.exists_rep b)
  have rep_spec : ∀ b, Quot.mk (SCSetoid V R) (rep b) = b := by
    intro b; exact Classical.choose_spec (Quot.exists_rep b)

  -- 射影 π とセクション σ
  let π : α → β :=
    fun x => if hx : x ∈ V then Quot.mk (SCSetoid V R) ⟨x, hx⟩
             else Quot.mk (SCSetoid V R) someV
  let σ : β → α := fun b => (rep b).1
  have σ_in_V : ∀ b, σ b ∈ V := by intro b; dsimp [σ, rep]; exact (rep b).2
  have sect : ∀ b, π (σ b) = b := by
    intro b; dsimp [π, σ]
    have hx : (rep b).1 ∈ V := (rep b).2
    -- if の真枝に入る
    simp [hx, rep_spec b]
  exact { β := β, π := π, σ := σ, σ_in_V := σ_in_V, βdec := βdec }
