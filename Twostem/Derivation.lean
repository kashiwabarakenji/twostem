-- Twostem/Derivation.lean
import Mathlib.Data.Finset.Basic
import Twostem.Rules
import Twostem.Closure

namespace Twostem

open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/-- RによるJからの導出：aがJからRで導ける -/
inductive Deriv (R : Finset (Rule α)) (J : Finset α) : α → Prop
| base {a} : a ∈ J → Deriv R J a
| step {t : Rule α} :
    t ∈ R →
    (t.prem ⊆ J) →
    (∀ a ∈ t.prem, Deriv R J a) →
    Deriv R J t.head

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
/-- ルールのheadで終わる導出は，その最後の一手のルールがheadで決まる。 -/
lemma last_step_head
  {R : Finset (Rule α)} {J : Finset α} {x : α}
  (h : Deriv (α:=α) R J x) :
  x ∈ J ∨ ∃ t ∈ R, t.head = x := by
  induction h with
  | base ha =>
      exact Or.inl ha
  | step tt ht hprem hrec=>
      rename_i t
      apply Or.inr
      use t

/-- 閉包に入るなら導出がある（Closure 側の仕様として用意しておく） -/
axiom mem_closure_iff_deriv :
  ∀ {R : Finset (Rule α)} {I : Finset α} {a : α},
    a ∈ syncCl R I ↔ Deriv (α:=α) R (syncCl R I) a

/-- 閉包は単調：I⊆Jなら cl[R] I ⊆ cl[R] J -/
axiom closure_mono :
  ∀ {R : Finset (Rule α)} {I J : Finset α}, I ⊆ J → syncCl R I ⊆ syncCl R J

/-- 閉包は包含：I ⊆ cl[R] I -/
axiom subset_closure :
  ∀ {R : Finset (Rule α)} {I : Finset α}, I ⊆ syncCl R I

/-- 閉包は冪等：cl[R] (cl[R] I) = cl[R] I -/
axiom closure_idem :
  ∀ {R : Finset (Rule α)} {I : Finset α}, syncCl R (syncCl R I) = syncCl R I

end Twostem
