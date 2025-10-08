import Twostem.Core.Rules
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card


namespace Core

variable {α : Type _} [DecidableEq α]

def heads (S : Finset (Rule α)) : Finset α :=
  S.image (fun r => r.head)

def stepPar (R : Finset (Rule α)) (I : Finset α) : Finset α :=
  I ∪ heads (fires R I)

def parIter (R : Finset (Rule α)) : Finset α → Nat → Finset α
  | I, 0          => I
  | I, Nat.succ k => stepPar R (parIter R I k)

end Core
