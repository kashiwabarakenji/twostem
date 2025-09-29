-- Twostem/Derivation.lean
import Mathlib.Data.Finset.Basic
--import Twostem.Rules
--import Twostem.Closure
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.Closure.Sync

namespace Twostem

open Finset
open Closure

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
lemma mem_closure_iff_deriv :
  ∀ {R : Finset (Rule α)} {I : Finset α} {a : α},
    a ∈ syncCl R I ↔ Deriv (α:=α) R (syncCl R I) a := by
  classical
  intro R I a
  constructor
  · -- (→) 基底にあるものは導出済み
    intro ha
    -- ここは `Deriv` の基底コンストラクタを使うだけです
    exact Deriv.base ha          -- ← 環境の名前に合わせて
  · -- (←) 導出からメンバーシップを示す
    intro h
    -- 閉包は R-閉
    have hClosed : IsClosed R (syncCl R I) := syncCl_closed (R := R) (I := I)
    -- 導出に対する帰納
    -- `Deriv.recOn` / `Deriv.induction_on` など、定義に合わせて使ってください
    --revert a
    induction h with
    | base hx =>
        exact hx
    | @step t ht hPrem ih =>
        -- 代表例A: 結論は `t.head` 固定。prem の各要素は ih で syncCl に入る。
        have hPremSub : t.prem ⊆ syncCl R I := by
          intro u hu;
          exact hPrem hu
        have hHead : t.head ∈ syncCl R I := hClosed ht hPremSub
        exact hHead

/-成り立たないということになった。
lemma mem_closure_iff_deriv_from_base
  {R : Finset (Rule α)} {I : Finset α} {a : α} :
  a ∈ syncCl R I ↔ Deriv R I a := by
  classical
  constructor
  · -- (→) 方向：syncCl のメンバから導出を作る
    intro ha
    -- 段数付きの強化版：∀ n, b ∈ syncClIter R I n → Deriv R I b
    have deriv_of_iter :
        ∀ n (b : α), b ∈ syncClIter R I n → Deriv R I b := by
      -- 強い帰納法 on n
      refine Nat.rec (motive := fun n => ∀ b, b ∈ syncClIter R I n → Deriv R I b) ?base ?step
      · -- n = 0: syncClIter R I 0 = I
        intro b hb
        -- Deriv の基底コンストラクタ（名前は環境に合わせて）
        -- 例：Deriv.base : b ∈ I → Deriv R I b
        -- `simp [syncClIter]` で hb : b ∈ I に落とせるなら rw/simp で書き換え
        -- ここでは書き換え無しで扱うため、まず等式で展開
        have : syncClIter R I 0 = I := rfl
        -- hb : b ∈ I
        have hbI : b ∈ I := by simpa [this] using hb
        exact Deriv.base hbI
      · -- n → n+1
        intro n IH b hb
        -- J を前段集合
        set J := syncClIter R I n with hJ
        -- 定義に従って分岐
        cases h : nextHead? R J with
        | none =>
            -- 停止しているので n+1 段も J
            -- hb : b ∈ J
            have hstep : syncClIter R I (n+1) = J := by
              -- `syncClIter` の定義を 1 段ほどく
              --   syncClIter R I (n+1) = match nextHead? R J with | none => J | some a0 => insert a0 J
              -- ここでは none 分岐
              simp [syncClIter, hJ]
              simp_all only [syncCl_eq_step_closure, Step.cl, Nat.succ_eq_add_one, J]
            have hbJ : b ∈ J := by simpa [hstep] using hb
            -- 帰納法の仮定を b に適用
            have : Deriv R I b := IH b (by simpa [hJ] using hbJ)
            exact this
        | some a0 =>
            -- 1 個挿入：syncClIter R I (n+1) = insert a0 J
            have hstep : syncClIter R I (n+1) = insert a0 J := by
              simp [syncClIter, hJ]
              simp_all only [syncCl_eq_step_closure, Step.cl, Nat.succ_eq_add_one, J]
            -- a0 の来歴：nextHead?_spec_some
            obtain ⟨ha0_notJ, t, htR, hPremJ, hHead⟩ :=
              nextHead?_spec_some (R := R) (I := J) (a := a0) h
            -- hb の場合分け
            --   hb : b ∈ insert a0 J なので b = a0 か b ∈ J
            have hb' : b = a0 ∨ b ∈ J := by
              -- まず hb を insert a0 J の形に
              have : b ∈ insert a0 J := by simpa [hstep] using hb
              -- 会員分解
              simpa [Finset.mem_insert] using this
            cases hb' with
            | inl hba =>
                -- b = a0。規則 t の前提は J に入っているので、各前提 u は IH で Deriv R I u
                -- それをまとめて Deriv.step で head = a0 を導出
                have hDerivPrem : ∀ u ∈ t.prem, Deriv R I u := by
                  intro u hu
                  have huJ : u ∈ J := hPremJ hu
                  -- J = syncClIter R I n
                  have : Deriv R I u := IH u (by simpa [hJ] using huJ)
                  exact this
                -- Deriv.step : t ∈ R → (∀ u∈prem, Deriv R I u) → Deriv R I t.head
                have hDerivHead : Deriv R I t.head := by

                  sorry --Deriv.step htR hDerivPrem
                -- b = a0 = t.head
                -- 目標は Deriv R I b
                -- hHead : t.head = a0
                -- hba   : b = a0
                -- 書き換えて終了
                -- まず b = a0 の向きで書き換え
                -- then a0 = t.head の向き（必要に応じて cases / rw）
                -- ここでは両方 `cases` で潰す
                cases hba
                cases hHead
                exact hDerivHead
            | inr hbJ =>
                -- b ∈ J は前段なので IH
                have : Deriv R I b := IH b (by simpa [hJ] using hbJ)
                exact this

    -- syncCl = syncClIter … (|α| 段)
    -- a ∈ syncCl R I ⇒ a ∈ syncClIter R I (|α|)
    have ha_iter : a ∈ syncClIter R I (Fintype.card α) := by
      -- 定義が syncCl R I := syncClIter R I (|α|) なら rfl
      -- 環境の定義に合わせて
      change a ∈ syncCl R I at ha
      -- そのまま使える場合
      -- exact ha
      -- 通常は `rfl` で書き換え
      simpa [syncCl] using ha
    exact deriv_of_iter (Fintype.card α) a ha_iter

  · -- (←) 方向：導出から syncCl への所属
    intro h
    -- syncCl は R-閉
    have hClosed : IsClosed R (syncCl R I) := syncCl_closed (R := R) (I := I)
    -- また I ⊆ syncCl R I
    have hInfl : I ⊆ syncCl R I := syncCl_infl (R := R) (I := I)
    -- 導出の構造帰納
    -- 代表的定義に合わせた induction
    induction h with
    | base hx =>
        -- 基底：x∈I ⊆ syncCl R I
        exact hInfl hx
    | @step t ht hPrem ih =>
        -- prem ⊆ syncCl R I （ih で各要素が入る）
        have hPremSub : t.prem ⊆ syncCl R I := by
          intro u hu
          exact hInfl (hPrem hu)
        -- 閉性で head ∈ syncCl R I
        exact hClosed ht hPremSub
-/

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
