import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.SymmDiff
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.NDS
import Twostem.Fiber --FreeOfなどで必要。
--import Twostem.Synchronous
--import Twostem.Derivation --mem_closure_iff_derivなど。

namespace Twostem

open scoped BigOperators
open scoped symmDiff
open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)]

--/***********************
-- * 0. TwoStem / UC / NoEmpty
-- ***********************/
--こちらは、Rに対する条件。TwoStemという個別のルールに対する条件もある。
def TwoStemR (R : Finset (Rule α)) : Prop :=
  ∀ t ∈ R, (t.prem.card ≤ 2)

--Rulesのところで同値な条件であるUCを定めているが微妙に違う。
def UniqueChild (α : Type _) (R : Finset (Rule α)) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ R → t₂ ∈ R → t₁.head = t₂.head → t₁ = t₂

omit [Fintype α] [LinearOrder α] in
--UCとUniqueChildの同値性の証明
lemma UniqueChild_iff_UC (R : Finset (Rule α)) :
  UniqueChild (α:=α) R ↔ UC (α:=α) R := by
  dsimp [UniqueChild, UC]
  constructor
  · intro h a
    --change (R.filter (fun t => t.head = a)).card ≤ 1
  -- 「任意の2要素が等しい」ことを示せば card ≤ 1
    apply Finset.card_le_one.mpr
    intro t₁ t₂ ht₁ ht₂
    -- filter のメンバを分解
    simp_all only [mem_filter]
    obtain ⟨left, right⟩ := t₂
    obtain ⟨left_1, right_1⟩ := ht₂
    subst right
    apply @h
    · simp_all only
    · simp_all only
    · simp_all only
  · intro h t₁ t₂ ht₁ ht₂ hhead
  -- 集合 s := { t ∈ R | t.head = t₁.head }
    let s : Finset (Rule α) := R.filter (fun t => t.head = t₁.head)

    -- t₁ ∈ s
    have ht₁s : t₁ ∈ s := by
      -- mem_filter ⇔ (mem R ∧ head=…)
      have : t₁ ∈ R ∧ t₁.head = t₁.head := And.intro ht₁ rfl
      exact (Finset.mem_filter.mpr this)

    -- t₂ ∈ s （t₂.head = t₁.head を使用）
    have ht₂s : t₂ ∈ s := by
      have : t₂ ∈ R ∧ t₂.head = t₁.head := And.intro ht₂ hhead.symm
      exact (Finset.mem_filter.mpr this)

    -- もし t₁ ≠ t₂ なら {t₁,t₂} ⊆ s なので 2 ≤ s.card になって矛盾
    by_contra hneq
    -- {t₁,t₂} を `insert t₂ {t₁}` で表す
    have hsubset : insert t₂ ({t₁} : Finset (Rule α)) ⊆ s := by
      intro x hx
      -- x = t₂ ∨ x = t₁
      have hx' := (Finset.mem_insert.mp hx)
      cases hx' with
      | inl hx2 =>
          -- x = t₂
          cases hx2
          exact ht₂s
      | inr hx1 =>
          -- x ∈ {t₁} → x = t₁
          have : x = t₁ := (Finset.mem_singleton.mp hx1)
          cases this
          exact ht₁s

    have hcard_pair : (insert t₂ ({t₁} : Finset (Rule α))).card = 2 := by
      -- card_insert (if a∉s) : (insert a s).card = s.card + 1
      -- ここで s = {t₁} だから 1 + 1 = 2
      have : ({t₁} : Finset (Rule α)).card = 1 := by
        -- 単集合の濃度
        -- again, simp で十分
        simp
      -- まとめて
      -- simp [Finset.card_insert, hnot] は
      --   card (insert t₂ {t₁}) = card {t₁} + 1 = 1 + 1 = 2
      -- を出してくれる
      --simp_all only [mem_filter, and_self, ne_eq, card_singleton, s]
      have h_card_insert : (insert t₂ ({t₁} : Finset (Rule α))).card = ({t₁}:Finset (Rule α)).card + 1 := by
        simp
        exact card_pair fun a => hneq (id (Eq.symm a))
      exact h_card_insert

    -- 部分集合なら濃度は増えない： card {t₁,t₂} ≤ card s
    have two_le_card_s : 2 ≤ s.card := by

      have := Finset.card_le_card (s := insert t₂ ({t₁} : Finset (Rule α)))
         (t := s) hsubset
      simp_all only [mem_filter, and_self, ne_eq, s]

    -- {t₁,t₂} の濃度は 2（t₂ ∉ {t₁} を使って card_insert）
    have hnot : t₂ ∉ ({t₁} : Finset (Rule α)) := by
      -- t₂ ∈ {t₁} ↔ t₂ = t₁
      have : t₂ = t₁ := by
        -- 反証用に仮定すると hneq と矛盾
        have h_s_card_le : s.card ≤ 1 := by
          simp_all only [mem_filter, and_self, ne_eq, s]
        have h_card_pair : #{t₁, t₂} = 2 := by
          simp [hneq]
        have h_s_card_ge : 2 ≤ s.card := by
          simp_all only [mem_filter, and_self, ne_eq, mem_singleton, not_false_eq_true, card_insert_of_notMem, card_singleton,
             Nat.reduceAdd, s]
        linarith

      all_goals
        -- 目的は t₂ ∉ {t₁}
        -- 直接書く：
        -- simp [Finset.mem_singleton, hneq] で済みますが、simpa を避けるなら unfold 的に
        exact by
          -- `simp` で十分（`simpa` は使っていない）
          simp [Finset.mem_singleton]
          exact fun a => hneq (id (Eq.symm this))

    -- 一方、仮定 h から s.card ≤ 1
    have one_ge_card_s : s.card ≤ 1 := by
      -- h を a := t₁.head に適用し，{t∈R | t.head = a} を filter に変換
      have := h (t₁.head)
      -- {t ∈ R | t.head = t₁.head} = R.filter …
      -- `change` で左辺を揃える
      change (R.filter (fun t => t.head = t₁.head)).card ≤ 1 at this
      -- s の定義に一致
      -- s = R.filter …
      -- 置換して終了
      -- `rfl` で一致
      -- （s の定義が `let s := …` なので `rfl`）
      exact (by
        have : s = R.filter (fun t => t.head = t₁.head) := rfl
        simp_all only [mem_filter, and_self, ne_eq, mem_singleton, not_false_eq_true, card_insert_of_notMem, card_singleton,
    Nat.reduceAdd, s])

    -- 2 ≤ s.card ≤ 1 の矛盾
    linarith
    --exact (Nat.le_trans two_le_card_s one_ge_card_s).false

--非空前提。Ruleを一般のステムとして定義しているので、自動的には満たされない。
def NoEmptyPremise (R : Finset (Rule α)) : Prop :=
  ∀ t ∈ R, t.prem ≠ ∅

--/***********************
-- * 1. ルール順序(first violationあたり)
-- ***********************/
structure RuleOrder (α) where
  carrier : List (Rule α)
  nodup   : carrier.Nodup

namespace RuleOrder

variable {R : Finset (Rule α)}

def ruleIndex (ρ : RuleOrder α) (t : Rule α) : Nat :=
  ρ.carrier.findIdx (fun s => decide (s = t))

noncomputable def firstRule (ρ : RuleOrder α) (S : Finset (Rule α)) : Option (Rule α) :=
  S.val.toList.argmin (fun t => ρ.ruleIndex t)

end RuleOrder

--/***********************
-- * 2. 「最初の違反」
-- ***********************/
def violates (R : Finset (Rule α)) (t : Rule α) (I : Finset α) : Prop :=
  t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I

def violatesFirst (ρ : RuleOrder α) (R : Finset (Rule α))
    (t : Rule α) (I : Finset α) : Prop :=
  violates R t I ∧
  (∀ s, violates R s I → ρ.ruleIndex t ≤ ρ.ruleIndex s)

omit [DecidableEq α][Fintype α] [LinearOrder α] in
lemma violates_not_closed {ρ} {R} {t : Rule α} {I}
  (h : violatesFirst ρ R t I) : ¬ IsClosed R I := by
  intro hcl
  rcases h with ⟨⟨hR, hPrem, hHead⟩, _⟩
  have : t.head ∈ I := hcl (t:=t) hR hPrem
  exact hHead this

omit [Fintype α] [LinearOrder α] in
lemma exists_first_violation
  (ρ : RuleOrder α) (R : Finset (Rule α)) (I : Finset α) :
  (¬ IsClosed R I) → ∃ t, violatesFirst ρ R t I := by
  classical
  intro hnot
  -- 適用可能で head ∉ I の規則の集合
  let V : Finset (Rule α) :=
    R.filter (fun t => (t.prem ⊆ I) ∧ t.head ∉ I)

  -- V は空でないことを示す（空だと IsClosed になって矛盾）
  have V_nonempty : V.Nonempty := by
    by_contra h'
    -- V = ∅ だと各 t∈R, prem⊆I に対し head∈I が従う
    have hClosed : IsClosed R I := by
      intro t ht hsub
      -- もし head ∉ I なら t ∈ V で V.Nonempty を作れて矛盾
      by_contra hhead
      have htV : t ∈ V := by
        -- t ∈ R ∧ (prem⊆I ∧ head∉I) なので filter に入る
        have : t ∈ R ∧ ((t.prem ⊆ I) ∧ t.head ∉ I) := ⟨ht, ⟨hsub, hhead⟩⟩
        simpa [V, mem_filter] using this
      exact h' ⟨t, htV⟩
    exact hnot hClosed

  -- V の中で ρ.ruleIndex を最小化する元 t を取る
  obtain ⟨t, htV, hmin⟩ :
      ∃ t ∈ V, ∀ t' ∈ V, ρ.ruleIndex t ≤ ρ.ruleIndex t' := by
    classical
    -- `exists_min_image` の型は `∃ a ∈ s, ∀ b ∈ s, f a ≤ f b`
    -- ここでは s = V, f = ρ.ruleIndex
    simpa using
      Finset.exists_min_image (s := V) (f := fun t => ρ.ruleIndex t) V_nonempty

  refine ⟨t, ?hf⟩
  constructor
  · -- t は定義上「違反」している
    have : t ∈ R ∧ t.prem ⊆ I ∧ t.head ∉ I := by
      have : t ∈ V := htV
      simpa [V, mem_filter] using this
    simpa [violates] using this
  · -- ρ の最小性
    intro s hs
    have hsV : s ∈ V := by
      rcases hs with ⟨hsR, hsp, hsh⟩
      simp_all only [mem_filter, and_imp, not_false_eq_true, and_self, V]
    exact hmin s hsV

--/***********************
-- * 3. 正規極小証人（辞書式一意化）
--- ***********************/
variable (Rep : Finset α)
--def FreeOf (Rep : Finset α) : Finset α := (univ : Finset α) \ Rep

def isWitness (ρ : RuleOrder α) (R : Finset (Rule α))
    (B S : Finset α) (t : Rule α) : Prop :=
  (S ⊆ FreeOf (α:=α) B) ∧ violatesFirst ρ R t (B ∪ S)

/-- 候補：Free からとった部分集合で、t が first violation になるもの -/
private noncomputable def witnessCandidates
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Finset (Finset α) :=
by
  classical
  -- powerset 上で「t が最小違反 head になるような拡張 S」をフィルタ
  exact (FreeOf (α:=α) B).powerset.filter
    (fun S =>
      violates R t (B ∪ S)
      ∧ ∀ s, violates R s (B ∪ S) → ρ.ruleIndex t ≤ ρ.ruleIndex s)

/-- inclusion 極小元の集合 -/
private def inclusionMinimals (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun S => ∀ S' ∈ F, S' ⊆ S → S = S')

/-- Finset をソートした `List α` に変換（辞書式比較用） -/
private def asLexList (S : Finset α) : List α :=
  S.sort (· ≤ ·)

/-- 「辞書式最小」の 1 要素を返す（Nonempty を仮定） -/
private noncomputable def chooseLexMin (F : Finset (Finset α)) : Option (Finset α) :=
  -- `F.val : Multiset (Finset α)` → `toList : List (Finset α)`
  -- `argmin? (asLexList)` でキー最小の要素を `Option` で取得
  (F.val.toList).argmin asLexList

/-
/-- 正規極小証人を返す：候補が空なら none -/
noncomputable def lexMinWitness
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Option (Finset α) := by
  classical
  let cand := witnessCandidates (α:=α) ρ R B t
  let mins := inclusionMinimals cand    -- : Finset (Finset α)
  exact chooseLexMin mins               -- : Option (Finset α)
-/

/-- 返した witness が本当に witness -/
noncomputable def lexMinWitness
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α) : Option (Finset α) := by
  classical
  let cand := witnessCandidates (α:=α) ρ R B t
  let mins := inclusionMinimals cand
  exact if h : mins.Nonempty then some (Classical.choose h) else none

lemma lexMinWitness_isWitness
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α)
  (h : ∃ S, lexMinWitness (α:=α) ρ R B t = some S) :
  ∃ S, isWitness (α:=α) ρ R B S t := by
  classical
  -- 展開
  rcases h with ⟨S, hS⟩
  dsimp [lexMinWitness] at hS
  set cand := witnessCandidates (α:=α) ρ R B t with hcand
  set mins := inclusionMinimals cand with hmins
  by_cases hne : mins.Nonempty
  · -- then 分岐：`some (Classical.choose hne)` と一致
    have hS' : some (Classical.choose hne) = some S := by
    -- 依存 if を評価する等式
      have hreduce :
          (if h : mins.Nonempty then some (Classical.choose h) else none)
            = some (Classical.choose hne) :=
        dif_pos hne
      -- hS は dsimp で展開済み：左辺が今の if 式
      exact hreduce.symm.trans hS
    -- 中身を取り出し
    have S_eq : Classical.choose hne = S := Option.some.inj hS'
    subst S_eq
    -- `S ∈ mins`
    have S_in_mins : Classical.choose hne ∈ mins :=
      Classical.choose_spec hne
    /- inclusionMinimals の定義に依存：
       ここでは `mins = cand.filter P` の形だとし，mem_filter で分解する -/
    have S_in_cand_andP :
        Classical.choose hne ∈ cand ∧
        True := by
      -- P の具体は使わないので `True` に吸収。定義があればそこに合わせて置き換えてください。
      -- `S_in_mins : _ ∈ inclusionMinimals cand` だが、いまは `mins` に畳んでいる
      -- `mins = cand.filter _` を仮定して分解
      -- 具体定義を持っているなら：`have := Finset.mem_filter.mp S_in_mins`
      -- ここでは「cand に属する」ことだけ使う：
      -- とりあえず cand に属すると仮定するヘルパ（定義に合わせて書き換えてください）
      -- （もし `inclusionMinimals` が `cand.filter P` なら次の 1 行で OK）
      simp
      have : mins ⊆ cand := by
        simp [inclusionMinimals, hmins]
      exact this S_in_mins

    have S_in_cand : Classical.choose hne ∈ cand := S_in_cand_andP.left

    -- ここから witnessCandidates の membership をほどいて3条件を抽出
    -- witnessCandidates = powerset (FreeOf B) で filter したもの
    have S_mem_filtered :
        Classical.choose hne ∈
          (Finset.powerset (FreeOf (α:=α) B)).filter
            (fun S =>
              violates R t (B ∪ S) ∧
              ∀ s, violates R s (B ∪ S) → ρ.ruleIndex t ≤ ρ.ruleIndex s) := by
      -- `hcand : cand = witnessCandidates …` を使って書き換え
      -- まず `S_in_cand : _ ∈ cand` を `witnessCandidates` へ
      -- `rw` で書き換える
      have : Classical.choose hne ∈ cand := S_in_cand
      -- `hcand` は `cand = witnessCandidates …`
      -- 右辺へ書き換え
      --   `by cases hcand; exact this` とすれば `simpa` 不要
      cases hcand
      exact this

    -- `mem_filter` で分解
    have hPair := Finset.mem_filter.mp S_mem_filtered
    -- powerset 側
    have hPow : Classical.choose hne ⊆ FreeOf (α:=α) B :=
      (Finset.mem_powerset.mp hPair.left)
    -- 述語側
    have hPred : violates R t (B ∪ Classical.choose hne)
              ∧ ∀ s, violates R s (B ∪ Classical.choose hne) → ρ.ruleIndex t ≤ ρ.ruleIndex s :=
      hPair.right

    -- 3条件をまとめて witness を構成
    refine ⟨Classical.choose hne, ?_⟩
    exact And.intro hPow (And.intro hPred.left hPred.right)

  · -- else 分岐は `none` を返すので `some S` は矛盾
    have : mins = ∅ := by
      exact not_nonempty_iff_eq_empty.mp hne
    exfalso
    rw [this] at hS
    dsimp [chooseLexMin] at hS
    simp at hS

omit [DecidableEq α] [LinearOrder α] in
/-- 返した witness が inclusion 極小 -/
lemma lexMinWitness_isInclusionMinimal
  [DecidableEq α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (B : Finset α) (t : Rule α)
  (h : ∃ S, lexMinWitness (α:=α) ρ R B t = some S) :
  ∃ S, (S ∈ witnessCandidates ρ R B t) ∧
       (∀ S' ∈ witnessCandidates ρ R B t, S' ⊆ S → S' = S) := by
  classical
  rcases h with ⟨S, hS⟩
  dsimp [lexMinWitness] at hS
  -- 記号を固定
  set cand := witnessCandidates (α:=α) ρ R B t with hcand
  set mins := inclusionMinimals cand with hmins
  by_cases hne : mins.Nonempty
  · -- then: if を評価し，some の中身を同定
    have hreduce :
        (if h : mins.Nonempty then some (Classical.choose h) else none)
        = some (Classical.choose hne) := by
      exact dif_pos hne
    have hS' : some (Classical.choose hne) = some S :=
      hreduce.symm.trans hS
    have S_eq : Classical.choose hne = S := Option.some.inj hS'
    -- 以降 S = choose hne に統一
    subst S_eq

    -- choose hne は mins に属する
    have S_in_mins : Classical.choose hne ∈ mins :=
      Classical.choose_spec hne

    -- mins = inclusionMinimals cand を展開し，filter のメンバで分解
    -- （simpa は使わずに `cases hmins` で書き換え → `dsimp`/`unfold`）
    cases hmins
    -- ここで mins = inclusionMinimals cand に固定
    -- inclusionMinimals の定義を展開
    --dsimp [inclusionMinimals] at S_in_mins
    -- filter のメンバを分解
    have hpair := Finset.mem_filter.mp S_in_mins
    -- hpair : (choose hne ∈ cand) ∧ (∀ S' ∈ cand, S' ⊆ choose hne → S' = choose hne)
    refine ⟨Classical.choose hne, ?_, ?_⟩
    · -- cand に属する
      -- hcand : cand = witnessCandidates …
      cases hcand
      exact hpair.left
    · -- inclusion 極小性
      cases hcand
      intro S' hS' hsub
      have : mins ⊆ cand := by
        dsimp [mins]
        dsimp [inclusionMinimals]
        exact filter_subset (fun S => ∀ S' ∈ cand, S' ⊆ S → S = S') cand
      simp_all [mins, cand]
      obtain ⟨left, right⟩ := hpair
      symm
      exact right S' hS' hsub

  · -- else: if は none を返すので仮定と矛盾
    have hreduce :
        (if h : mins.Nonempty then some (Classical.choose h) else none) = none :=
      dif_neg hne
    have : none = some S := hreduce.symm.trans hS
    cases this

--/***********************
-- * 4. 弱化リフティング
-- ***********************/
noncomputable def addedFamily
  [DecidableEq α] [DecidableEq (Rule α)]
  (R : Finset (Rule α)) (t : Rule α) :
  Finset (Finset α) := by
  classical
  -- Family (R.erase t) で必要になる決定性インスタンスをローカルに用意
  letI : DecidablePred (IsClosed (R.erase t)) :=
    fun I => Classical.dec (IsClosed (R.erase t) I)
  -- R \ {t} で閉じていて、かつ t が「適用可能（prem⊆I かつ head∉I）」な I を集める
  exact (Family (α := α) (R.erase t)).filter
    (fun I => t.prem ⊆ I ∧ t.head ∉ I)

/-
noncomputable def addedFamily (S : Finset α) (R : Finset (Rule α)) [DecidablePred (IsClosed R)] (t : Rule α) :
    Finset (Finset α) :=
  let _ : DecidablePred (IsClosed (R.erase t)) :=
    fun I => Classical.dec (IsClosed (R.erase t) I)
  (Family (α:=α) (R.erase t)).filter
  (fun I => t.prem ⊆ I ∧ t.head ∉ I)
-/



-- Twostem/Bridge.lean の末尾付近に追記


--variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/- UC: 同一ヘッドを持つルールは高々 1 本 -/
--def UniqueChild (R : Finset (Rule α)) : Prop :=
--  ∀ {t₁ t₂}, t₁ ∈ R → t₂ ∈ R → t₁.head = t₂.head → t₁ = t₂

--補題5.1
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- UC から：t を外した閉包から t.head は出てこない。 -/
lemma head_not_in_closure_of_erase
  [Fintype α] [DecidableEq α] [DecidableEq (Rule α)]
  {R : Finset (Rule α)} {t : Rule α} {I : Finset α}
  (hUC : UC R) (ht : t ∈ R) (hnotI : t.head ∉ I) :
  t.head ∉ syncCl (R.erase t) I := by
  classical
  -- “parIter で得られる要素は I か、R のどれかの head”
  have origin :
    ∀ {k a}, a ∈ parIter (R.erase t) I k →
      a ∈ I ∨ ∃ s ∈ R.erase t, s.head = a := by
    intro k a hk; revert a hk
    induction k with
    | zero =>
        intro a hk; left; exact hk
    | succ k ih =>
        intro a hk
        -- hk : a ∈ stepPar (R.erase t) (parIter (R.erase t) I k)
        rcases Finset.mem_union.mp hk with hkL | hkR
        · exact ih hkL
        · rcases Finset.mem_image.mp hkR with ⟨s, hsApp, hEq⟩
          -- applicable の分解から s ∈ R.erase t
          have hsR : s ∈ R.erase t :=
            (Finset.mem_filter.mp hsApp).1
          right; exact ⟨s, hsR, hEq⟩

  -- 反証：閉包に入ると仮定
  intro hIn
  -- syncCl = parIter … (|α|)
  have : t.head ∈ parIter (R.erase t) I (Fintype.card α) := by
    exact hIn
  -- 出自分解
  have hsrc := origin this
  -- 初期にはないので「誰かの head」として入ったはず
  rcases hsrc with hI | ⟨s, hsErase, hEq⟩
  · exact hnotI hI
  -- ここから UC で `s = t` を導く（erase に矛盾）
  have hs_ne_t : s ≠ t := (Finset.mem_erase.mp hsErase).1
  have hs_in_R : s ∈ R := (Finset.mem_erase.mp hsErase).2

  -- UC: 同じ head を持つ規則は一意
  have s_eq_t : s = t := by
    -- S := {u ∈ R | u.head = t.head} は card ≤ 1
    set S := R.filter (fun u => u.head = t.head) with hS
    have hsS : s ∈ S := by
      -- s ∈ R ∧ s.head = t.head
      apply Finset.mem_filter.mpr
      exact And.intro hs_in_R (by
        -- hEq : s.head = t.head
        exact hEq)
    have htS : t ∈ S := by
      apply Finset.mem_filter.mpr
      exact And.intro ht (by rfl)
    -- もし s ≠ t なら、S は少なくとも 2 要素になる（矛盾）
    by_contra hne
    -- t は S.erase s に入る
    have t_in_erase : t ∈ S.erase s := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hne, htS⟩
    -- erase が非空 → (S.erase s).card ≥ 1
    have pos : 0 < (S.erase s).card :=
      Finset.card_pos.mpr ⟨t, t_in_erase⟩
    -- s ∈ S なので、card (S) = card (S.erase s) + 1 ≥ 2
    have step : (S.erase s).card + 1 = S.card :=
      Finset.card_erase_add_one hsS
    have two_le : Nat.succ 1 ≤ S.card := by
      have one_le : 1 ≤ (S.erase s).card := Nat.succ_le_of_lt pos
      have : 1 + 1 ≤ (S.erase s).card + 1 :=
        Nat.add_le_add_right one_le 1
      -- 書き換え
      have : 1 + 1 ≤ S.card := by
        have htmp := this
        rw [step] at htmp
        exact htmp
      -- 1+1 = Nat.succ 1
      -- 以後の定理と相性の良い形に直す
      simpa [Nat.succ_eq_add_one] using this
    -- UC の仮定（S.card ≤ 1）と矛盾
    have hSle1 : S.card ≤ 1 := by
      -- hUC t.head はまさに S のカード制限
      have := hUC t.head
      -- S の定義で書き換え不要（同じ定義）
      exact this
    exact Nat.not_succ_le_self 1 (le_trans two_le hSle1)
  -- しかし s = t なら erase に入れない
  exact hs_ne_t s_eq_t

--/***********************
-- * 5. 多重度 ≤ 1（Two-Stem + UC）
-- ***********************/

omit [LinearOrder α] in
lemma isWitness_disjoint
  (ρ : RuleOrder α) (R : Finset (Rule α)) (B S : Finset α) (t : Rule α)
  (hW : isWitness ρ R B S t) :
  Disjoint B S := by
  have hS_free : S ⊆ FreeOf B := hW.1
  unfold FreeOf at hS_free
  -- S ⊆ (univ \ B) ⇒ Disjoint B S
  --dsimp [Disjoint, Finset.disjoint_iff_inter_eq_empty]

  (expose_names; rw [subset_sdiff] at hS_free)
  simp_all only [subset_univ, true_and]
  rw [disjoint_iff] at hS_free ⊢
  simp_all only [inf_eq_inter, bot_eq_empty]
  rwa [inter_comm]



--使わないかも。
omit [Fintype α] [DecidableEq (Rule α)] in
lemma syncClIter_mono_in_steps (R : Finset (Rule α)) (I : Finset α) (k : ℕ) :
  syncClIter R I k ⊆ syncClIter R I (k + 1) := by
  unfold syncClIter
  cases h : nextHead? R (syncClIter R I k) with
  | none =>
    -- nextHead? が none なら変化なし
    simp_all only
    split
    next x => rfl
    next x k =>
      simp_all only [Nat.succ_eq_add_one]
      rfl

  | some a =>
    -- nextHead? が some a なら a を追加
    simp_all only
    split
    exact subset_insert a I
    (expose_names;
      exact
        subset_insert a
          (match nextHead? R (syncClIter R I k) with
          | none => syncClIter R I k
          | some a => insert a (syncClIter R I k)))

omit [Fintype α] [DecidableEq (Rule α)] in
lemma syncClIter_increasing (R : Finset (Rule α)) (I : Finset α) :
  ∀ k₁ k₂, k₁ ≤ k₂ → syncClIter R I k₁ ⊆ syncClIter R I k₂ := by
  intro k₁ k₂ h
  induction h with
  | refl =>
    -- k₁ = k₂ の場合
    exact Finset.Subset.refl _
  | step h ih =>
    -- k₁ ≤ k₂ → k₁ ≤ k₂ + 1
    calc syncClIter R I k₁
      ⊆ syncClIter R I _ := ih
      _ ⊆ syncClIter R I (_ + 1) := syncClIter_mono_in_steps R I _

/-
--ChatGPTによると、これは成り立たない。
lemma syncClIter_mono [DecidableEq α] (R : Finset (Rule α)) [DecidableEq (Rule α)] (k : ℕ) :
  Monotone (syncClIter R · k) := by
  -/


/-
lemma syncCl_contains_derivable [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) (I : Finset α) :
  ∀ r ∈ R, r.prem ⊆ syncCl R I →
    r.head ∈ syncCl R I ∨ r.head ∈ fires R (syncCl R I) := by
-/

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
private lemma exists_enter_before
  (R : Finset (Rule α)) (I : Finset α) (x : α) :
  ∀ N, x ∈ parIter R I N → x ∉ parIter R I 0 →
    ∃ k, k < N ∧ x ∉ parIter R I k ∧ x ∈ parIter R I (k+1) := by
  intro N
  induction' N with N ih
  · -- N = 0 は矛盾
    intro hxN hx0
    -- hxN : x ∈ parIter R I 0, hx0 : x ∉ parIter R I 0
    exact (hx0 hxN).elim
  · -- N+1
    intro hxN1 hx0
    -- 場合分け：前段 N にもう入っているか？
    by_cases hxN : x ∈ parIter R I N
    · -- 既に N で入っているなら、N に対して帰納法を適用
      have ⟨k, hk_lt, hk_notin, hk_in⟩ := ih hxN hx0
      -- k < N < N+1
      have hk' : k < N.succ := Nat.lt_trans hk_lt (Nat.lt_succ_self N)
      exact ⟨k, hk', hk_notin, hk_in⟩
    · -- N では入っていないが N+1 では入っている → ちょうど N→N+1 で入った
      exact ⟨N, Nat.lt_succ_self N, by exact hxN, by
        -- parIter R I (N+1) そのもの
        exact hxN1⟩

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/- メイン：閉包に入るが初期にない要素 x は、どこかの段 k で fires によって入る。
   そのとき head = x の規則 r と prem⊆(基底) が取れる。 -/
lemma element_has_rule_in_closure [Fintype α] [DecidableEq α]
  (R : Finset (Rule α)) (I : Finset α) (x : α)
  (hx : x ∈ syncCl R I) (hx_not_init : x ∉ I) :
  ∃ (k : ℕ) (r : Rule α),
    k < Fintype.card α ∧
    r ∈ R ∧
    r.head = x ∧
    x ∉ parIter R I k ∧
    x ∈ parIter R I (k+1) ∧
    r.prem ⊆ parIter R I k := by
  classical
  -- 記号：N = |α|
  set N := Fintype.card α
  -- hx は syncCl = parIter … N への所属
  have hxN : x ∈ parIter R I N := by
    -- syncCl の定義が parIter … N なら定義展開で一致
    -- （syncCl をそう定義している前提です）
    exact hx
  -- 初期にない：parIter 0 = I
  have hx0 : x ∉ parIter R I 0 := by
    intro hx0'
    -- parIter R I 0 = I
    have hxI : x ∈ I := by
      -- `parIter R I 0` を `I` に書き換え
      -- parIter の定義より rfl
      change x ∈ I at hx0'
      exact hx0'
    exact hx_not_init hxI
  -- まず「ちょうどこの段で入る」k を取る
  obtain ⟨k, hk_ltN, hk_notin, hk_in⟩ :=
    exists_enter_before (R:=R) (I:=I) (x:=x) N hxN hx0
  -- parIter (k+1) = stepPar R (parIter k)
  have hx_step : x ∈ stepPar R (parIter R I k) := by
    -- parIter の定義をそのまま使う
    -- hk_in : x ∈ parIter R I (k+1)
    -- 目標を書き換え
    change x ∈ stepPar R (parIter R I k) at hk_in
    exact hk_in
  -- 左側にはいないので、右側 fires にいる
  have hx_fires : x ∈ fires R (parIter R I k) := by
    -- x ∈ (parIter k) ∪ fires … で、x ∉ parIter k だから fires 側
    have := Finset.mem_union.mp hx_step
    cases this with
    | inl hxL => exact False.elim (hk_notin hxL)
    | inr hxR => exact hxR
  -- fires = (applicable …).image head から、規則 r を取り出し
  rcases Finset.mem_image.mp hx_fires with ⟨r, hr_app, hr_head⟩
  -- applicable の分解：r ∈ R ∧ prem ⊆ parIter … k ∧ head ∉ parIter … k
  have hr_split : r ∈ R ∧ r.prem ⊆ parIter R I k ∧ r.head ∉ parIter R I k :=
    Finset.mem_filter.mp hr_app
  -- 目的のタプルを組み立てて終了
  refine ⟨k, r, hk_ltN, ?hr_inR, ?hr_head_eq, hk_notin, ?hx_in_next, ?hPrem⟩
  · -- r ∈ R
    exact hr_split.1
  · -- r.head = x
    exact hr_head
  · -- x ∈ parIter R I (k+1)
    -- 先ほどの hk_in をそのまま返す（表記戻し）
    exact hk_in
  · -- r.prem ⊆ parIter R I k
    exact hr_split.2.1

/- UniqueChildがないと成り立たないらしい。
lemma twoStem_one_new_head_at_first_diff
  (ρ : RuleOrder α) (R : Finset (Rule α)) (hTS : TwoStemR R)
  (X Y : Finset α)
  (k : ℕ)
  (hXYeq : parIter (R.erase t) X k = parIter (R.erase t) Y k)
  (hΔ_here :
    ((parIter (R.erase t) X (k+1) \ parIter (R.erase t) Y (k+1)) ∪
     (parIter (R.erase t) Y (k+1) \ parIter (R.erase t) X (k+1))).Nonempty) :
  ∃! f, f ∈
    ((parIter (R.erase t) X (k+1) \ parIter (R.erase t) Y (k+1)) ∪
     (parIter (R.erase t) Y (k+1) \ parIter (R.erase t) X (k+1))) := by
  sorry
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
--次のweak_liftingの証明で用いられる。
/-- UC を使う背理補題：もし `closure (R.erase t) (B∪S)` だけで `t.head` が出るなら、
    「t が first violation」という事実に矛盾する。 -/
lemma head_from_Rerase_contra_first
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (hUC : UC R)
  (B S : Finset α) (t : Rule α)
  (hFirst : violatesFirst ρ R t (B ∪ S))
  (hHead  : t.head ∈ syncCl (R.erase t) (B ∪ S)) : False := by
  classical
  -- まず violatesFirst の中身を展開
  rcases hFirst with ⟨hViol, _hMin⟩
  rcases hViol with ⟨htR, htPrem, htHeadNot⟩
  -- t.head は初期集合には入っていない
  have h_not_init : t.head ∉ (B ∪ S) := htHeadNot

  obtain ⟨k, r, _hk_lt, hr_in, hr_head, _hx_not_before, _hx_in_after, _hr_prem⟩ :
      ∃ (k : ℕ) (r : Rule α),
        k < Fintype.card α ∧
        r ∈ (R.erase t) ∧
        r.head = t.head ∧
        t.head ∉ parIter (R.erase t) (B ∪ S) k ∧
        t.head ∈  parIter (R.erase t) (B ∪ S) (k+1) ∧
        r.prem ⊆ parIter (R.erase t) (B ∪ S) k := by
    exact element_has_rule_in_closure (R:=R.erase t) (I:=B ∪ S) (x:=t.head) hHead h_not_init

  -- r ∈ erase t なので r ≠ t かつ r ∈ R
  rcases Finset.mem_erase.mp hr_in with ⟨r_ne_t, hrR⟩

  -- UC（各 head ごとに R.filter (head=…) の card ≤ 1）から矛盾を作る
  -- 対象となるフィルタ
  set H : Finset (Rule α) := R.filter (fun s => s.head = t.head) with hH

  have ht_memH : t ∈ H := by
    -- t は R にあり、head=t.head は自明なので filter に入る
    apply Finset.mem_filter.mpr
    exact ⟨htR, by simp⟩

  have hr_memH : r ∈ H := by
    apply Finset.mem_filter.mpr
    exact ⟨hrR, by simp [hr_head]⟩

  -- H は空でなく（t が入っている）、UC により card ≤ 1
  have hH_pos : 0 < H.card := Finset.card_pos.mpr ⟨t, ht_memH⟩
  have hH_le1 : H.card ≤ 1 := by
    -- UC の定義：∀ a, (R.filter (fun t => t.head = a)).card ≤ 1
    simpa [hH] using hUC t.head

  -- よって H.card = 1
  have hH_card1 : H.card = 1 := by
    apply Nat.le_antisymm hH_le1
    exact hH_pos

  -- card=1 から H = {u} for some u
  rcases Finset.card_eq_one.mp hH_card1 with ⟨u, hHu⟩

  -- すると t ∈ {u} かつ r ∈ {u} なので t = u かつ r = u、ゆえに t = r
  have ht_eq_u : t = u := by
    have : t ∈ ({u} : Finset (Rule α)) := by simpa [hHu] using ht_memH
    simpa [Finset.mem_singleton] using this
  have hr_eq_u : r = u := by
    have : r ∈ ({u} : Finset (Rule α)) := by simpa [hHu] using hr_memH
    simpa [Finset.mem_singleton] using this

  have : r = t := by simp [ht_eq_u, hr_eq_u]
  exact r_ne_t this


--ここをChatGPTに書いてもらったら10個ぐらいsorryが残った。THikingじゃなかったからかも。
--UCとUnique Childの変換もうまくいかないし、最後までうまくいきそうにないので、一旦リセットすることにした。




--補題5.1あたり。今の所直接は使われてないが、重要だと思われる。
lemma weak_lifting
  (ρ : RuleOrder α) (R : Finset (Rule α)) [DecidablePred (IsClosed R)]
  (hUC : UC R)
  (B S : Finset α) (t : Rule α)
  (hwit : isWitness (α:=α)  ρ R B S t) :
  let J := syncCl (R.erase t) (B ∪ S)
  t.prem ⊆ J ∧ t.head ∉ J ∧ J ∈ addedFamily (α:=α) R t := by
  classical
  intro J
  rcases hwit with ⟨hSsub, hfirst⟩
  rcases hfirst with ⟨⟨htR, htPrem, htHead⟩, hmin⟩
  -- (1) prem ⊆ J
  have h1 : t.prem ⊆ J := by
    intro x hx
    have hx' : x ∈ B ∪ S := htPrem hx
    dsimp [J]
    show x ∈ syncCl (R.erase t) (B ∪ S)
    exact syncCl_infl (α:=α) (R:=R.erase t) (I:=B ∪ S) hx'

    --exact subset_closure_of_subset (R:=R.erase t) (X:=B ∪ S) hx'
  -- (2) head ∉ J ：`head_from_Rerase_contra_first` に依存
  have h2 : t.head ∉ J := by
    intro contra
    exact head_from_Rerase_contra_first (α:=α) ρ R hUC B S t ⟨⟨htR, htPrem, htHead⟩, hmin⟩ contra
  -- (3) addedFamily メンバ性
  have hJclosed : IsClosed (R.erase t) J := by exact syncCl_closed (R.erase t) (B ∪ S)
  have hJmem : J ∈ Family (α:=α) (R.erase t) := by simpa [mem_Family] using hJclosed
  have hfilter : (t.prem ⊆ J ∧ t.head ∉ J) := ⟨h1, h2⟩
  have : J ∈ (Family (α:=α) (R.erase t)).filter
            (fun I => t.prem ⊆ I ∧ t.head ∉ I) := by
    simpa [mem_filter] using And.intro hJmem hfilter
  exact And.intro h1 (And.intro h2 (by simpa [addedFamily] using this))

omit [LinearOrder α] in
lemma head_not_in_syncCl_of_erase_witness
  {ρ : RuleOrder α} {R : Finset (Rule α)} {B S : Finset α} {t : Rule α}
  (hUC : UniqueChild α R) (ht : t ∈ R)
  (hW : isWitness ρ R B S t) :
  t.head ∉ syncCl (R.erase t) (B ∪ S) := by
  classical
  -- Witness から初期不在
  have hVI : violates R t (B ∪ S) := (hW.2).1
  have hHeadNotInit : t.head ∉ (B ∪ S) := hVI.2.2
  -- もし閉包にあれば，原因規則 r ∈ R.erase t で r.head = t.head
  by_contra hIn
  rcases element_has_rule_in_closure (R.erase t) (B ∪ S) t.head hIn hHeadNotInit with
    ⟨k, r, _, hrInErase, hrHead, _, _, _⟩
  -- r ∈ R.erase t ⇒ r ∈ R ∧ r ≠ t
  have hrR : r ∈ R := by
    have : r ∈ R.erase t := hrInErase
    exact mem_of_mem_erase this
  have hrNe : r ≠ t := by
    have : r ∈ R.erase t := hrInErase
    exact (ne_of_mem_erase this)
  -- UC で head が同じなら r = t，矛盾
  have : r = t := hUC hrR ht (by exact hrHead)
  exact hrNe this

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma cause_unique_on_right_of_step_eq
  {R : Finset (Rule α)} (hUC : UniqueChild α R)
  {X Y : Finset α} (hstep : stepPar R X = stepPar R Y)
  {f : α} (hf : f ∈ X \ Y) :
  ∃! r : Rule α, r ∈ R ∧ r.prem ⊆ Y ∧ r.head = f := by
  classical
  -- f は stepPar R X に属し、等式で stepPar R Y にも属する
  have hf_in_stepX : f ∈ stepPar R X := by
    have hfX : f ∈ X := (by
      have hpair : f ∈ X ∧ f ∉ Y := by
        simpa [Finset.mem_sdiff] using hf
      exact hpair.1)
    exact Finset.mem_union.mpr (Or.inl hfX)
  have hf_in_stepY : f ∈ stepPar R Y := by
    -- 書き換え
    have := hf_in_stepX
    rw [hstep] at this
    exact this
  -- f ∉ Y なので、stepPar R Y の右側（fires）にいる
  have hf_notY : f ∉ Y := (by
    have hpair : f ∈ X ∧ f ∉ Y := by
      simpa [Finset.mem_sdiff] using hf
    exact hpair.2)
  have hf_in_firesY : f ∈ fires R Y := by
    -- step の所属を分解
    have := Finset.mem_union.mp hf_in_stepY
    cases this with
    | inl hInY => exact False.elim (hf_notY hInY)
    | inr hInF => exact hInF
  -- fires = image head (applicable …) から、原因規則 r を取り出す
  obtain ⟨r, hr_app, hr_head⟩ := Finset.mem_image.mp hf_in_firesY
  have hr_in_R : r ∈ R := (Finset.mem_filter.mp hr_app).1
  have hr_prem : r.prem ⊆ Y := (Finset.mem_filter.mp hr_app).2.1
  -- 存在は OK。あとは一意性：同じ head=f の別ルールは UC で排除
  refine ExistsUnique.intro r ?exist ?uniq
  · exact And.intro hr_in_R (And.intro hr_prem hr_head)
  · intro s hs
    -- hs : s ∈ R ∧ s.prem ⊆ Y ∧ s.head = f
    have hs_in_R : s ∈ R := hs.1
    have hs_head  : s.head = f := hs.2.2
    -- `r.head = f = s.head` → UC より r = s
    have : r = s := by
      have hre : r.head = s.head := by
        -- r.head = f かつ s.head = f
        have : r.head = f := hr_head
        have : s.head = f := hs_head
        -- どちらも f に等しいので対称性で繋ぐ
        exact Eq.trans hr_head (Eq.symm hs_head)
      exact hUC hr_in_R hs_in_R hre
    exact hUC hs_in_R hr_in_R (congrArg Rule.head (id (Eq.symm this)))

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma cause_unique_on_left_of_step_eq
  {R : Finset (Rule α)} (hUC : UniqueChild α R)
  {X Y : Finset α} (hstep : stepPar R X = stepPar R Y)
  {g : α} (hg : g ∈ Y \ X) :
  ∃! r : Rule α, r ∈ R ∧ r.prem ⊆ X ∧ r.head = g := by
  classical
  -- 対称なので X↔Y, f↔g に入れ替えて前補題を使う手もあり。
  -- ここでは直接書きます。
  have hg_in_stepY : g ∈ stepPar R Y := by
    have hgY : g ∈ Y := (by
      have hp : g ∈ Y ∧ g ∉ X := by
        simpa [Finset.mem_sdiff] using hg
      exact hp.1)
    exact Finset.mem_union.mpr (Or.inl hgY)
  have hg_in_stepX : g ∈ stepPar R X := by
    have := hg_in_stepY
    -- 等式の対称を使う
    have hstep' : stepPar R Y = stepPar R X := Eq.symm hstep
    rw [hstep'] at this
    exact this
  have hg_notX : g ∉ X := (by
    have hp : g ∈ Y ∧ g ∉ X := by
      simpa [Finset.mem_sdiff] using hg
    exact hp.2)
  have hg_in_firesX : g ∈ fires R X := by
    have := Finset.mem_union.mp hg_in_stepX
    cases this with
    | inl hInX => exact False.elim (hg_notX hInX)
    | inr hInF => exact hInF
  obtain ⟨r, hr_app, hr_head⟩ := Finset.mem_image.mp hg_in_firesX
  have hr_in_R : r ∈ R := (Finset.mem_filter.mp hr_app).1
  have hr_prem : r.prem ⊆ X := (Finset.mem_filter.mp hr_app).2.1
  refine ExistsUnique.intro r ?ex ?uniq
  · exact And.intro hr_in_R (And.intro hr_prem hr_head)
  · intro s hs
    have hs_in_R : s ∈ R := hs.1
    have hs_head  : s.head = g := hs.2.2
    have : r = s := by
      have hre : r.head = s.head := by
        exact Eq.trans hr_head (Eq.symm hs_head)
      exact hUC hr_in_R hs_in_R hre
    exact hUC hs_in_R hr_in_R (congrArg Rule.head (id (Eq.symm this)))

/-上と同じ。
/- `UniqueChild` があれば原因規則は一意（右差分版；左差分も同様に証明可） -/
lemma cause_unique_on_left_of_step_eq
  {R : Finset (Rule α)} (hUC : UniqueChild α R)
  {X Y : Finset α} (hstep : stepPar R X = stepPar R Y)
  {g : α} (hg : g ∈ Y \ X) :
  ∃! r, r ∈ R ∧ r.prem ⊆ X ∧ r.head = g := by
  classical
  rcases cause_exists_on_left_of_step_eq (R:=R) hstep hg with ⟨r, hrR, hrPr, hrHd⟩
  refine ⟨r, ?ex, ?uniq⟩
  · exact ⟨hrR, hrPr, hrHd⟩
  · intro s hs
    have hsR : s ∈ R := hs.1
    have hsHd : s.head = g := hs.2.2
    have : r = s := hUC hrR hsR (by
      -- r.head = s.head ： r.head = g = s.head
      have : r.head = g := hrHd
      have : s.head = g := hsHd
      exact Eq.trans hrHd (hsHd.symm))
    exact hUC hsR hrR (congrArg Rule.head (id (Eq.symm this)))
  -/

lemma disjoint_union_eq_implies_right_eq
  {α : Type*} [DecidableEq α]
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (h : B ∪ S₁ = B ∪ S₂) : S₁ = S₂ := by
  classical
  apply le_antisymm
  · -- S₁ ⊆ S₂
    intro x hx
    -- x ∈ S₁。互いに素なので x ∉ B。
    have hxNB : x ∉ B := by
      -- `Disjoint` → `x ∈ S₁` かつ `x ∈ B` は両立しない
      -- `disjoint_left.mp hD1` を使う手もあるが、ここは素朴に：
      intro hxB
      -- x ∈ B ∩ S₁ の矛盾を作る
      have : x ∈ B ∩ S₁ := by exact mem_inter.mpr ⟨hxB, hx⟩
      -- `hD1` から `B ∩ S₁ = ∅`
      have hIntEmpty : B ∩ S₁ = (∅ : Finset α) := by
        -- `Disjoint` の定義：`disjoint_left`/`disjoint_right` 等でもOK
        -- ここでは `disjoint_iff` を使っても良いが、簡便に：
        -- Mathlib: `disjoint_left.mp hD1 x hxB hx` で矛盾にできる
        have contra := (disjoint_left.mp hD1) hxB hx
        exact by cases contra
      -- 空集合の要素にする：
      have : x ∈ (∅ : Finset α) := by simp_all only [notMem_empty]
      exact (notMem_empty x) this
    -- 和の等式から x ∈ B ∪ S₂
    have hxInUnion : x ∈ B ∪ S₂ := by
      have : x ∈ B ∪ S₁ := by exact mem_union.mpr (Or.inr hx)
      have := congrArg (fun (s : Finset α) => x ∈ s) h
      -- 書き換え： `x ∈ B ∪ S₁` ≡ `x ∈ B ∪ S₂`
      -- term で直接使うなら：
      -- `rw [h] at this` の代わりに次の2行で：
      -- （ここは戦術的に `have` を使っても良い）
      -- 簡便のため次を採用
      -- 実際の環境では `rw [h]` でOKです
      exact by
        -- tactic が使えるなら：`simpa [h] using this`
        -- ここでは直接：
        -- 既に x∈B∪S₁ を持っており、h : B∪S₁ = B∪S₂ なので差し替え可
        -- いったん rfl 書換に近い扱いをします
        -- ただしチャットでは簡潔に：
        -- （エディタでは `have := this; simpa [h] using this` が楽）
        simp_all only [mem_union, false_or, or_true]
    -- x ∉ B なので、x ∈ S₂
    have : x ∈ S₂ := by
      rcases mem_union.mp hxInUnion with hxB | hxS2
      · exact False.elim (hxNB hxB)
      · exact hxS2
    exact this
  · -- 対称に S₂ ⊆ S₁
    intro x hx
    have hxNB : x ∉ B := by
      intro hxB
      have : x ∈ B ∩ S₂ := by exact mem_inter.mpr ⟨hxB, hx⟩
      -- 同様に `Disjoint B S₂`
      have hIntEmpty : B ∩ S₂ = (∅ : Finset α) := by
        have contra := (disjoint_left.mp hD2) hxB hx
        exact by cases contra
      have : x ∈ (∅ : Finset α) := by
        have hx' : x ∈ B ∩ S₂ := this
        rw [hIntEmpty] at hx'     -- B ∩ S₂ を ∅ に書き換え
        exact hx'
      exact (notMem_empty x) this
    have hxInUnion : x ∈ B ∪ S₁ := by
      have : x ∈ B ∪ S₂ := mem_union.mpr (Or.inr hx)
      -- x ∈ B ∪ S₁ を得るには `h.symm` で書換
      exact by
        -- tactic なら：`simpa [h.symm] using this`
        simp_all only [mem_union, or_true]
    have : x ∈ S₁ := by
      rcases mem_union.mp hxInUnion with hxB | hxS1
      · exact False.elim (hxNB hxB)
      · exact hxS1
    exact this

lemma union_singleton_cases
  {α : Type*} [DecidableEq α]
  {X Y : Finset α} {f : α}
  (h : X ∪ Y = {f}) :
  (X = ∅ ∧ Y = {f}) ∨ (X = {f} ∧ Y = ∅) ∨ (X = {f} ∧ Y = {f}) := by
  classical
  -- まず X, Y はともに {f} の部分集合
  have hXsub : X ⊆ ({f} : Finset α) := by
    intro x hx
    have : x ∈ X ∪ Y := Finset.mem_union.mpr (Or.inl hx)
    -- X ∪ Y = {f}
    have h' : x ∈ ({f} : Finset α) := by
      have hxy : X ∪ Y = {f} := h
      -- `rw [h]` と同等
      have tmp := this; rw [hxy] at tmp; exact tmp
    exact h'
  have hYsub : Y ⊆ ({f} : Finset α) := by
    intro y hy
    have : y ∈ X ∪ Y := Finset.mem_union.mpr (Or.inr hy)
    have hxy : X ∪ Y = {f} := h
    have tmp := this; rw [hxy] at tmp; exact tmp

  -- f は X ∪ Y に必ずいる
  have hfUnion : f ∈ X ∪ Y := by
    have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
    -- 書換
    simp_all only [subset_singleton_iff, mem_singleton]

  rcases Finset.mem_union.mp hfUnion with hfX | hfY

  · -- ケース1：f ∈ X
    by_cases hfY' : f ∈ Y
    · -- 両方に f が入る ⇒ どちらも = {f}
      have hXeq : X = {f} :=
        le_antisymm hXsub (Finset.singleton_subset_iff.mpr hfX)
      have hYeq : Y = {f} :=
        le_antisymm hYsub (Finset.singleton_subset_iff.mpr hfY')
      exact Or.inr (Or.inr ⟨hXeq, hYeq⟩)
    · -- f ∈ X, f ∉ Y ⇒ Y = ∅, X = {f}
      have hYempty : Y = ∅ := by
        -- Y ⊆ {f} かつ f ∉ Y なので、Y の元は存在しない
        apply Finset.eq_empty_of_forall_notMem
        intro y hy
        have hy_in_singleton : y ∈ ({f} : Finset α) := hYsub hy
        have hy_eq_f : y = f := Finset.mem_singleton.mp hy_in_singleton
        -- y = f だが f ∉ Y に矛盾
        have : f ∈ Y := by simpa [hy_eq_f] using hy
        exact hfY' this
      have hXeq : X = {f} :=
        le_antisymm hXsub (Finset.singleton_subset_iff.mpr hfX)
      exact Or.inr (Or.inl ⟨hXeq, hYempty⟩)

  · -- ケース2：f ∈ Y（対称）
    by_cases hfX' : f ∈ X
    · -- 両方に f ⇒ どちらも {f}
      have hXeq : X = {f} :=
        le_antisymm hXsub (Finset.singleton_subset_iff.mpr hfX')
      have hYeq : Y = {f} :=
        le_antisymm hYsub (Finset.singleton_subset_iff.mpr hfY)
      exact Or.inr (Or.inr ⟨hXeq, hYeq⟩)
    · -- f ∈ Y, f ∉ X ⇒ X = ∅, Y = {f}
      have hXempty : X = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have hx_in_singleton : x ∈ ({f} : Finset α) := hXsub hx
        have hx_eq_f : x = f := Finset.mem_singleton.mp hx_in_singleton
        have : f ∈ X := by simpa [hx_eq_f] using hx
        exact hfX' this
      have hYeq : Y = {f} :=
        le_antisymm hYsub (Finset.singleton_subset_iff.mpr hfY)
      exact Or.inl ⟨hXempty, hYeq⟩

omit [LinearOrder α] [DecidableEq (Rule α)] in
lemma exists_singleton_lastDiff_of_syncEq_strong
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α}
  (hSync : syncCl R' U = syncCl R' V) :
  U = V ∨ ∃ (k : ℕ) (f : α),
    k + 1 ≤ Fintype.card α ∧
    parIter R' U (k+1) = parIter R' V (k+1) ∧
    (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k) = {f} := by
  classical
  -- N と P を置く
  set N := Fintype.card α
  let P : Nat → Prop := fun m => parIter R' U m = parIter R' V m
  have hPN : P N := by
    -- syncCl の定義展開
    -- hSync : parIter R' U N = parIter R' V N
    exact hSync
  have hNonempty : ∃ m, P m := ⟨N, hPN⟩
  -- 最小一致段 k₀
  let k0 : ℕ := Nat.find hNonempty
  have hk0P : P k0 := Nat.find_spec hNonempty
  -- k₀ = 0 なら U=V
  by_cases hk0_zero : k0 = 0
  · left
    -- parIter … 0 = … 0
    have h0 : parIter R' U 0 = parIter R' V 0 := by
      -- hk0P : parIter R' U k0 = parIter R' V k0
      -- 書換
      have h := hk0P
      have h' := h
      -- k0 を 0 に置換
      -- tactic: rw [hk0_zero] at h'
      -- term で：
      have : parIter R' U 0 = parIter R' V 0 := by
        -- 補助として equality を作り、`rw` を使うのが素直です
        -- ここでは `by` ブロックを使います
        -- （実ファイルでは `rw [hk0_zero] at h'; exact h'` でOK）
        -- h : P k0, hk0_zero : k0 = 0
        have hPk : parIter R' U k0 = parIter R' V k0 := by
          -- P を展開
          have hh := h
          dsimp [P] at hh
          exact hh

        -- k0 = 0 を反映してゴールへ
        have h0 : parIter R' U 0 = parIter R' V 0 := by
          simp_all only [Nat.find_eq_zero, P, N, k0]

        exact h0
      exact this
    -- 0 段は初期集合
    exact h0
  · -- k₀ > 0 の場合
    right
    have hk0_pos : 0 < k0 := Nat.pos_of_ne_zero hk0_zero
    set k := k0 - 1
    have hk_succ : k + 1 = k0 := Nat.succ_pred_eq_of_pos hk0_pos
    -- k 段の差は非空（そうでなければ最小性に反する）
    have hNe : ((parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)).Nonempty := by
      -- もし空なら parIter … k = parIter … k となり、k le k0 で一致が出る
      by_contra hEmpty
      -- 両 sdiff が空 ⇒ 相互包含で等しい
      have hXYempty : parIter R' U k \ parIter R' V k = ∅ := by
        -- 空の union の左側は空
        -- （エディタでは `have := hEmpty;` から `…` で落とせます。ここは省略）
        simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero, not_false_eq_true, implies_true, Nat.le_find_iff,
          Nat.lt_one_iff, Nat.sub_add_cancel, union_nonempty, not_or, not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset, P,
          N, k0, k]
      have hYXempty : parIter R' V k \ parIter R' U k = ∅ := by
        simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero, not_false_eq_true, implies_true, Nat.le_find_iff,
          Nat.lt_one_iff, Nat.sub_add_cancel, union_nonempty, not_or, not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset, P,
          N, k0, k]
      -- 等号：parIter R' U k = parIter R' V k
      have hEqk : parIter R' U k = parIter R' V k := by
        -- 相互 ⊆ を示す
        apply le_antisymm
        · intro x hx
          -- もし x ∉ Vk なら x ∈ X\Y のはずで矛盾
          by_contra hxV
          have hxDiff : x ∈ parIter R' U k \ parIter R' V k := by
            exact mem_sdiff.mpr ⟨hx, hxV⟩
          -- 空集合に属する矛盾
          have : x ∈ (∅ : Finset α) := by
            -- 書換
            have hx' := hxDiff
            -- rw [hXYempty] at hx'
            rw [hXYempty] at hx'
            exact hx'
          exact (Finset.notMem_empty x) this
        · intro x hx
          by_contra hxU
          have hxDiff : x ∈ parIter R' V k \ parIter R' U k := by
            exact mem_sdiff.mpr ⟨hx, hxU⟩
          have : x ∈ (∅ : Finset α) := by
            -- rw [hYXempty] at hxDiff
            rw [hYXempty] at hxDiff
            exact hxDiff
          exact (Finset.notMem_empty x) this
      -- k < k0 を作る
      have hk_lt_k0 : k < k0 := by
        -- k < k+1，かつ k+1 = k0
        have t : k < k + 1 := Nat.lt_succ_self k
        -- 書換：k+1 = k0
        -- tactic: have tt := t; rw [hk_succ] at tt; exact tt
        simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero, not_false_eq_true, implies_true, Nat.le_find_iff,
          Nat.lt_one_iff, Nat.sub_add_cancel, union_nonempty, not_or, not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset,
          tsub_lt_self_iff, zero_lt_one, and_self, P, N, k0, k]

      -- 最小性に反する：P k
      have : P k := hEqk
      -- Nat.find_min' : ∀ m < k0, ¬ P m
      have hk0_le_k : k0 ≤ k := Nat.find_min' hNonempty this

      -- 合成して k0 < k0 を作る
      have hk0_lt_self : k0 < k0 := Nat.lt_of_le_of_lt hk0_le_k hk_lt_k0

      -- 反射律に反するので矛盾
      exact (lt_irrefl _) hk0_lt_self

    -- k+1 段で一致（hk0P を書換）
    have hEq_next : parIter R' U (k+1) = parIter R' V (k+1) := by
      -- hk0P : P k0
      -- 書換：k+1 = k0
      -- tactic: have h := hk0P; rw [hk_succ] at h; exact h
        simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero, not_false_eq_true, implies_true, Nat.le_find_iff,
            Nat.lt_one_iff, Nat.sub_add_cancel, union_nonempty, P, N, k0, k]

    -- 直前段はシングルトン
    have hSingleton := lastDiff_is_singleton (R':=R') hNTF hNS (U:=U) (V:=V) (k:=k) hNe hEq_next
    rcases hSingleton with ⟨f, hf_mem, huniq⟩
    -- 差集合 SΔ = {f} を作る
    set SΔ := (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k)
    -- SΔ ⊆ {f}
    have hSub₁ : SΔ ⊆ ({f} : Finset α) := by
      intro x hx
      -- 一意性から x=f
      have hx_eq : x = f := huniq x hx
      -- x∈{f}
      have : x ∈ ({f} : Finset α) := by
        -- x=f から
        -- `mem_singleton` を使う
        exact by
          -- `by cases hx_eq; exact mem_singleton_self f` でも可
          cases hx_eq
          exact mem_singleton_self f
      exact this
    -- {f} ⊆ SΔ
    have hSub₂ : ({f} : Finset α) ⊆ SΔ := by
      intro x hx
      -- x=f かつ f∈SΔ（hf_mem）
      have hx_eq : x = f := by
        -- `mem_singleton` の逆向き
        exact Finset.mem_singleton.mp hx
      -- 書換
      -- これで x∈SΔ
      -- tactic: cases hx_eq; exact hf_mem
      cases hx_eq
      exact hf_mem
    have hEqSingle : SΔ = ({f} : Finset α) := le_antisymm hSub₁ hSub₂
    -- まとめて返す
    refine ⟨k, f, ?bound, hEq_next, ?eqΔ⟩
    · -- k+1 ≤ N
      -- k+1 = k0 ≤ N
      have hk0_le_N : k0 ≤ N := by
        -- N も witness なので最小値は N 以下
        -- `Nat.find_min'` から得られます。詳細は1–2行の補題で埋められます。
        have hk0_le_N : k0 ≤ N := Nat.find_min' hNonempty hPN
        exact hk0_le_N
      -- 書換
      -- tactic: have := hk0_le_N; rw [hk_succ] at this; exact this
      simp_all only [Nat.find_eq_zero, Nat.lt_find_iff, nonpos_iff_eq_zero, not_false_eq_true, implies_true, Nat.le_find_iff,
        Nat.lt_one_iff, Nat.sub_add_cancel, union_nonempty, mem_union, mem_sdiff, subset_singleton_iff, union_eq_empty,
        sdiff_eq_empty_iff_subset, singleton_subset_iff, Nat.find_le_iff, P, N, k0, k, SΔ]

    · -- 差集合＝{f}
      -- SΔ の定義に戻して与える
      -- ここは `rfl` で差し戻せないので、そのまま hEqSingle を返す
      exact hEqSingle

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
theorem exists_k_singleton_symmDiff_of_syncEq
  [DecidableEq α] [Fintype α]
  {R : Finset (Rule α)} (hNTF : NoTwoFreshHeads R) (hNS : NoSwap R)
  {U V : Finset α}
  (hSync : syncCl R U = syncCl R V) :
  U = V ∨ ∃ (k : ℕ) (f : α),
    k + 1 ≤ Fintype.card α ∧
    parIter R U (k+1) = parIter R V (k+1) ∧
    ((parIter R U k \ parIter R V k) ∪ (parIter R V k \ parIter R U k) = {f}) := by
  classical
  simpa using
    exists_singleton_lastDiff_of_syncEq_strong (R':=R) hNTF hNS (U:=U) (V:=V) hSync

----

--使ってないもので使っているだけ。
omit [DecidableEq (Rule α)] in
/-- **スリム版**：閉包が等しければ，直前段は片側単元差 `{f}`。
    さらにその `{f}` は (UC なしでも) 原因規則 `r ∈ R'` を持つ。 -/
private lemma lastDiff_unique_cause_of_syncEq_slim
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  {U V : Finset α}
  (hSync : syncCl R' U = syncCl R' V) :
  U = V ∨ ∃ (k : ℕ) (f : α) (r : Rule α),
    k + 1 ≤ Fintype.card α ∧
    parIter R' U (k+1) = parIter R' V (k+1) ∧
    ( ((parIter R' U k \ parIter R' V k) = ∅ ∧ parIter R' V k \ parIter R' U k = {f}
        ∧ r ∈ R' ∧ r.prem ⊆ parIter R' U k ∧ r.head = f)  -- 右差分のみ：左側 fires 由来
      ∨ ((parIter R' V k \ parIter R' U k) = ∅ ∧ parIter R' U k \ parIter R' V k = {f}
        ∧ r ∈ R' ∧ r.prem ⊆ parIter R' V k ∧ r.head = f) ) := by
  classical
  -- 強化版：直前段の単元差＋次段一致を取得
  have hED := exists_singleton_lastDiff_of_syncEq_strong (R':=R') hNTF hNS (U:=U) (V:=V) hSync
  cases hED with
  | inl hUV =>
      exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩
      -- 記号
      set X := parIter R' U k
      set Y := parIter R' V k
      -- k+1 段一致 ⇒ step 等式
      have hstep : stepPar R' X = stepPar R' Y := by
        -- parIter … (k+1) = stepPar R' X, stepPar R' Y
        have hx : parIter R' U (k+1) = stepPar R' X := rfl
        have hy : parIter R' V (k+1) = stepPar R' Y := rfl
        -- 書換して終了
        have t := hEqNext
        rw [hx, hy] at t
        exact t
      -- 側の決定
      have hΔ : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        -- 定義置換
        simpa [X, Y]
          using (hSingle :
            (parIter R' U k \ parIter R' V k) ∪ (parIter R' V k \ parIter R' U k) = {f})
      have hcases := union_singleton_cases (X:=(X \ Y)) (Y:=(Y \ X)) (f:=f) hΔ
      -- NoSwap による “両方 {f}” の排除
      have hnoswap_side : (X \ Y = ∅) ∨ (Y \ X = ∅) := hNS X Y hstep
      cases hcases with
      | inl hXY =>
          -- (X\Y)=∅, (Y\X)={f} ：右差分のみ
          rcases hXY with ⟨hXemp, hYone⟩
          -- f ∈ Y\X を作る
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          -- 原因規則（存在）
          rcases cause_exists_on_left_of_step_eq (R:=R') hstep hfYX with ⟨r, hrR, hrPr, hrHd⟩
          -- まとめて返す
          exact Or.inr ⟨k, f, r, hkBound, hEqNext, Or.inl ⟨hXemp, hYone, hrR, hrPr, hrHd⟩⟩
      | inr hRest =>
          cases hRest with
          | inl hYX =>
              -- (Y\X)=∅, (X\Y)={f} ：左差分のみ
              rcases hYX with ⟨hYemp, hXone⟩
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := mem_singleton_self f
                have t := this;
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]

              rcases cause_exists_on_right_of_step_eq (R:=R') hstep hfXY with ⟨r, hrR, hrPr, hrHd⟩
              right
              refine ⟨k, f, r, hkBound, hEqNext, Or.inr ⟨?_, ?_, hrR, hrPr, hrHd⟩⟩
              · exact hXone
              · exact hYemp

          | inr hBoth =>
              -- 両方 {f} は NoSwap に反するので矛盾で潰す
              cases hnoswap_side with
              | inl hXYempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (X \ Y) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hBoth.left.symm] at t; exact t
                    have t := hf; rw [hXYempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))
              | inr hYXempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (Y \ X) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hBoth.right.symm] at t; exact t
                    have t := hf; rw [hYXempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))

--使ってない
omit [DecidableEq (Rule α)] in
lemma lastDiff_unique_cause_of_syncEq_unique
  {R' : Finset (Rule α)} (hNTF : NoTwoFreshHeads R') (hNS : NoSwap R')
  (hUC' : UniqueChild α R')   -- ★ R' 側（= R.erase t 側）で UC
  {U V : Finset α}
  (hSync : syncCl R' U = syncCl R' V) :
  U = V ∨ ∃ (k : ℕ) (f : α),
    k + 1 ≤ Fintype.card α ∧ parIter R' U (k+1) = parIter R' V (k+1) ∧
    ( ((parIter R' U k \ parIter R' V k) = ∅ ∧ ∃! r, r ∈ R' ∧ r.prem ⊆ parIter R' U k ∧ r.head = f)
    ∨ ((parIter R' V k \ parIter R' U k) = ∅ ∧ ∃! r, r ∈ R' ∧ r.prem ⊆ parIter R' V k ∧ r.head = f) ) := by
  classical
  -- まず存在版を取得
  have hslim :=
  lastDiff_unique_cause_of_syncEq_slim (R':=R') hNTF hNS (U:=U) (V:=V) hSync
 -- 以降は分岐
  cases hslim with
  | inl hUV => exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, r, hkBound, hEqNext, hside⟩
      -- 記号
      set X := parIter R' U k
      set Y := parIter R' V k
      have hstep : stepPar R' X = stepPar R' Y := by
        have hx : parIter R' U (k+1) = stepPar R' X := rfl
        have hy : parIter R' V (k+1) = stepPar R' Y := rfl
        have t := hEqNext; rw [hx, hy] at t; exact t
      -- 側ごとに一意化を付与
      cases hside with
      | inl hR =>
          rcases hR with ⟨hXemp, hYone, hrR, hrPr, hrHd⟩
          -- 右差分：Y\X={f} → f∈Y\X
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          -- 一意化
          -- 既存の r は witness；その一意性集合を作る
          have hex : ∃! s, s ∈ R' ∧ s.prem ⊆ X ∧ s.head = f := by
            -- 存在は cause_exists_on_left_of_step_eq
            rcases cause_exists_on_left_of_step_eq (R:=R') hstep hfYX with ⟨s, hsR, hsPr, hsHd⟩
            refine ⟨s, ?ex, ?uniq⟩
            · exact ⟨hsR, hsPr, hsHd⟩
            · intro s' hs'

              apply hUC'
              · exact hs'.1
              · exact hsR
              ·
                have : s.head = f := hsHd
                have : s'.head = f := hs'.2.2
                subst hsHd
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, and_true, X, Y]
          exact Or.inr ⟨k, f, hkBound, hEqNext, Or.inl ⟨hXemp, hex⟩⟩
      | inr hL =>
          rcases hL with ⟨hYemp, hXone, hrR, hrPr, hrHd⟩
          have hfXY : f ∈ X \ Y := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hXone.symm] at t; exact t
          have hex : ∃! s, s ∈ R' ∧ s.prem ⊆ Y ∧ s.head = f := by
            rcases cause_exists_on_right_of_step_eq (R:=R') hstep hfXY with ⟨s, hsR, hsPr, hsHd⟩
            refine ⟨s, ?ex0, ?uniq0⟩
            · exact ⟨hsR, hsPr, hsHd⟩
            · intro s' hs'
              subst hrHd
              simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]
              obtain ⟨left, right⟩ := hs'
              obtain ⟨left_1, right⟩ := right
              apply hUC'
              · simp_all only
              · simp_all only
              · simp_all only
          exact Or.inr ⟨k, f, hkBound, hEqNext, Or.inr ⟨hYemp, hex⟩⟩

lemma eq_or_unique_cause_for_erased
  {R : Finset (Rule α)} {t : Rule α}
  (hNTF' : NoTwoFreshHeads (R.erase t)) (hNS' : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hEqCl : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  (B ∪ S₁ = B ∪ S₂) ∨
  ∃ (k : ℕ) (f : α) (r : Rule α),
    k + 1 ≤ Fintype.card α ∧
    parIter (R.erase t) (B ∪ S₁) (k+1) = parIter (R.erase t) (B ∪ S₂) (k+1) ∧
    ( ((parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k) = ∅ ∧
        parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = {f}
        ∧ r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₁) k ∧ r.head = f)
    ∨ ((parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k) = ∅ ∧
        parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k = {f}
        ∧ r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k ∧ r.head = f) ) := by
  classical
  -- 強化版（あなたが通したもの）を R' := R.erase t に適用
  have hED :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R':=R.erase t) hNTF' hNS' (U:=B ∪ S₁) (V:=B ∪ S₂) hEqCl
  cases hED with
  | inl hUV =>
      exact Or.inl hUV
  | inr hK =>
      rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩
      set X := parIter (R.erase t) (B ∪ S₁) k
      set Y := parIter (R.erase t) (B ∪ S₂) k
      have hstep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
        have hx : parIter (R.erase t) (B ∪ S₁) (k+1) = stepPar (R.erase t) X := rfl
        have hy : parIter (R.erase t) (B ∪ S₂) (k+1) = stepPar (R.erase t) Y := rfl
        have t := hEqNext; rw [hx, hy] at t; exact t
      have hΔ : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        simpa [X, Y] using hSingle
      have hcases := union_singleton_cases (X:=(X \ Y)) (Y:=(Y \ X)) (f:=f) hΔ
      have hnoswap_side : (X \ Y = ∅) ∨ (Y \ X = ∅) := hNS' X Y hstep
      cases hcases with
      | inl hXY =>
          rcases hXY with ⟨hXemp, hYone⟩
          have hfYX : f ∈ Y \ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have t := this; rw [hYone.symm] at t; exact t
          rcases cause_exists_on_left_of_step_eq (R:=R.erase t) hstep hfYX with ⟨r, hrR, hrPr, hrHd⟩
          exact Or.inr ⟨k, f, r, hkBound, hEqNext,
            Or.inl ⟨hXemp, hYone, hrR, hrPr, hrHd⟩⟩
      | inr hRest =>
          cases hRest with
          | inl hYX =>
              rcases hYX with ⟨hYemp, hXone⟩
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := mem_singleton_self f
                have t := this;
                simp_all only [sdiff_eq_empty_iff_subset, mem_singleton, X, Y]
              rcases cause_exists_on_right_of_step_eq (R:=R.erase t) hstep hfXY with ⟨r, hrR, hrPr, hrHd⟩
              right
              constructor
              · simp
                refine And.intro hkBound ?_
                refine And.intro hEqNext ?_
                -- 分岐は左差分 = {f} の側（Or.inr）を選ぶ
                subst hrHd
                simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, mem_singleton, singleton_inj, true_and, or_true,
                  singleton_union, X, Y]
                obtain ⟨left, right⟩ := hrR
                apply Exists.intro
                · apply Exists.intro
                  · tauto

          | inr hboth =>
              -- 両側 {f} は NoSwap と矛盾
              cases hnoswap_side with
              | inl hXYempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (X \ Y) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hboth.left.symm] at t; exact t
                    have t := hf; rw [hXYempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))
              | inr hYXempty =>
                  have : f ∈ (∅ : Finset α) := by
                    have hf : f ∈ (Y \ X) := by
                      have : f ∈ ({f} : Finset α) := mem_singleton_self f
                      have t := this; rw [hboth.right.symm] at t; exact t
                    have t := hf; rw [hYXempty] at t; exact t
                  exact (False.elim ((Finset.notMem_empty f) this))

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
/-- **消去系の差の head は `t.head` ではない**：
`r ∈ R.erase t` が差 `{f}` を生む原因規則なら，`f ≠ t.head`。 -/
lemma erased_cause_head_ne_thead
  {R : Finset (Rule α)} {t r : Rule α} (hUC : UniqueChild α R)(ht : t ∈ R)
  (hrErase : r ∈ R.erase t) :
  r.head ≠ t.head := by
  classical
  have hrR : r ∈ R := mem_of_mem_erase hrErase
  have htR : t ∈ R := by
    -- `mem_of_mem_erase` は `r` 用なので，`t ∈ R` は別途前提で持っているのが普通です。
    -- ここでは「UC で矛盾を出す」ために `t ∈ R` を仮定して呼び出す側で渡してください。
    -- 万一ここで必要なら引数に `ht : t ∈ R` を追加してください。
    -- ダミーを置かず，外側の定理では `ht : t ∈ R` を既に持っているはずです。
    exact ht
  intro hEq
  have : r = t := hUC hrR htR hEq
  exact ne_of_mem_erase hrErase this


-- (A) 追加仮定：等閉包で生じる“最小一致段直前の 1 点差”は必ず `t.head`. -/
def OnlyTLastDiff (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α) : Prop :=
∀ {B S₁ S₂ : Finset α} {k : ℕ} {f : α},
  isWitness ρ R B S₁ t →
  isWitness ρ R B S₂ t →
  parIter (R.erase t) (B ∪ S₁) (k+1) = parIter (R.erase t) (B ∪ S₂) (k+1) →
  ((parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k) ∪
   (parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k)) = {f} →
  f = t.head
  -- 右枝（sdiff 受け）

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 時間方向の単調性（1段） -/
lemma parIter_succ_superset (R : Finset (Rule α)) (I : Finset α) (m : ℕ) :
  parIter R I m ⊆ parIter R I (m+1) := by
  intro x hx
  -- parIter R I (m+1) = stepPar R (parIter R I m)
  have : x ∈ stepPar R (parIter R I m) := Finset.mem_union.mpr (Or.inl hx)
  simpa using this

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 時間方向の単調性：m ≤ n ⇒ parIter R I m ⊆ parIter R I n -/
lemma parIter_le_of_le (R : Finset (Rule α)) (I : Finset α) {m n : ℕ}
  (hmn : m ≤ n) : parIter R I m ⊆ parIter R I n := by
  classical
  induction' hmn with n hmn ih
  · simp
  · intro x hx
    exact parIter_succ_superset R I n (ih hx)

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma mem_fires_of_applicable
  [DecidableEq α]
  {R : Finset (Rule α)} {I : Finset α} {r : Rule α}
  (hr : r ∈ applicable R I) :
  r.head ∈ fires R I := by
  -- fires = (applicable …).image (·.head)
  change r.head ∈ (applicable R I).image (fun t => t.head)
  exact mem_image.mpr ⟨r, hr, rfl⟩

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- ルールが `R` にあり，prem ⊆ I かつ head ∉ I なら `applicable R I` に入る。 -/
lemma mem_applicable_of_prem_subset_and_head_notin
  {R : Finset (Rule α)} {I : Finset α} {r : Rule α}
  (hrR : r ∈ R) (hprem : r.prem ⊆ I) (hnot : r.head ∉ I) :
  r ∈ applicable R I := by
  -- applicable = R.filter …
  exact mem_filter.mpr ⟨hrR, ⟨hprem, hnot⟩⟩

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- `Y \\ X = {f}` なら `f ∈ Y` かつ `f ∉ X`。 -/
lemma mem_and_not_mem_of_sdiff_singleton_right
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (h : Y \ X = {f}) : f ∈ Y ∧ f ∉ X := by
  have hf : f ∈ Y \ X := by
    simp [h]
  exact mem_sdiff.mp hf

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
/-- 集合のサイズが高々 1 で，`a, b` が共に入っていれば等しい。 -/
lemma eq_of_two_mem_of_card_le_one
  {s : Finset α} {a b : α}
  (ha : a ∈ s) (hb : b ∈ s) (hcard : s.card ≤ 1) : a = b := by
  classical
  by_contra hne
  -- {a,b} ⊆ s かつ card {a,b} = 2 → 2 ≤ card s と矛盾
  have hpair_subset : ({a,b} : Finset α) ⊆ s := by
    intro x hx
    have : x = a ∨ x = b := by
      simp_all only [mem_insert, mem_singleton]
    cases this with
    | inl hx => simpa [hx] using ha
    | inr hx => simpa [hx] using hb
  have hpair_card : ({a,b} : Finset α).card = 2 := by
    simp [hne]
  have : 2 ≤ s.card := by
    have hle : ({a, b} : Finset α).card ≤ s.card :=
      card_mono hpair_subset
    exact by
      simpa [hpair_card] using hle

  have hcontr : 2 ≤ (1 : Nat) := le_trans this hcard
  exact (Nat.not_succ_le_self 1) hcontr   -- つまり ¬(2 ≤ 1)

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma subset_singleton_of_card_le_one_of_mem
  {s : Finset α} {f : α}
  (hcard : s.card ≤ 1) (hf : f ∈ s) :
  s ⊆ ({f} : Finset α) := by
  intro x hx
  -- s に 2 つの元 x, f があるので card≤1 なら x=f
  have : x = f :=
    eq_of_two_mem_of_card_le_one (ha := hx) (hb := hf) (hcard := hcard)
  -- x ∈ {f}
  exact Finset.mem_singleton.mpr this

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma eq_singleton_of_subset_singleton_nonempty
  {s : Finset α} {f : α}
  (hsub : s ⊆ ({f} : Finset α)) (hne : s.Nonempty) :
  s = ({f} : Finset α) := by
  -- ext で両包含
  ext x
  constructor
  · intro hx; exact hsub hx
  · intro hx
    -- hx : x = f
    have hf : f ∈ s := by
      rcases hne with ⟨y, hy⟩
      -- hsub で y ∈ {f}、なので y=f
      have : y = f := by
        have hy' : y ∈ ({f} : Finset α) := hsub hy
        exact Finset.mem_singleton.mp hy'
      -- したがって f ∈ s
      simpa [this] using hy
    -- x=f なら {f} の元は f なので f ∈ s を使って戻す
    have : x = f := Finset.mem_singleton.mp hx
    simpa [this] using hf

omit [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma sdiff_singleton_right_of_symmdiff_singleton_left_empty
  {X Y : Finset α} {f : α}
  (hXYempty : X \ Y = ∅)
  (hsymm : (X \ Y) ∪ (Y \ X) = ({f} : Finset α)) :
  Y \ X = ({f} : Finset α) := by
  -- 左が空なので (X\Y) ∪ (Y\X) = Y\X
  have : (X \ Y) ∪ (Y \ X) = (Y \ X) := by
    -- ∅ ∪ A = A
    -- `Finset.union_eq_left.2` で `X\Y ⊆ Y\X` を要る形ですが、ここは直接書き換えでもOK
    -- ここでは素直に hXYempty で書換
    -- rewrite を避けるなら ext でも可。簡潔に：
    have : X \ Y = (∅ : Finset α) := hXYempty
    -- (∅) ∪ (Y\X) = (Y\X)
    simp [this]

  -- よって Y\X = {f}
  rw [this] at hsymm
  exact hsymm

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
@[simp] lemma result_right_impossible
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) (ht : t ∈ R)
  --(hNTF : NoTwoFreshHeads (R.erase t)) (hNS : NoSwap (R.erase t))
  {B S₁ : Finset α}
  (hW1 : isWitness ρ R B S₁ t)  -- ← violatesFirst を含む
  -- k, f, U, V, X, Y は本体側と一致させてください
  {k : ℕ} {f : α}
  (U V : Finset α) (hU : U = B ∪ S₁) --(hV : V = B ∪ S₂)
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (X Y : Finset α)
  (hX : X = parIter (R.erase t) U k)
  (hY : Y = parIter (R.erase t) V k)
  -- 右枝の仮定（X\Y=∅ & 原因一意）
  (hXYempty : X \ Y = ∅)
  (hExu : ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f)
  -- ここがキモ：この枝での head 同一性。これを仮定に含めます。
  (hf_head : f = t.head)
  -- |α| 段まで持ち上げるための境界
  (hkBound : k + 1 ≤ Fintype.card α) :
  False :=
by
  classical
  -- 一意原因 r を取り出す
  obtain ⟨r, hrU, _huniq⟩ := hExu
  have hr_in  : r ∈ R.erase t := hrU.left
  have hr_prem: r.prem ⊆ X    := (hrU.right).left
  have hr_head: r.head = f     := (hrU.right).right

  -- fires と NoTwoFreshHeads を準備（後で Y\X ⊆ {f} などにも使えるが、
  -- ここでは f を syncCl U に持ち上げるのが目的なので最低限で進める）
  -- r が X で applicable：head∉X は applicable 側の条件から得る
  have hYdiff_singleton : Y \ X = ({f} : Finset α) := by
  -- あなたの既存補題（card ≤ 1 から単点化）と「非空」の組合せで証明
  -- すでにお持ちの補題群で詰められます
    apply sdiff_singleton_right_of_symmdiff_singleton_left_empty hXYempty
    have hUC' : UniqueChild α R :=
      (UniqueChild_iff_UC R).mpr hUC

    -- UC と ht, hr_in から、消去側の頭は t.head と一致しない
    have hneq : r.head ≠ t.head :=
      erased_cause_head_ne_thead
        (R:=R) (t:=t) (r:=r) hUC' ht hr_in

    -- ところが、hr_head : r.head = f と hf_head : f = t.head で r.head = t.head
    have hcontra : False := by
      have hrt : r.head = t.head :=
        Eq.trans hr_head hf_head
      exact hneq hrt

    -- 矛盾から任意の結論。ここでは目標を出す：
    exact False.elim hcontra

  have hf_notinX : f ∉ X :=
    (mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f) hYdiff_singleton).2

  -- ↑ 上のスケッチが気になる場合は、次の一行で直接 applicable を作り、
  --   そこから fires 経由で f ∉ X を取り出してください：

  have hr_app : r ∈ applicable (R.erase t) X :=
    mem_applicable_of_prem_subset_and_head_notin
      (hrR := hr_in) (hprem := hr_prem) (hnot := ?_)

  have hf_in_firesX : f ∈ fires (R.erase t) X := by
    have : r.head ∈ fires (R.erase t) X := mem_fires_of_applicable hr_app
    cases hr_head; simpa using this

  -- ここから f を (k+1) 段→|α| 段（=syncCl）へ持ち上げる。
  -- まず f ∈ stepPar (R.erase t) X
  have hf_in_stepX : f ∈ stepPar (R.erase t) X :=
    Finset.mem_union.mpr (Or.inr hf_in_firesX)

  -- hEqNext を X,Y に書き換え
  have hStepEq : stepPar (R.erase t) (parIter (R.erase t) U k)
                   = stepPar (R.erase t) (parIter (R.erase t) V k) := by
    simpa [hX, hY] using hEqNext

  have hf_in_stepY : f ∈ stepPar (R.erase t) Y := by
    -- 等式で membership を移送
    have : (f ∈ stepPar (R.erase t) X) = (f ∈ stepPar (R.erase t) Y) :=
      congrArg (fun s => f ∈ s) (by simpa [hX, hY] using hEqNext)
    exact Eq.mp this hf_in_stepX

  -- stepPar Y = Y ∪ fires Y なので、いずれにせよ f ∈ parIter … V (k+1)
  have hf_in_k1_V : f ∈ parIter (R.erase t) V (k+1) := by
    -- Y = parIter … V k
    have : f ∈ stepPar (R.erase t) (parIter (R.erase t) V k) := by
      simpa [hY] using hf_in_stepY
    exact this

  -- k+1 段の等式で U 側へ
  have hf_in_k1_U : f ∈ parIter (R.erase t) U (k+1) := by
    have : (f ∈ parIter (R.erase t) V (k+1))
         = (f ∈ parIter (R.erase t) U (k+1)) :=
      congrArg (fun s => f ∈ s) (hEqNext.symm)
    exact Eq.mp this hf_in_k1_V

  -- 段数単調性で syncCl へ
  have hf_in_syncU : f ∈ syncCl (R.erase t) U := by
    have mono :
      parIter (R.erase t) U (k+1) ⊆ parIter (R.erase t) U (Fintype.card α) :=
      parIter_le_of_le (R.erase t) U hkBound
    have : f ∈ parIter (R.erase t) U (Fintype.card α) := mono hf_in_k1_U
    simpa [syncCl] using this

  -- f = t.head による書き換え
  have : t.head ∈ syncCl (R.erase t) U := by
    cases hf_head; exact hf_in_syncU

  -- 最後は first violation との矛盾
  exact head_from_Rerase_contra_first
          (ρ:=ρ) (R:=R) (hUC:=hUC) (B:=B) (S:=S₁) (t:=t)
          (hFirst := hW1.right) (hHead := by
            -- U = B ∪ S₁

            -- U を引数にもつ syncCl の等式に持ち上げる
            have hSyncEq :
                syncCl (R.erase t) U = syncCl (R.erase t) (B ∪ S₁) :=
              congrArg (fun I => syncCl (R.erase t) I) hU

            -- 「集合の等式」から「所属命題の等式」へ
            have hMemEq :
                (t.head ∈ syncCl (R.erase t) U)
                  = (t.head ∈ syncCl (R.erase t) (B ∪ S₁)) :=
              congrArg (fun s => t.head ∈ s) hSyncEq

            -- これで書き換えてゴールを得る

            exact Eq.mp hMemEq this

            --change t.head ∈ syncCl (R.erase t) (B ∪ S₁)

            )

  exact Eq.mpr_not (congrArg (Membership.mem X) hr_head) hf_notinX

-- A: 対称差が単点 & 次段一致 → 直前段は等しい。なりたたない。
/-
lemma singleton_symmDiff_step_eq_forces_prev_equal
  [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R) (hNTF : NoTwoFreshHeads R)
  (X Y : Finset α) (f : α)
  (hStep : stepPar R X = stepPar R Y)
  (hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α))
  (hUC' : UniqueChild α R) : X = Y := by
-/

/-
lemma singleton_symmDiff_step_eq_struct
  [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R) (hNTF : NoTwoFreshHeads R)
  (X Y : Finset α) (f : α)
  (hStep : stepPar R X = stepPar R Y)
  (hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α))
  (hUC' : UniqueChild α R) :
  (X \ Y = ∅ ∧ Y \ X = {f} ∧ f ∈ fires R X ∧ f ∉ X)
  ∨
  (Y \ X = ∅ ∧ X \ Y = {f} ∧ f ∈ fires R Y ∧ f ∉ Y) :=
by
  sorry
-/

/-
-- B: 直前段が等しい & 次段一致 → 初期入力も等しい
lemma prev_equal_lifts_to_U_eq_V
  [DecidableEq α]
  (R : Finset (Rule α)) (U V : Finset α) (k : ℕ)
  (hEqNext : parIter R U (k+1) = parIter R V (k+1))
  (hPrevEq : parIter R U k = parIter R V k) : U = V := by
  -- parIter の再帰定義で下ろす（あなたの標準補題に合わせて詰めてください）
  -- スケッチ：
  --   parIter R U 0 = U, parIter R V 0 = V
  --   k から 0 へ帰納で等式を伝播
  admit
-/

/-
omit [DecidableEq α] [Fintype α] [LinearOrder α] in
--証明ルートを変えたので以下はいらなくなったかも。
lemma head_ne_thead_on_right_branch
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (t : Rule α)
  (hUC : UniqueChild α R) (ht : t ∈ R)
  (X : Finset α)
  (hExu : ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f)
  : f ≠ t.head := by
  classical
  -- 一意実在の r を取り出す
  rcases hExu with ⟨r, hr_pack, _uniq⟩
  have hrErase : r ∈ R.erase t := hr_pack.left
  have hrHead  : r.head = f     := (hr_pack.right).right
  -- erase 側の head は t.head と一致しない
  have hneq : r.head ≠ t.head :=
    erased_cause_head_ne_thead (hUC := hUC) (ht := ht) (hrErase := hrErase)
  -- r.head = f で置換して f ≠ t.head
  exact by
    intro hf
    apply hneq
    simp [hrHead, hf]
-/

/-
--成り立たない。
lemma head_eq_thead_on_right_branch
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) (ht : t ∈ R)
  {B S₁: Finset α} (hW1 : isWitness ρ R B S₁ t)
  {k : ℕ} {f : α}
  (U V : Finset α) (hU : U = B ∪ S₁)
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (X Y : Finset α)
  (hX : X = parIter (R.erase t) U k)
  (hY : Y = parIter (R.erase t) V k)
  (hXYempty : X \ Y = ∅)
  (hExu : ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f)
  : f = t.head := by
  sorry
-/
/-
--成り立たない。
lemma head_eq_thead_on_left_branch
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) (ht : t ∈ R)
  {B S₁  : Finset α} (hW1 : isWitness ρ R B S₁ t)
  {k : ℕ} {f : α}
  (U V : Finset α) (hU : U = B ∪ S₁)
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (X Y : Finset α)
  (hX : X = parIter (R.erase t) U k)
  (hY : Y = parIter (R.erase t) V k)
  (hYXempty : Y \ X = ∅)
  (hExuY : ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f)
  : f = t.head := by
  -- 右枝のミラー。あなたの「左枝」ブロックを関数化すればOK。
  admit
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma contra_from_head_in_sync_left
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R)
  {B S₁ : Finset α} (hW1 : isWitness ρ R B S₁ t)
  {k : ℕ} (U V : Finset α) (hU : U = B ∪ S₁)
  (hEqNext : parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  {X Y : Finset α} (hX : X = parIter (R.erase t) U k) (hY : Y = parIter (R.erase t) V k)
  (hkBound : k + 1 ≤ Fintype.card α)
  (hStepEq : stepPar (R.erase t) X = stepPar (R.erase t) Y)
  (rY : Rule α)  (hrY_prem : rY.prem ⊆ Y)
  (hy : rY.head ∈ Y) (hf_head : rY.head = t.head) :
  False := by
  classical
  -- y := rY.head ∈ stepPar … Y
  have hy_stepY : rY.head ∈ stepPar (R.erase t) Y := by
    -- stepPar R I = I ∪ fires R I なので，inl で十分
    exact Finset.mem_union.mpr (Or.inl hy)

  -- step の等式で X 側へ運ぶ
  have hy_stepX : rY.head ∈ stepPar (R.erase t) X := by
    -- (rY.head ∈ stepPar X) = (rY.head ∈ stepPar Y)
    have hmem :=
      congrArg (fun s => rY.head ∈ s) hStepEq
    -- 右辺が真なので左辺も真
    exact Eq.mp hmem.symm hy_stepY

  -- parIter の (k+1) 段へ（X = parIter … U k）
  have hy_in_k1_U : rY.head ∈ parIter (R.erase t) U (k+1) := by
    --change rY.head ∈ stepPar (R.erase t) (parIter (R.erase t) U k) at hy_stepX
    simpa [hX] using hy_stepX

  -- |α| 段（= syncCl）まで上げる
  have hy_in_syncU : rY.head ∈ syncCl (R.erase t) U := by
    have hmono :
      parIter (R.erase t) U (k+1)
        ⊆ parIter (R.erase t) U (Fintype.card α) :=
      parIter_le_of_le (R.erase t) U hkBound
    have : rY.head ∈ parIter (R.erase t) U (Fintype.card α) := hmono hy_in_k1_U
    change rY.head ∈ syncCl (R.erase t) U
    simpa [syncCl] using this

  -- U = B ∪ S₁ で syncCl の引数を書き換え
  have hSyncEq :
      syncCl (R.erase t) U = syncCl (R.erase t) (B ∪ S₁) :=
    congrArg (fun I => syncCl (R.erase t) I) hU
  have hMemEq :
      (rY.head ∈ syncCl (R.erase t) U)
        = (rY.head ∈ syncCl (R.erase t) (B ∪ S₁)) :=
    congrArg (fun s => rY.head ∈ s) hSyncEq
  have hy_in_syncUS1 : rY.head ∈ syncCl (R.erase t) (B ∪ S₁) :=
    Eq.mp hMemEq hy_in_syncU

  -- rY.head = t.head で書き換えて，t.head ∈ syncCl (R.erase t) (B ∪ S₁)
  have hthead_in_syncUS1 : t.head ∈ syncCl (R.erase t) (B ∪ S₁) := by
    --cases hf_head
    subst hY hU hX
    simp_all only

  -- violatesFirst と矛盾
  exact head_from_Rerase_contra_first
    (ρ:=ρ) (R:=R) (hUC:=hUC) (B:=B) (S:=S₁) (t:=t)
    (hFirst := hW1.right)
    (hHead  := hthead_in_syncUS1)

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
@[simp] lemma result_left_impossible
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) --(ht : t ∈ R)
  {B S₁ : Finset α} (hW1 : isWitness ρ R B S₁ t)  -- violatesFirst を含む
  {k : ℕ} {f : α}
  (U V : Finset α) (hU : U = B ∪ S₁)
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (X Y : Finset α)
  (hX : X = parIter (R.erase t) U k)
  (hY : Y = parIter (R.erase t) V k)
  -- 左枝の仮定（Y\X=∅ & 原因一意）
  (hYXempty : Y \ X = ∅)
  (hExuY : ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f)
  -- この枝での head 同一性
  (hf_head : f = t.head)
  -- |α| 段まで持ち上げるための境界
  (hkBound : k + 1 ≤ Fintype.card α) :
  False := by
  classical
  -- step の一致
  have hStepEq : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
    change stepPar (R.erase t) (parIter (R.erase t) U k)
        = stepPar (R.erase t) (parIter (R.erase t) V k) at hEqNext
    simpa [hX, hY] using hEqNext

  -- 一意原因 rY を取り出す
  obtain ⟨rY, hrY_pack, huniqY⟩ := hExuY
  have hrY_in   : rY ∈ R.erase t := hrY_pack.left
  have hrY_prem : rY.prem ⊆ Y    := (hrY_pack.right).left
  have hrY_head : rY.head = f     := (hrY_pack.right).right

  -- Y 側の差集合から fires への包含（左右版）
  have hXdiff_sub : X \ Y ⊆ fires (R.erase t) Y := by
    -- 既存の左右版を使ってください（あなたの環境名に合わせて差し替え可）
    -- 右版が `diff_subset_fires_right` なら、左右版は `diff_subset_fires_left`
    exact diff_subset_fires_right hStepEq

  -- rY は Y で適用可能：prem⊆Y かつ head∉Y
  have h_head_notinY : rY.head ∉ Y := by

    intro hy

    cases hrY_head
    exact contra_from_head_in_sync_left (ρ:=ρ) (R:=R) (t:=t) (hUC:=hUC)
      (B:=B) (S₁:=S₁) (hW1:=hW1) (k:=k) (U:=U) (V:=V) (hU:=hU)
      (hEqNext:=hEqNext) (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
      (hkBound:=hkBound) (hStepEq:=hStepEq)
      (rY:=rY) (hrY_prem:=hrY_prem) (hy:=hy) (hf_head:=hf_head)

  have hrY_app : rY ∈ applicable (R.erase t) Y :=
    mem_applicable_of_prem_subset_and_head_notin
      (R := R.erase t) (I := Y) (r := rY)
      (hrR := hrY_in) (hprem := hrY_prem) (hnot := h_head_notinY)

  -- fires は applicable.image head なので f ∈ fires (R.erase t) Y
  have hf_in_firesY : f ∈ fires (R.erase t) Y := by
    have : rY.head ∈ fires (R.erase t) Y :=
      mem_fires_of_applicable (hr := hrY_app)
    -- rY.head = f を cases で書き換え
    cases hrY_head
    exact this

  -- 反対側差集合は空：X\Y = ∅
  --have hXdiff_empty : X \ Y = ∅ := by
  --  sorry

  -- f ∈ stepPar (R.erase t) Y
  have hf_in_stepY : f ∈ stepPar (R.erase t) Y :=
    Finset.mem_union.mpr (Or.inr hf_in_firesY)

  -- step 同一で X 側へ
  have hf_in_stepX : f ∈ stepPar (R.erase t) X := by
    have hmem : (f ∈ stepPar (R.erase t) X) = (f ∈ stepPar (R.erase t) Y) :=
      congrArg (fun s => f ∈ s) hStepEq
    exact Eq.mpr hmem hf_in_stepY

  -- parIter の k+1 へ持ち上げ（定義）
  have hf_in_k1_U : f ∈ parIter (R.erase t) U (k+1) := by
    -- X = parIter … U k
    --change f ∈ stepPar (R.erase t) (parIter (R.erase t) U k) at hf_in_stepX
    subst hrY_head hX hY hU
    simp_all only [and_self, applicable, mem_filter, not_false_eq_true, mem_erase, ne_eq, and_true,
      and_imp, fires, mem_image, sdiff_eq_empty_iff_subset]
    obtain ⟨w, h⟩ := hf_in_firesY
    obtain ⟨left_1, right_2⟩ := h
    simp_all only [not_false_eq_true]
    exact hf_in_stepY

  -- k+1 段一致で V 側へ
  have hf_in_k1_V : f ∈ parIter (R.erase t) V (k+1) := by
    have hmem :
      (f ∈ parIter (R.erase t) U (k+1)) =
      (f ∈ parIter (R.erase t) V (k+1)) :=
      congrArg (fun s => f ∈ s) hEqNext
    exact Eq.mp hmem hf_in_k1_U

  -- |α| 段（syncCl）まで上げる
  have hf_in_syncU : f ∈ syncCl (R.erase t) U := by
    have hmono :
      parIter (R.erase t) U (k+1)
        ⊆ parIter (R.erase t) U (Fintype.card α) :=
      parIter_le_of_le (R.erase t) U hkBound
    have : f ∈ parIter (R.erase t) U (Fintype.card α) := hmono hf_in_k1_U
    change f ∈ syncCl (R.erase t) U
    simpa [syncCl] using this

  -- f = t.head へ書き換え、さらに U = B ∪ S₁ へ書き換え
  have : t.head ∈ syncCl (R.erase t) (B ∪ S₁) := by
    -- まず f = t.head
    have hf_mem : t.head ∈ syncCl (R.erase t) U := by
      cases hf_head
      exact hf_in_syncU
    -- 次に U = B ∪ S₁
    have hSyncEq :
      syncCl (R.erase t) U = syncCl (R.erase t) (B ∪ S₁) :=
      congrArg (fun I => syncCl (R.erase t) I) hU
    have hMemEq :
      (t.head ∈ syncCl (R.erase t) U)
        = (t.head ∈ syncCl (R.erase t) (B ∪ S₁)) :=
      congrArg (fun s => t.head ∈ s) hSyncEq
    exact Eq.mp hMemEq hf_mem

  -- violatesFirst（hW1.right）と「消去系閉包に t.head が入る」の矛盾
  exact head_from_Rerase_contra_first
    (ρ:=ρ) (R:=R) (hUC:=hUC) (B:=B) (S:=S₁) (t:=t)
    (hFirst := hW1.right)
    (hHead  := this)

/-後ろに移動。
-- 前提： result_right_impossible, result_left_impossible,
--        exists_k_singleton_symmDiff_of_syncEq, disjoint_union_eq_implies_right_eq などは既証明
--あとで、言明や証明をdiff版に置き換え。OnlyTLastDiff ρ R t
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂
  -- U=V なら disjoint から S₁=S₂
  have finish_eq : U = V → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- UC を erase 側へ
  have hUC' : UniqueChild (α:=α) (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhd
    exact hUC (Finset.mem_of_mem_erase hr₁) (Finset.mem_of_mem_erase hr₂) hhd

  -- 等閉包から：U=V か、∃ k f. (k+1段一致 ∧ 最小差が単点)
  cases exists_k_singleton_symmDiff_of_syncEq (R:=R.erase t) hNTF hNS (U:=U) (V:=V) hEq with
  | inl hUV =>
      exact finish_eq hUV
  | inr hK =>
    rcases hK with ⟨k, f, hk, hEqNext, hSingle⟩
    set X := parIter (R.erase t) U k
    set Y := parIter (R.erase t) V k
    -- (k+1) 段一致を step の形に
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) U k)
          = stepPar (R.erase t) (parIter (R.erase t) V k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差が単点 → どちらかの差が空
    have hXYempty_or_YXempty :
      X \ Y = ∅ ∨ Y \ X = ∅ := by
      -- {f} は片側にしか現れない：NoSwap からの「一方の差が空」補題を使う/導出する
      -- 既存のあなたの系（NoSwap：step同値→左右どちらかの差が空）を使ってください
      -- 例: from hNS and hStep
      exact (hNS X Y hStep)

    -- 2分岐の各々で「不可能」を出す（すでに作った補題を使う）
    cases hXYempty_or_YXempty with
    | inl hXYempty =>
      -- 右枝（X\Y=∅ & 原因一意）での矛盾
      -- 「原因一意」は hSingle と NoTwoFreshHeads & UC' から既に引ける設計で準備している想定。
      -- ここでは、既存の result_right_impossible にそのまま渡す。
      have : False :=
        result_right_impossible
          (ρ:=ρ) (R:=R) (t:=t)
          (hUC:=(UniqueChild_iff_UC R).mp hUC) (ht:=ht)
          (B:=B) (S₁:=S₁) (hW1:=hW1)
          (k:=k) (f:=f)
          (U:=U) (V:=V) (hU:=rfl)
          (hEqNext:=hEqNext)
          (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
          (hXYempty:=by simpa [X,Y] using hXYempty)
          -- 「∃! r …」は、あなたの “一意原因” 補題から hSingle・hStep・hUC' を使って供給
          --(hExu:= sorry)
          --             cause_unique_on_right_of_step_eq (R:=R.erase t) (hUC:=hUC') (hstep:=hStep)
                -- 右側単点化から f∈Y\X を作る
                --(mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f)
                  (by
                    -- X\Y=∅ と対称差単点 hSingle から Y\X={f}
                    -- ここは既にあなたの補題群で出せる形
                    admit
                  )
          (hf_head:=by
            -- result_right_impossible が要求する “f = t.head”
            -- これは head_eq_thead_on_right_branch で供給
            exact head_eq_thead_on_right_branch
              ρ R t ((UniqueChild_iff_UC R).mp hUC) ht
              (B:=B) (S₁:=S₁) (hW1:=hW1)
              (k:=k) (U:=U) (V:=V) (hU:=rfl)
              (hEqNext:=hEqNext) (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
              (hXYempty:=by simpa [X,Y] using hXYempty)
              (hExu:=by
                -- 上と同様に “∃! r …” を供給
                admit))
          (hkBound:=hk)
      exact (this.elim)
    | inr hYXempty =>
      -- 左枝（Y\X=∅ & 原因一意）での矛盾
      have : False :=
        result_left_impossible
          (ρ:=ρ) (R:=R) (t:=t)
          (hUC:=(UniqueChild_iff_UC R).mp hUC)
          (B:=B) (S₁:=S₁) (hW1:=hW1)
          (k:=k) (f:=f)
          (U:=U) (V:=V) (hU:=rfl)
          (hEqNext:=hEqNext)
          (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
          (hYXempty:=by simpa [X,Y] using hYXempty)
          (hExuY:=by
            -- “∃! r …” 左枝版を供給
            admit)
          (hf_head:=by
            -- 左枝版の f=t.head も、左右対称の head_eq_thead_on_left_branch で供給
            exact head_eq_thead_on_left_branch
              ρ R t ((UniqueChild_iff_UC R).mp hUC) ht
              (B:=B) (S₁:=S₁) (hW1:=hW1)
              (k:=k) (U:=U) (V:=V) (hU:=rfl)
              (hEqNext:=hEqNext) (X:=X) (Y:=Y) (hX:=rfl) (hY:=rfl)
              (hYXempty:=by simpa [X,Y] using hYXempty)
              (hExuY:=by admit))
          (hkBound:=hk)
      exact (this.elim)
-/

/-
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂
  have finish_eq : U = V → S₁ = S₂ :=
    fun hUV => disjoint_union_eq_implies_right_eq hD1 hD2 hUV

  -- erase側 UC
  have hUC' : UniqueChild α (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhead
    exact hUC (Finset.mem_of_mem_erase hr₁) (Finset.mem_of_mem_erase hr₂) hhead

  -- 同期閉包等式から「等しい or 最小段の一意原因」へ
  have hCause :=
    lastDiff_unique_cause_of_syncEq_unique
      (R' := R.erase t) hNTF hNS (hUC' := hUC')
      (U := U) (V := V) (hSync := hEq)

  -- 分岐処理
  rcases hCause with hUV | ⟨k, f, hkBound, hEqNext, hUniq⟩
  · exact finish_eq hUV
  ·
    -- k段の状態
    set X : Finset α := parIter (R.erase t) U k
    set Y : Finset α := parIter (R.erase t) V k
    have hX : X = parIter (R.erase t) U k := rfl
    have hY : Y = parIter (R.erase t) V k := rfl

    -- (k+1) 段一致の形に直す
    have hEqNext' :
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) := hEqNext

    -- 右枝 or 左枝
    cases hUniq with
    | inl hR =>
        -- 右枝データ
        have hXYempty : X \ Y = ∅ := hR.left
        have hExu : ∃! r, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f := hR.right
        -- まず f = t.head を右枝用補題で取得
        have hf_head : f = t.head := by
          exact head_eq_thead_on_right_branch
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (B:=B) (S₁:=S₁) (hW1:=hW1)
            (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hXYempty:=hXYempty) (hExu:=hExu)

        -- 右枝は不可能（矛盾）→ U=V の枝のみ残る
        exact (False.elim <|
          result_right_impossible
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (hW1:=hW1) (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hXYempty:=hXYempty) (hExu:=hExu)
            (hf_head:=hf_head) (hkBound:=hkBound))

    | inr hL =>
        -- 左枝データ
        have hYXempty : Y \ X = ∅ := hL.left
        have hExuY : ∃! r, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f := hL.right
        -- 左枝でも f = t.head
        have hf_head : f = t.head :=
          head_eq_thead_on_left_branch
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (B:=B) (S₁:=S₁) (hW1:=hW1)
            (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY) (hYXempty:=hYXempty) (hExuY:=hExuY)

        -- 左枝も不可能（矛盾）
        exact (False.elim <|
          result_left_impossible
            (ρ:=ρ) (R:=R) (t:=t) (hUC:=(UniqueChild_iff_UC _).mp hUC) (ht:=ht)
            (hW1:=hW1) (k:=k) (f:=f) (U:=U) (V:=V) (hU:=rfl)
            (hEqNext:=hEqNext') (X:=X) (Y:=Y) (hX:=hX) (hY:=hY)
            (hYXempty:=hYXempty) (hExuY:=hExuY)
            (hf_head:=hf_head) (hkBound:=hkBound))

-/

/-
/-- **最終定理（(A) 仮定つき完成版）**：
Witness が 2 組 `(B,S₁,t)` と `(B,S₂,t)` を与え，
`R.erase t` の閉包が一致すれば `S₁ = S₂`。 -/
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 等閉包から分岐パッケージ
  have hpack :=
    eq_or_unique_cause_for_erased (R:=R) (t:=t) hNTF hNS (B:=B) (S₁:=S₁) (S₂:=S₂) hEq
  cases hpack with
  | inl hUV =>
      exact disjoint_union_eq_implies_right_eq (B:=B) (S₁:=S₁) (S₂:=S₂) hD1 hD2 hUV
  | inr hK =>
      rcases hK with ⟨k, f, r, hkBound, hEqNext, hside⟩
      -- t.head は両閉包に出現しない
      have hnot1 : t.head ∉ syncCl (R.erase t) (B ∪ S₁) :=
        head_not_in_syncCl_of_erase_witness (R:=R) (ρ:=ρ) (B:=B) (S:=S₁) (t:=t) hUC ht hW1
      have hnot2 : t.head ∉ syncCl (R.erase t) (B ∪ S₂) :=
        head_not_in_syncCl_of_erase_witness (R:=R) (ρ:=ρ) (B:=B) (S:=S₂) (t:=t) hUC ht hW2
      -- 記号短縮
      set X := parIter (R.erase t) (B ∪ S₁) k
      set Y := parIter (R.erase t) (B ∪ S₂) k
      -- 片側単元差 → 対称差の合併は {f}
      have hUnionSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
        cases hside with
        | inl hRight =>
            rcases hRight with ⟨hXemp, hYone, _, _, _⟩

            simp [X, Y, hXemp, hYone]

        | inr hLeft  =>
            rcases hLeft with ⟨hYemp, hXone, _, _, _⟩
            simp [X, Y, hYemp, hXone, union_comm]
      -- (A) により f = t.head
      have hf_head : f = t.head :=
        hA (B:=B) (S₁:=S₁) (S₂:=S₂) (k:=k) (f:=f) hW1 hW2 hEqNext (by simpa [X, Y] using hUnionSingle)
      -- k+1 段で一致しているので、差があった側の k+1 に f は入っている
      have hle_k1_N : k+1 ≤ Fintype.card α := hkBound
      cases hside with
      | inl hRight =>
          -- 右差分のみ：Y\X={f}
          rcases hRight with ⟨hXemp, hYone, _, _, _⟩
          -- f ∈ Y
          have hfY : f ∈ Y := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have : f ∈ Y \ X := by simp [hYone]
            exact (mem_sdiff.mp this).1
          -- f ∈ (k+1) 段（右側）
          have hf_in_k1 : f ∈ parIter (R.erase t) (B ∪ S₂) (k+1) := by
            have : f ∈ stepPar (R.erase t) Y := mem_union.mpr (Or.inl hfY)
            simpa [Y] using this
          -- (k+1) ≤ N から syncCl へ
          have hf_in_sync₂ : f ∈ syncCl (R.erase t) (B ∪ S₂) := by
            have hmono := parIter_le_of_le (R.erase t) (B ∪ S₂) hle_k1_N
            exact hmono hf_in_k1
          -- f = t.head と矛盾
          rename_i right
          subst right
          simp_all only [not_false_eq_true, sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      | inr hLeft  =>
          -- 左差分のみ：X\Y={f}
          rcases hLeft with ⟨hYemp, hXone, _, _, _⟩
          -- f ∈ X
          have hfX : f ∈ X := by
            have : f ∈ ({f} : Finset α) := mem_singleton_self f
            have : f ∈ X \ Y := by simp [hXone]
            exact (mem_sdiff.mp this).1
          -- f ∈ (k+1) 段（左側）
          have hf_in_k1 : f ∈ parIter (R.erase t) (B ∪ S₁) (k+1) := by
            have : f ∈ stepPar (R.erase t) X := mem_union.mpr (Or.inl hfX)
            simpa [X] using this
          -- syncCl へ
          have hf_in_sync₁ : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
            have hmono := parIter_le_of_le (R.erase t) (B ∪ S₁) hle_k1_N
            exact hmono hf_in_k1
          -- f = t.head と矛盾
          let hn := (hnot1 (by simpa [hf_head] using hf_in_sync₁))
          exact False.elim hn

-/

omit [Fintype α] in
private lemma nextHead?_mem_and_min
  {α} [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {a : α}
  (h : nextHead? R I = some a) :
  a ∈ (applicable R I).image (fun t => t.head) ∧
  ∀ b ∈ (applicable R I).image (fun t => t.head), a ≤ b := by
  classical
  unfold nextHead? at h
  set heads := (applicable R I).image (fun t => t.head) with hH
  by_cases hne : heads.Nonempty
  · simp [hH] at h
    constructor
    · by_cases hne : heads.Nonempty
      case pos =>
        rcases h with ⟨happ, hmin⟩
        have hmem_min :
            (image (fun t => t.head)
                  ({t ∈ R | t.prem ⊆ I ∧ t.head ∉ I})).min'
              (Finset.image_nonempty.mpr happ)
              ∈ image (fun t => t.head)
                      ({t ∈ R | t.prem ⊆ I ∧ t.head ∉ I}) :=
          Finset.min'_mem _ _
        -- `a = min' …` を用いて書き換え（`applicable R I = R.filter …` を使うなら `[applicable]` に直しても可）
        have : a ∈ image (fun t => t.head) (applicable R I) := by
          simpa [applicable, hmin] using hmem_min
        -- 最後に `heads = image …` で `heads` 側へ戻す
        simpa [hH] using this

      case neg =>
        (expose_names; exact False.elim (hne hne_1))
    · intro b hb
      simp_all [heads]
      subst h
      obtain ⟨w, h⟩ := hb
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      subst right
      apply min'_le
      simp_all only [applicable, image_nonempty, mem_image, mem_filter, heads]
      use w

  · constructor
    · simp_all only [applicable, image_nonempty, Option.dite_none_right_eq_some, Option.some.injEq, not_nonempty_iff_eq_empty,
        filter_eq_empty_iff, not_and, Decidable.not_not, mem_image, mem_filter, isEmpty_Prop, not_true_eq_false,
        not_false_eq_true, implies_true, IsEmpty.exists_iff, heads]
    · intro b hb
      simp_all only [applicable, image_nonempty, Option.dite_none_right_eq_some, Option.some.injEq, not_nonempty_iff_eq_empty,
        filter_eq_empty_iff, not_and, Decidable.not_not, mem_image, mem_filter, isEmpty_Prop, not_true_eq_false,
        not_false_eq_true, implies_true, IsEmpty.exists_iff, heads]

--使われている。
lemma step2_superset
  {α} [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  I ⊆ step2 R I := by
  intro x hx
  cases h : nextHead? R I with
  | none   => simpa [step2, h] using hx
  | some a =>
      have : x ∈ insert a I := by exact mem_insert_of_mem hx
      simpa [step2, h] using this

def iter2
  {α} [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) : Nat → Finset α
  | 0     => I
  | k+1   => step2 R (iter2 R I k)

lemma iter2_le_of_le
  {α} [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α)
  {m n : ℕ} (hmn : m ≤ n) :
  iter2 R I m ⊆ iter2 R I n := by
  classical
  induction' hmn with n hmn ih
  · simp
  · intro x hx
    have hx' := ih hx
    simpa [iter2] using (step2_superset R (iter2 R I n) hx')

--使われてない。
private lemma step2_adds_minimal_head
  {α} [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {x : α}
  (hx : x ∈ step2 R I \ I) :
  x ∈ (applicable R I).image (fun t => t.head) ∧
  ∀ b ∈ (applicable R I).image (fun t => t.head), x ≤ b := by
  classical
  rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
  cases h : nextHead? R I with
  | none =>
      simp
      constructor
      · dsimp [nextHead?] at h
        simp at h
        rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
        -- step2 の場合分け
        cases hnh : nextHead? R I with
        | none =>
            -- none なら step2 = I なので矛盾
              have hI : x ∈ I := by
                simpa [step2, hnh] using hx_step
              -- 矛盾から任意の命題が従う
              exact False.elim (hx_notI hI)

        | some a =>
            -- x ∈ insert a I なので x = a か x ∈ I
            have hx_ins : x ∈ insert a I := by simpa [step2, hnh] using hx_step
            rcases Finset.mem_insert.mp hx_ins with hx_eq | hx_inI
            · -- x = a の場合：nextHead?_spec_some から規則 t を取る
              subst hx_eq
              rcases nextHead?_spec_some (R:=R) (I:=I) hnh with ⟨ha_notI, ⟨t, htR, htPrem, htHead⟩⟩
              refine ⟨t, ?_, ?_⟩
              · exact ⟨htR, htPrem, by simpa [htHead] using ha_notI⟩
              · -- 目標は t.head = x。今は x を a に置換済みなので t.head = a で十分
                simp [htHead]
            · -- x ∈ I は sdiff と矛盾
              exact (hx_notI hx_inI).elim

      · intro b hb hb2 hb3 hb4 hb5
        dsimp [nextHead?] at h
        simp at h
        subst hb5
        simp_all only [mem_sdiff, not_false_eq_true, and_self, not_true_eq_false]

  | some a =>
      have hx_ins : x ∈ insert a I := by simpa [step2, h] using hx_step
      rcases Finset.mem_insert.mp hx_ins with rfl | hxI
      · exact nextHead?_mem_and_min (R:=R) (I:=I)  h
      · exact (hx_notI hxI).elim

--使われている。
private lemma noRuleWith_thead_in_erase
  {α} [DecidableEq α] {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R) :
  ∀ {r}, r ∈ R.erase t → r.head ≠ t.head := by
  classical
  intro r hr
  have hrR : r ∈ R := Finset.mem_of_mem_erase hr
  intro hEq
  have : r = t := hUC hrR ht hEq
  have : r ∉ R.erase t := by
    subst this
    simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true]
  exact this hr

/-
--使われてない。
lemma head_not_in_iter2_of_erase
  {α} [DecidableEq α] [Fintype α] [LinearOrder α]
  {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  {I₀ : Finset α} (h0 : t.head ∉ I₀) :
  ∀ k, t.head ∉ iter2 (R.erase t) I₀ k := by
  classical
  intro k; induction' k with k ih
  · simpa [iter2] using h0
  · intro hIn
    cases hnh : nextHead? (R.erase t) (iter2 (R.erase t) I₀ k) with
    | none =>
      have : t.head ∈ iter2 (R.erase t) I₀ k := by
        simpa [iter2, step2, hnh] using hIn
      exact ih this

    | some a =>
        have : t.head ∈ insert a (iter2 (R.erase t) I₀ k) := by
          simpa [iter2, step2, hnh] using hIn
        rcases Finset.mem_insert.mp this with hEq | hOld
        · -- `a = t.head` だと、erase側に `t.head` を持つ規則があることになって矛盾
          -- 最小性から `∃ r ∈ R.erase t, r.head = a`
          have hmin := nextHead?_mem_and_min
            (R:=(R.erase t)) (I:=(iter2 (R.erase t) I₀ k)) (a:=a) hnh
          rcases hmin.left with ha_mem
          rcases Finset.mem_image.mp ha_mem with ⟨r, hrApp, rfl⟩
          have hr_inRE : r ∈ R.erase t := (Finset.mem_filter.mp hrApp).1
          exact (noRuleWith_thead_in_erase (R:=R) (t:=t) hUC ht hr_inRE) (by exact id (Eq.symm hEq))
        · exact ih hOld
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma step2_eq_iff_applicable_empty
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  step2 R I = I ↔ applicable R I = ∅ := by
  classical
  constructor
  · intro h
    cases hnh : nextHead? R I with
    | none   =>
      simp
      intro x hx hhx
      dsimp [nextHead?] at hnh
      simp at hnh
      simp_all only

    | some a =>
        -- some の場合は step2 = insert a I なので不動点は無理
        have hii: I = insert a I := by simpa [step2, hnh] using h.symm
        -- 矛盾から空を導く（好みで `nextHead?_spec_none` を使う形にしてOK）
        exact False.elim <| by
          have : a ∈ insert a I := by simp
          have : a ∈ I := by
            rw [←hii] at this
            exact this
          rcases nextHead?_spec_some (R:=R) (I:=I) (a:=a) hnh with ⟨haNot, _⟩
          exact haNot this
  · intro h
    -- applicable 空 ⇒ nextHead? = none ⇒ 据え置き
    have : nextHead? R I = none := by
      unfold nextHead?
      simp
      intro x a a_1
      simp_all only [applicable, filter_eq_empty_iff, not_and, Decidable.not_not]
    simp [step2, this]

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma ssubset_step2_of_applicable_nonempty
  [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α}
  (hne : (applicable R I).Nonempty) :
  I ⊂ step2 R I := by
  classical
  refine ⟨step2_superset R I, ?_⟩
  -- nextHead? = some a, その a は I に入っていないので真に増える
  obtain ⟨a, ha⟩ : ∃ a, nextHead? R I = some a := by
    -- heads 非空から some を取る（applicable 非空 ⇒ heads 非空）
    unfold nextHead?
    have : ((applicable R I).image (fun t => t.head)).Nonempty :=
      Finset.image_nonempty.mpr hne
    simp
    let S : Finset (Rule α) := {t ∈ R | t.prem ⊆ I ∧ t.head ∉ I}

    -- hne : (applicable R I).Nonempty から S.Nonempty を作る
    have happ : S.Nonempty := by
      rcases hne with ⟨r, hr⟩
      -- hr : r ∈ applicable R I
      -- applicable を展開
      change r ∈ R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I) at hr
      -- 目標は r ∈ S だが，S はちょうど同じ filter 記法
      refine ⟨r, ?_⟩
      change r ∈ R.filter (fun t => t.prem ⊆ I ∧ t.head ∉ I)
      exact hr

    -- 画像の非空性
    have himg : (image (fun t => t.head) S).Nonempty :=
      Finset.image_nonempty.mpr happ

    -- a を「その画像の min'」として取る
    refine ⟨(image (fun t => t.head) S).min' himg, ?_, ?_⟩
    · -- Nonempty の証人
      exact happ
    · -- min' の定義通り
      rfl

  rcases nextHead?_spec_some (R:=R) (I:=I) (a:=a) ha with ⟨ha_notI, -⟩
  intro hEq
  have : a ∈ I := by
    have : a ∈ step2 R I := by
      simp [step2, ha]
    exact hEq this


  exact ha_notI this

/-
--以下は成り立たない。反例あり。
lemma iter2_mono_in_I
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (k : ℕ) :
  Monotone (fun I => iter2 R I k) := by
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma applicable_lift_of_head_notin
  [DecidableEq α]
  {R : Finset (Rule α)} {I J : Finset α}
  (hIJ : I ⊆ J) {t : Rule α}
  (ht : t ∈ applicable R I) (hnotJ : t.head ∉ J) :
  t ∈ applicable R J := by
  rcases Finset.mem_filter.mp ht with ⟨hR, ⟨hprem, _⟩⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨hR, ⟨?premJ, hnotJ⟩⟩
  intro x hx
  exact hIJ (hprem hx)

/- なりたたない。けしてよい。
lemma applicable_mono
  [DecidableEq α] {R : Finset (Rule α)} {I J : Finset α}
  (hIJ : I ⊆ J) : applicable R I ⊆ applicable R J := by
  intro t ht; rcases Finset.mem_filter.mp ht with ⟨hR, hcond⟩
  rcases hcond with ⟨hprem, hnot⟩
  refine Finset.mem_filter.mpr ?_
  exact ⟨hR, ⟨by exact fun x hx => hIJ (hprem hx), by
    -- `t.head ∉ I` から `t.head ∉ J` を言う必要はない（「適用可能」は `head ∉ I` 条件なので
    -- J 側では「もっと入っている」ため `head ∉ J` は generally false。ここは `applicable` の定義次第。
    -- もし J 側の適用条件が `head ∉ J` を要求するなら、この補題は「⊆」ではなく別の使い方になります。
    dsimp [applicable] at ht
    simp at ht

    admit⟩⟩
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma enter_at_iter2_exists_rule
  [DecidableEq α] [LinearOrder α]
  {R : Finset (Rule α)} {I : Finset α} {x : α}
  (hx : x ∈ step2 R I \ I) :
  ∃ r ∈ R, r.prem ⊆ I ∧ r.head = x := by
  classical
  -- step2 で some a を入れて x=a、`nextHead?_spec_some` を使う
  rcases Finset.mem_sdiff.mp hx with ⟨hx_step, hx_notI⟩
  cases h : nextHead? R I with
  | none =>
    have hI : x ∈ I := by

      -- step2 を展開（match を hnh で解消）
      simp [step2] at hx_step
      simp_all only [mem_sdiff, not_false_eq_true, and_true]
    exact False.elim (hx_notI hI)

  | some a =>
      have hx_ins : x ∈ insert a I := by simpa [step2, h] using hx_step
      rcases Finset.mem_insert.mp hx_ins with hx_eq | hx_inI
      · subst hx_eq
        rcases nextHead?_spec_some (R:=R) (I:=I) h with ⟨_, ⟨r, hrR, hrPrem, hrHead⟩⟩
        exact ⟨r, hrR, hrPrem, by exact hrHead⟩
      · exact (hx_notI hx_inI).elim

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma frozen_forever_of_none
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) {S : Finset α}
  (h : nextHead? R S = none) :
  ∀ m, (Nat.iterate (step2 R) m) S = S := by
  intro m; induction m with
  | zero => rfl
  | succ m ih =>
      -- step2 S = S, かつ以降も S に留まる
      have : step2 R S = S := by simp [step2, h]
      simp [Nat.iterate, ih, this]

omit [DecidableEq α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma all_steps_increase_if_last_increases
  [DecidableEq α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) (N : ℕ)
  (hneq : iter2 R I N ≠ iter2 R I (N+1)) :
  ∀ k ≤ N, iter2 R I k ≠ iter2 R I (k+1) := by
  classical
  intro k hk
  by_contra heq
  -- k 段で据え置きなら nextHead? = none
  have hnone : nextHead? R (iter2 R I k) = none := by
    -- `heq` を `step2` の定義に戻して評価すると `none` が出る
    -- （`some` なら insert で絶対に変わるため）
    cases hnh : nextHead? R (iter2 R I k) with
    | none   => rfl
    | some a =>
      simp
      set S := iter2 R I k

      -- (k+1)段は step2
      have hstep : iter2 R I (k+1) = step2 R S := by
        -- S = iter2 R I k を使って定義展開
        change iter2 R I (k+1) = step2 R (iter2 R I k)
        simp [iter2]

      -- heq：S = iter2 R I (k+1) なので、step2 R S = S が従う
      have hfix : step2 R S = S := by
        have : S = iter2 R I (k+1) := by
          -- S の定義で置換
          change iter2 R I k = iter2 R I (k+1) at heq
          exact heq
        -- S = (k+1)段 = step2 R S
        have : S = step2 R S := this.trans hstep
        exact this.symm

      -- nextHead? = some a なら step2 は insert a
      have hsomeS : nextHead? R S = some a := by
        -- S の定義で置換
        change nextHead? R (iter2 R I k) = some a at hnh
        exact hnh
      have hstep_some : step2 R S = insert a S := by
        simp [step2, hsomeS]

      -- 以上より insert a S = S
      have hins_eq : insert a S = S := by
        -- hfix : step2 R S = S と hstep_some を合成
        apply Eq.trans
        exact id (Eq.symm hstep_some)--hstep_some hfix
        exact hfix

      -- すると a ∈ S が出る（mem を等式で運ぶ）
      have ha_in_S : a ∈ S := by
        -- まず a ∈ insert a S
        have ha_ins : a ∈ insert a S := Finset.mem_insert_self a S
        -- (a ∈ insert a S) = (a ∈ S) に書き換え
        have hmem_eq : (a ∈ insert a S) = (a ∈ S) :=
          congrArg (fun s => a ∈ s) hins_eq
        exact Eq.mp hmem_eq ha_ins

      -- しかし spec_some から a ∉ S なので矛盾
      have ha_notin : a ∉ S := by
        rcases nextHead?_spec_some (R:=R) (I:=S) (a:=a) hsomeS with ⟨ha_not, _⟩
        exact ha_not
      exact ha_notin ha_in_S

  -- 据え置き以降は永遠に据え置き → 特に N+1 段も等しい
  set S := iter2 R I k with hS
  have step_S : step2 R S = S := by
    -- hnone から直ちに step2 R S = S
    have : nextHead? R S = none := by
      -- hnone を S に書き換え
      have : nextHead? R (iter2 R I k) = none := hnone
      simpa [hS] using this
    -- step2 の定義
    simp [step2, this]

  -- d による帰納で iter2 (k + d) = S
  have frozen_from_k : ∀ d : ℕ, iter2 R I (k + d) = S := by
    intro d
    induction' d with d ih
    · -- d = 0
      -- iter2 R I (k+0) = iter2 R I k = S
      exact hS.symm
    · -- d+1
      -- iter2 (k+d+1) = step2 R (iter2 (k+d)) = step2 R S = S
      have h1 : iter2 R I (k + d + 1) = step2 R (iter2 R I (k + d)) := by
        -- iter2 の定義（k+d+1 段は 1 ステップ）
        -- 注意: + の結合の整形が必要
        have : k + d + 1 = (k + d) + 1 := by exact rfl
        -- 上の等式で simp
        simp [iter2]
      calc
        iter2 R I (k + d + 1)
            = step2 R (iter2 R I (k + d)) := h1
        _   = step2 R S := by
                -- 直前の帰納仮定 ih : iter2 R I (k + d) = S
                -- これを使って書き換え
                -- `congrArg` で step2 の引数に等式を適用
                have := congrArg (fun s => step2 R s) ih
                exact this
        _   = S := step_S

  -- N = k + d に分解して、N と N+1 の両方が S に等しいことを示す
  rcases Nat.exists_eq_add_of_le hk with ⟨d, rfl⟩
  -- これで (k+d) 段と (k+d+1) 段の等号が出る
  have hN  : iter2 R I (k + d)     = S := frozen_from_k d
  have hN1 : iter2 R I (k + d + 1) = S := frozen_from_k (d+1)
  -- したがって等しい
  have hEqFinal :
      iter2 R I (k + d) = iter2 R I (k + d + 1) := by
    -- 2つの等式を合成
    apply hN.trans hN1.symm

  -- ところで N = k+d ≤ N なので、特に N= k+d。今の等式は N と N+1 の等式に他ならない。
  -- これは hneq に反する（N は仮定の N）
  -- 形式的には、k+d = N の置換は上で済んでいる（`rcases` で rfl を入れている）。
  exact hneq hEqFinal

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
@[simp] lemma onlyTLastDiff_core_case_split
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) (R : Finset (Rule α)) (t : Rule α)
  (hUC : UC R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t)) (hNS : NoSwap (R.erase t))
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t)-- (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂))
  -- 枝ごとの等式化（既存のあなたの補題を渡す）
  (head_eq_right :
    ∀ {k f}
      (hEqNext :
        parIter (R.erase t) (B ∪ S₁) (k+1)
          = parIter (R.erase t) (B ∪ S₂) (k+1))
      (hXYempty :
        parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k = ∅)
      (hExu :
        ∃! r : Rule α,
          r ∈ R.erase t
          ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₁) k
          ∧ r.head = f), f = t.head)
  (head_eq_left :
    ∀ {k f}
      (hEqNext :
        parIter (R.erase t) (B ∪ S₁) (k+1)
          = parIter (R.erase t) (B ∪ S₂) (k+1))
      (hYXempty :
        parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = ∅)
      (hExuY :
        ∃! r : Rule α,
          r ∈ R.erase t
          ∧ r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k
          ∧ r.head = f), f = t.head)
  -- NoSwap からの決定版（あなたの環境の既存補題名で差し替えてOK）
  (noSwap_step_forces_empty :
    ∀ {X Y}, stepPar (R.erase t) X = stepPar (R.erase t) Y →
      X \ Y = ∅ ∨ Y \ X = ∅)
  : S₁ = S₂ := by
  classical
  -- U=V → S₁=S₂
  have finish_eq :
      (B ∪ S₁) = (B ∪ S₂) → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- 強い版：k,f
  obtain hUV | ⟨k, f, hk, hEqNext, hSingle⟩ :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R' := R.erase t) hNTF hNS
      (U := B ∪ S₁) (V := B ∪ S₂) hEq
  · exact finish_eq hUV
  ·
    set X := parIter (R.erase t) (B ∪ S₁) k
    set Y := parIter (R.erase t) (B ∪ S₂) k
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₁) k)
          = stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₂) k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差 = {f} の3分岐
    have hcases :=
      union_singleton_cases
        (X := X \ Y) (Y := Y \ X) (f := f)
        (h := hSingle)

    -- UC (erase) を一度用意（原因一意補題で使う場合があるなら）
    have hUC_erase : UC (R.erase t) := by
      intro a
      -- ((R.erase t).filter …) ⊆ (R.filter …)
      have hsubset :
          ((R.erase t).filter (fun r : Rule α => r.head = a))
            ⊆ (R.filter (fun r : Rule α => r.head = a)) := by
        intro r hr
        -- r ∈ (erase t).filter ↔ r ∈ erase t ∧ r.head = a
        -- r ∈ erase t → r ∈ R
        rcases Finset.mem_filter.mp hr with ⟨hr_erase, hhead⟩
        rcases Finset.mem_erase.mp hr_erase with ⟨_, hrR⟩
        exact Finset.mem_filter.mpr ⟨hrR, hhead⟩
      -- card_monotone + UC R
      apply le_trans
      exact Nat.le_refl #({t ∈ R.erase t | t.head = a})
      have hcard_le :
        #({r ∈ R.erase t | r.head = a})
          ≤ #({r ∈ R | r.head = a}) := by exact card_le_card hsubset

      have hcard_R_le_one :
        #({r ∈ R | r.head = a}) ≤ 1 :=
        hUC a

      exact le_trans hcard_le hcard_R_le_one

    have hUCh' : UniqueChild α (R.erase t) :=
      (UniqueChild_iff_UC (R.erase t)).mpr hUC_erase

    cases hcases with
    | inl hR =>
      rcases hR with ⟨hXempty, hYsingle⟩
      -- f ∈ Y \ X
      have hfY : f ∈ Y ∧ f ∉ X :=
        mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f) hYsingle
      -- 原因一意（左側版：hg : f ∈ Y\X）
      have hExu :
        ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f :=
        cause_unique_on_left_of_step_eq
          (R := R.erase t) (hUC := hUCh')
          (hstep := hStep)
          (hg := by exact Finset.mem_sdiff.mpr ⟨hfY.left, hfY.right⟩)

      have hXYempty: X \ Y = ∅ := by
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      -- f = t.head（右枝用の外部補題）
      have hf_head : f = t.head :=
        head_eq_right (hEqNext := hEqNext) (hXYempty := hXYempty) (hExu := hExu)


      -- 右枝は不可能
      have contra :=
        (result_right_impossible ρ R t
          (hUC := hUC) (ht := ht)
          (hW1 := hW1)
          (B := B) (S₁ := S₁)
          (k := k) (f := f)
          (U := B ∪ S₁) (V := B ∪ S₂)
          (hU := rfl)
          (hEqNext := hEqNext)
          (X := X) (Y := Y)
          (hX := rfl) (hY := rfl)
          (hXYempty := hXYempty)
          (hExu := hExu)
          (hf_head := hf_head)
          (hkBound := hk))


      exact contra.elim

    | inr hrest =>
      cases hrest with
      | inl hL =>
        rcases hL with ⟨hXsingle, hYempty⟩
        -- f ∈ X \ Y
        have hfX : f ∈ X ∧ f ∉ Y :=
          -- X\Y = {f} から f∈X∧f∉Y を得るには、補題を左右反転で使えばよい
          by
            -- 「{f} = X\Y」は「Y\X = {f}」に置き換えづらいので、
            -- 直接この用途の補題を持っているならそれを使ってOK。
            -- 今回は「左右反転して使う」ために対称形に書き直す：
            have := mem_and_not_mem_of_sdiff_singleton_right
              (X:=Y) (Y:=X) (f:=f) hXsingle

            -- ただし上の rfl はダミーなので、素直に作る：
            exact
            ⟨ by
                -- f ∈ X
                have : f ∈ X \ Y := by
                  -- hXsingle : X\Y = {f}
                  have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  exact by
                    -- 置換
                    have := congrArg (fun (s : Finset α) => f ∈ s) hXsingle
                    (expose_names; exact mem_sdiff.mpr this_1)
                exact (Finset.mem_sdiff.mp this).left
              , by
                -- f ∉ Y
                have : f ∈ X \ Y := by
                  have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  have := congrArg (fun (s : Finset α) => f ∈ s) hXsingle
                  (expose_names; exact mem_sdiff.mpr this_1)
                exact (Finset.mem_sdiff.mp this).right ⟩

        -- 原因一意（右側版：hf : f ∈ X\Y）
        have hExuY :
          ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f :=
          cause_unique_on_right_of_step_eq
            (R := R.erase t) (hUC := hUCh')
            (hstep := hStep)
            (hf := by exact Finset.mem_sdiff.mpr ⟨hfX.left, hfX.right⟩)

        -- f = t.head（左枝用の外部補題）
        have hYXempty: Y \ X = ∅ := by
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

        have hf_head : f = t.head :=
          head_eq_left (hEqNext := hEqNext) (hYXempty := hYXempty) (hExuY := hExuY)

        -- 左枝は不可能
        have contra :=
          result_left_impossible ρ R t
            (hUC := hUC)
            (B := B) (S₁ := S₁) (hW1 := hW1)
            (k := k) (f := f)
            (U := B ∪ S₁) (V := B ∪ S₂) (hU := rfl)
            (hEqNext := hEqNext)
            (X := X) (Y := Y) (hX := rfl) (hY := rfl)
            (hYXempty := hYXempty) (hExuY := hExuY)
            (hf_head := hf_head) (hkBound := hk)
        exact contra.elim

      | inr hdup =>
        -- 両側 {f} は NoSwap + step 一致に反する
        have : X \ Y = ∅ ∨ Y \ X = ∅ := noSwap_step_forces_empty (X:=X) (Y:=Y) hStep
        -- しかし hdup は (X={f} ∧ Y={f}) 型（union_singleton_cases の第3枝）なので空でない
        -- → 矛盾
        -- 形式上は「{f} = ∅」は成り立たないので OK
        cases this with
        | inl hxe =>
          have : ({f} : Finset α) = (∅ : Finset α) := by
            -- hdup から X\Y = {f}
            have hx : X \ Y = ({f} : Finset α) := by
              simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, union_idempotent, X, Y]
            exact Eq.trans hx.symm hxe
          exact (by
            -- {f} ≠ ∅
            have : (¬ ({f} : Finset α) = ∅) := by
              exact Finset.singleton_ne_empty f
            exact (this ‹{f} = ∅›).elim)
        | inr hye =>
          have : ({f} : Finset α) = (∅ : Finset α) := by
            -- hdup から Y\X = {f}
            have hy : Y \ X = ({f} : Finset α) := by
              simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, union_idempotent, X, Y]
            exact Eq.trans hy.symm hye
          exact (by
            have : (¬ ({f} : Finset α) = ∅) := by
              exact Finset.singleton_ne_empty f
            exact (this ‹{f} = ∅›).elim)

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma sdiff_union_singleton_cases
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (h : (X \ Y) ∪ (Y \ X) = ({f} : Finset α)) :
  (X \ Y = ∅ ∧ Y \ X = {f})
  ∨ (X \ Y = {f} ∧ Y \ X = ∅)
  ∨ (X \ Y = {f} ∧ Y \ X = {f}) := by
  classical
  -- まず両者が {f} に包含されることを示す
  have hXY_sub : X \ Y ⊆ ({f} : Finset α) := by
    intro x hx
    -- x ∈ X\Y ⊆ (X\Y) ∪ (Y\X) = {f}
    have : x ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inl hx)
    have : x ∈ ({f} : Finset α) := by simpa [h] using this
    exact this
  have hYX_sub : Y \ X ⊆ ({f} : Finset α) := by
    intro y hy
    have : y ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inr hy)
    have : y ∈ ({f} : Finset α) := by simpa [h] using this
    exact this

  -- 場合分け：どちらかが空か、両方非空か
  by_cases hXYempty : X \ Y = ∅
  · -- X\Y = ∅ なら、(X\Y) ∪ (Y\X) = {f} から Y\X = {f}
    left
    have : Y \ X = ({f} : Finset α) := by
      -- ∅ ∪ (Y\X) = {f}
      have : (X \ Y) ∪ (Y \ X) = Y \ X := by simp [hXYempty, Finset.empty_union]
      exact sdiff_singleton_right_of_symmdiff_singleton_left_empty hXYempty h
    exact ⟨hXYempty, this⟩
  · by_cases hYXempty : Y \ X = ∅
    · -- Y\X = ∅ の場合は対称
      right; left
      have : X \ Y = ({f} : Finset α) := by
        have : (X \ Y) ∪ (Y \ X) = X \ Y := by simp [hYXempty, Finset.union_empty]
        simp_all only [union_empty, subset_refl, subset_singleton_iff, true_or, singleton_ne_empty, not_false_eq_true,
           sdiff_eq_empty_iff_subset, singleton_union]
      exact ⟨this, hYXempty⟩
    · -- 両方非空の場合：どちらも {f} に等しい
      right; right
      have hne1 : (X \ Y).Nonempty := Finset.nonempty_iff_ne_empty.mpr hXYempty
      have hne2 : (Y \ X).Nonempty := Finset.nonempty_iff_ne_empty.mpr hYXempty
      -- 非空 & ⊆ {f} から X\Y = {f}
      have h1 : X \ Y = ({f} : Finset α) := by
        apply Finset.Subset.antisymm_iff.mpr
        constructor
        · exact hXY_sub
        · -- {f} ⊆ X\Y：非空元を取り、その元が f と一致することを使う
          intro z hz
          have hz_eq : z = f := Finset.mem_singleton.mp hz
          rcases hne1 with ⟨x, hx⟩
          have : x = f := by
            have : x ∈ ({f} : Finset α) := hXY_sub hx
            exact Finset.mem_singleton.mp this
          simpa [hz_eq, this] using hx
      -- 同様に Y\X = {f}
      have h2 : Y \ X = ({f} : Finset α) := by
        apply Finset.Subset.antisymm_iff.mpr
        constructor
        · exact hYX_sub
        · intro z hz
          have hz_eq : z = f := Finset.mem_singleton.mp hz
          rcases hne2 with ⟨y, hy⟩
          have : y = f := by
            have : y ∈ ({f} : Finset α) := hYX_sub hy
            exact Finset.mem_singleton.mp this
          simpa [hz_eq, this] using hy
      exact ⟨h1, h2⟩

/-
lemma OnlyTLastDiff.head_eq_right_subset
  (hA : OnlyTLastDiff ρ R t)
  {U V : Finset α} {k : ℕ} {f : α}
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (hsubset :
    parIter (R.erase t) U k ⊆ parIter (R.erase t) V k)
  (hExu :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) U k ∧
      r.head = f) :
  f = t.head :=
  sorry
-/

/-
lemma head_eq_right_from_A
  (hA : OnlyTLastDiff ρ R t)
  {U V : Finset α} {k : ℕ} {f : α}
  (hEqNext :
    parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1))
  (hXYempty :
    parIter (R.erase t) U k \ parIter (R.erase t) V k = ∅)
  (hExu :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) U k ∧
      r.head = f) :
  f = t.head :=
by
  -- sdiff=∅ → ⊆ （`sdiff_eq_empty_iff_subset` を ←向きに使う）
  have hsubset :
    parIter (R.erase t) U k ⊆ parIter (R.erase t) V k :=
  by
    -- `Finset.sdiff_eq_empty_iff_subset` の「→」向きを明示的に使う
    exact (Finset.sdiff_eq_empty_iff_subset).1 hXYempty
  exact OnlyTLastDiff.head_eq_right_subset hA hEqNext hsubset hExu
-/

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma OnlyTLastDiff.head_eq_of_symmDiff_singleton
  [DecidableEq α] [Fintype α] [LinearOrder α]
  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α}
  (hA : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α} {k : ℕ} {f : α}
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEqNext :
    parIter (R.erase t) (B ∪ S₁) (k+1)
      = parIter (R.erase t) (B ∪ S₂) (k+1))
  (hSingle :
    (parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k) ∪
    (parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k)
      = ({f} : Finset α)) :
  f = t.head := by
  -- `OnlyTLastDiff` はまさにこの4引数を取る形なので、そのまま適用で終わり
  exact hA (B:=B) (S₁:=S₁) (S₂:=S₂) (k:=k) (f:=f) hW1 hW2 hEqNext hSingle

omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma left_branch_Xdiff_singleton_of_symmDiff
  [DecidableEq α]
  {X Y : Finset α} {f : α}
  (hSingle : (X \ Y) ∪ (Y \ X) = ({f} : Finset α))
  (hYXempty : Y \ X = ∅) :
  X \ Y = ({f} : Finset α) := by
  -- 片方が空なので対称差＝左差分。等式を書き換えるだけ。
  -- 以降は ext/包含で閉じるだけです（お手元の補題で短くしてOK）
  -- left ⊆ right
  have hsubset : X \ Y ⊆ ({f} : Finset α) := by
    intro x hx
    have : x ∈ (X \ Y) ∪ (Y \ X) := Finset.mem_union.mpr (Or.inl hx)
    -- hSingle で右へ移す
    -- `mem_singleton.mp` で x=f と取り、`mem_singleton.mpr` で戻す
    have hx_single : x ∈ ({f} : Finset α) := by
      -- 置換： (X\Y) ∪ (Y\X) = {f}
      -- `rw [hSingle]` を避けるなら `congrArg (fun s => x ∈ s) hSingle` を使う
      have := congrArg (fun s => x ∈ s) hSingle
      -- now cast
      apply Eq.mp this
      (expose_names; exact this_1)
    exact hx_single
  -- right ⊆ left
  have hsuperset : ({f} : Finset α) ⊆ X \ Y := by
    intro x hx
    have hx_eq : x = f := Finset.mem_singleton.mp hx
    -- 対称差が {f} で Y\X=∅ だから f ∈ X\Y
    -- お手元の `mem_and_not_mem_of_sdiff_singleton_right` を使うと速い：
    -- 適用のために {f} = X\Y を先に主張する流れでも良いです。
    -- ここは簡潔化のため略。実装では ext で両包含を出してもOK。
    have hunion : (X \ Y) ∪ (Y \ X) = X \ Y := by
  -- rewrite the right union operand using hYXempty, then use union with empty
      have := congrArg (fun s => (X \ Y) ∪ s) hYXempty
      -- this : (X \ Y) ∪ (Y \ X) = (X \ Y) ∪ ∅
      exact Eq.trans this (Finset.union_empty _)

    -- From the two equalities, derive X \ Y = {f}.
    have hXYeq : X \ Y = ({f} : Finset α) :=
      Eq.trans hunion.symm hSingle

    -- Now rewrite membership using hXYeq.
    have : x ∈ X \ Y := by
      -- (x ∈ {f}) = (x ∈ X \ Y)
      have hmem := congrArg (fun s => x ∈ s) hXYeq.symm
      exact Eq.mp hmem hx

    exact this
  apply Finset.Subset.antisymm_iff.mpr
  exact ⟨hsubset, hsuperset⟩


lemma OnlyTLastDiff.head_eq_left_sdiff
  [DecidableEq α] [Fintype α] [LinearOrder α]
  {ρ : RuleOrder α} {R : Finset (Rule α)} {t : Rule α}
  (hA : OnlyTLastDiff ρ R t)
  {B S₁ S₂ : Finset α} {k : ℕ} {f : α}
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hNTF : NoTwoFreshHeads (R.erase t)) (hNS : NoSwap (R.erase t))
  (hUC' : UniqueChild α (R.erase t))
  (hEqNext :
    parIter (R.erase t) (B ∪ S₁) (k+1)
      = parIter (R.erase t) (B ∪ S₂) (k+1))
  (hYXempty :
    parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k = ∅)
  (hExuY :
    ∃! r : Rule α,
      r ∈ R.erase t ∧
      r.prem ⊆ parIter (R.erase t) (B ∪ S₂) k ∧
      r.head = f) :
  f = t.head := by
  -- 記号
  set X := parIter (R.erase t) (B ∪ S₁) k
  set Y := parIter (R.erase t) (B ∪ S₂) k

  -- 次段一致を step 形へ
  have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
    change stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₁) k)
       = stepPar (R.erase t) (parIter (R.erase t) (B ∪ S₂) k) at hEqNext
    simpa [X, Y] using hEqNext

  -- 左枝の標準手順：
  -- 1) hStep から (X \ Y) ⊆ fires (R.erase t) Y
  have hXdiff_sub : X \ Y ⊆ fires (R.erase t) Y := by
    -- あなたの環境の「左枝版」補題名に置き換えてください
    -- 例: diff_subset_fires_left hStep
    apply diff_subset_fires_left
    exact id (Eq.symm hEqNext)

  -- 2) hExuY より f ∈ fires (R.erase t) Y
  have hf_in_firesY : f ∈ fires (R.erase t) Y := by
    obtain ⟨r, hr_pack, huniq⟩ := hExuY
    have hr_in : r ∈ R.erase t := hr_pack.left
    have hr_prem : r.prem ⊆ Y := (hr_pack.right).left
    have hr_head : r.head = f := (hr_pack.right).right
    -- applicable
    have hr_app :
        r ∈ applicable (R.erase t) Y :=
      mem_applicable_of_prem_subset_and_head_notin
        (hrR := hr_in) (hprem := hr_prem)
        (hnot := by
          -- 「head ∉ Y」は applicable の要件。ここは一行で済むよう
          -- 既にあなたの環境にある head∉Y の導出を差し替えてください。
          -- 例えば、”入るのが step の『新規』だから Y には入っていない”の事実を
          -- 直前の最小段構成から引き出す、等。
          -- ここでは簡潔に placeholder：
          sorry)
          --exact head_not_in_Y_from_minimality hEqNext hYXempty hExuY

    have : r.head ∈ fires (R.erase t) Y :=
      mem_fires_of_applicable hr_app
    -- r.head = f に置換
    cases hr_head
    exact this

  -- 3) NoTwoFreshHeads → #(fires (R.erase t) Y) ≤ 1
  have hF_card_le : (fires (R.erase t) Y).card ≤ 1 := hNTF Y

  -- 4) 「任意 x ∈ X\Y は fires Y に入る」かつ「f も fires Y に入る」かつ「card ≤ 1」
  --    ⇒ x=f。よって X\Y ⊆ {f}。加えて Y\X=∅ だから対称差は {f}。
  have hSingle :
      (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
    -- まず X\Y ⊆ {f}
    have hXdiff_sub_singleton : X \ Y ⊆ ({f} : Finset α) := by
      intro x hx
      have hxF : x ∈ fires (R.erase t) Y := hXdiff_sub hx
      have : x = f :=
        eq_of_two_mem_of_card_le_one
          (ha := hxF) (hb := hf_in_firesY) (hcard := hF_card_le)
      exact Finset.mem_singleton.mpr this
    -- つぎに Y\X=∅
    have hYXempty' : Y \ X = ∅ := by
      -- 与件 hYXempty を X,Y に合わせて使うだけ
      simpa [X, Y] using hYXempty
    -- 対称差は (X\Y) ∪ ∅ = X\Y なので {f}
    -- 等式で出す：
    have : (X \ Y) ∪ (Y \ X) = X \ Y := by
      -- ∪ の右を ∅ にする
      -- Finset.union_eq_left.2 (by exact Finset.empty_subset _)
      -- を避けるなら ext でもOK
      apply Finset.Subset.antisymm_iff.mpr
      constructor
      · intro z hz; exact by
          cases Finset.mem_union.mp hz with
          | inl hzx => exact hzx
          | inr hzy =>
              have : False := by
                have : z ∈ (Y \ X) := hzy
                -- Y\X=∅
                have : z ∈ (∅ : Finset α) := by
                  simp
                  rw [hYXempty'] at this
                  simp_all only [mem_erase, ne_eq, sdiff_eq_empty_iff_subset, fires, applicable, mem_image, mem_filter,
                      subset_singleton_iff, mem_union, mem_sdiff, notMem_empty, Y, X]
                exact False.elim (by cases this)
              exact False.elim this
      · intro z hz; exact Finset.mem_union.mpr (Or.inl hz)
    -- まとめ
    -- (X\Y) ⊆ {f} かつ (X\Y) ∪ (Y\X) = (X\Y) ⇒ 対称差 ⊆ {f}
    -- さらに Nonempty は “原因一意”から確保できる（f が実際に現れる）
    -- ここでは等号の主張として {f} を出します
    -- ext で両包含でもOKですが、簡潔に：
    -- 左⊆右
    have hsub : (X \ Y) ∪ (Y \ X) ⊆ ({f} : Finset α) := by
      intro z hz
      cases Finset.mem_union.mp hz with
      | inl hzX => exact hXdiff_sub_singleton hzX
      | inr hzY =>
          -- hzY は Y\X=∅ なので到達しない
          have : z ∈ (∅ : Finset α) := by
            rw [hYXempty'] at hzY
            exact hzY
          exact False.elim (by cases this)
    -- 右⊆左（{f} ⊆ 対称差）は、原因一意から f∈X\Y を作れば出ます
    -- f ∈ X\Y を作るには：hExuY と step 同一から f が次段で“新しく”現れることを示す標準手順を使ってください
    -- ここは長くなるので、あなたの既存補題（mem_and_not_mem_of_sdiff_singleton_right等）を流用してください。
    -- 以降は、その補題経由で {f} ⊆ X\Y を得た体で閉じます：
    have hsup : ({f} : Finset α) ⊆ (X \ Y) ∪ (Y \ X) := by
      intro z hz
      have hz_eq : z = f := Finset.mem_singleton.mp hz
      -- f ∈ X\Y を主張（=左枝）：ここは既存の「最小段で f が右側から供給される」系で作れます
      -- 直接書くなら：
      have hf_in_XdiffY : f ∈ X \ Y := by
        -- 右から左へ追いつく状況なので、詳細は省略（あなたの既存補題に差し替え）
        sorry
        --exact f_mem_XdiffY_from_left_branch hStep hYXempty hExuY
      -- すると対称差にも入る
      exact Finset.mem_union.mpr (Or.inl (by simpa [hz_eq] using hf_in_XdiffY))
    exact Finset.Subset.antisymm_iff.mpr ⟨hsub, hsup⟩

  -- 最後：1) の薄いラッパで `OnlyTLastDiff` を適用
  exact
    OnlyTLastDiff.head_eq_of_symmDiff_singleton
      (hA := hA) (hW1 := hW1) (hW2 := hW2)
      (hEqNext := hEqNext)
      (hSingle := by
        -- X,Y で作った hSingle を B,S の形に戻すだけ
        simpa [X, Y])

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)     -- ★ 復活させた仮定
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ :=
by
  classical
  -- 記号
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂

  -- U=V → S₁=S₂
  have finish_eq : U = V → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- UC を erase 側へ（必要なら）
  have hUC' : UniqueChild (α:=α) (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhd
    have hr₁R : r₁ ∈ R := (Finset.mem_erase.mp hr₁).2
    have hr₂R : r₂ ∈ R := (Finset.mem_erase.mp hr₂).2
    exact hUC hr₁R hr₂R hhd

  -- 「等閉包⇒（U=V）or（最小段 k と f があり，(k+1)段一致 & 対称差＝単点）」を取得
  have hSplit :=
    exists_k_singleton_symmDiff_of_syncEq
      (R := R.erase t) hNTF hNS (U := U) (V := V) hEq

  -- 場合分け
  cases hSplit with
  | inl hUV =>
      exact finish_eq hUV
  | inr hdata =>
      rcases hdata with ⟨k, f, hkBound, hEqNext, hSingle⟩

      -- 記号：前段の集合
      set X : Finset α := parIter (R.erase t) U k
      set Y : Finset α := parIter (R.erase t) V k

      -- (k+1) 段一致を step 形に
      have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
        -- parIter … (k+1) = stepPar … (parIter … k)
        change
          stepPar (R.erase t) (parIter (R.erase t) U k)
            = stepPar (R.erase t) (parIter (R.erase t) V k)
          at hEqNext
        simp_all only [U, V, X, Y]

      ------------------------------------------------------------------
      -- まず OnlyTLastDiff を“そのまま”適用して f = t.head を取る
      ------------------------------------------------------------------
      have hf_head : f = t.head := by
        -- hA : OnlyTLastDiff ρ R t
        --   (isWitness ρ R B S₁ t) (isWitness ρ R B S₂ t)
        --   parIter (k+1) 等式
        --   ((X\Y) ∪ (Y\X) = {f}) から f = t.head
        have hEqNext' :
          parIter (R.erase t) (B ∪ S₁) (k+1)
            = parIter (R.erase t) (B ∪ S₂) (k+1) := by
          -- U,V の定義に戻して一致
          simp_all only [U, V, X, Y]

        have hSingle' :
          ((parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k)
            ∪ (parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k))
            = ({f} : Finset α) := by
          -- X,Y の定義で形を合わせる
          change ((X \ Y) ∪ (Y \ X) = ({f} : Finset α)) at hSingle
          -- ここで X,Y を元に戻す
          -- （hSingle は既に X,Y で書かれている想定ならそのままでも OK）
          -- 以後は hA の要求形に合わせて戻すだけ
          -- U,V 版に戻すには rw [X, Y] を使う
          have : ((parIter (R.erase t) (B ∪ S₁) k \ parIter (R.erase t) (B ∪ S₂) k)
                 ∪ (parIter (R.erase t) (B ∪ S₂) k \ parIter (R.erase t) (B ∪ S₁) k))
                 = ({f} : Finset α) := by
            -- 置換で X,Y に一致させてから hSingle を適用
            -- 左から右へ：X=…,Y=… を入れて戻す
            -- ここは `change` で目標を X,Y 形に落としてから exact hSingle でも OK
            -- 書き直し版：
            change ((parIter (R.erase t) U k \ parIter (R.erase t) V k)
                    ∪ (parIter (R.erase t) V k \ parIter (R.erase t) U k))
                    = ({f} : Finset α)
            at hSingle
            -- U,V を B∪S₁, B∪S₂ に戻す
            simpa [U, V] using hSingle
          exact this
        -- ここで hA を適用
        exact hA hW1 hW2 hEqNext' hSingle'

      -- 以降、対称差＝単点 {f} を A := X\Y, B := Y\X で場合分け
      -- A ∪ B = {f} から 3 ケース（右枝 / 左枝 / 両側 {f}）
      have hcases :
        (X \ Y = ∅ ∧ Y \ X = {f}) ∨
        (X \ Y = {f} ∧ Y \ X = ∅) ∨
        (X \ Y = {f} ∧ Y \ X = {f}) := by
        -- これはあなたの `union_singleton_cases` を A:=X\Y, B:=Y\X に適用
        -- union_singleton_cases : X ∪ Y = {f} → …
        -- に A,B を渡す
        have : (X \ Y) ∪ (Y \ X) = ({f} : Finset α) := by
          -- hSingle はまさにこれ
          -- ただし上で X,Y を set したので、そのまま使える
          change ((X \ Y) ∪ (Y \ X) = ({f} : Finset α)) at hSingle
          exact hSingle
        -- これに union_singleton_cases を適用
        -- まず短い補題として
        exact union_singleton_cases (X := X \ Y) (Y := Y \ X) (f := f) (h := this)

      -- それぞれ閉じる
      cases hcases with
      | inl hR =>
        -- 右枝: X\Y=∅, Y\X={f}
        rcases hR with ⟨hXYempty, hYsingle⟩
        -- f∈Y かつ f∉X
        have hfY : f ∈ Y := by
          have : f ∈ Y \ X := by
            -- mem_and_not_mem_of_sdiff_singleton_right から
            have hh := mem_and_not_mem_of_sdiff_singleton_right
              (X := X) (Y := Y) (f := f) (h := hYsingle)
            exact Finset.mem_sdiff.mpr ⟨hh.left, hh.right⟩
          exact (Finset.mem_sdiff.mp this).left
        -- よって f ∈ stepPar (R.erase t) Y
        have hf_in_stepY : f ∈ stepPar (R.erase t) Y :=
          Finset.mem_union.mpr (Or.inl hfY)
        -- (k+1) 段で V 側に所属
        have hf_in_k1_V : f ∈ parIter (R.erase t) V (k+1) := by
          -- parIter … (k+1) = stepPar … (parIter … k) = stepPar … Y
          change f ∈ stepPar (R.erase t) (parIter (R.erase t) V k)
          simp_all only [sdiff_eq_empty_iff_subset, U, V, X, Y]

        -- hEqNext で U 側へ移す
        have hf_in_k1_U : f ∈ parIter (R.erase t) U (k+1) := by
          -- メンバーシップの等式へ写す
          have hmem :
            (f ∈ parIter (R.erase t) V (k+1))
              = (f ∈ parIter (R.erase t) U (k+1)) :=
            congrArg (fun s => f ∈ s) (hEqNext.symm)
          exact Eq.mp hmem hf_in_k1_V
        -- |α| 段（=syncCl）へ持ち上げ
        have hf_sync_U : f ∈ syncCl (R.erase t) U := by
          have hmono :
            parIter (R.erase t) U (k+1)
              ⊆ parIter (R.erase t) U (Fintype.card α) :=
            parIter_le_of_le (R.erase t) U hkBound
          have : f ∈ parIter (R.erase t) U (Fintype.card α) := hmono hf_in_k1_U
          change f ∈ syncCl (R.erase t) U
          -- syncCl 定義
          rw [syncCl]; exact this
        -- f = t.head を代入して、t.head ∈ syncCl (R.erase t) U
        have hHeadIn :
          t.head ∈ syncCl (R.erase t) U := by
          -- hf_head : f = t.head
          -- 置換（rw を避けるなら cases）
          cases hf_head; exact hf_sync_U
        -- violatesFirst と矛盾（hW1）
        have contra :=
          head_from_Rerase_contra_first
            (ρ := ρ) (R := R)
            (hUC := (UniqueChild_iff_UC R).mp hUC)
            (B := B) (S := S₁) (t := t)
            (hFirst := hW1.right)  -- isWitness → violatesFirst
            (hHead  := by
              -- U = B ∪ S₁ を戻して渡す
              change t.head ∈ syncCl (R.erase t) (B ∪ S₁) at hHeadIn
              -- これは U の定義そのもの
              -- `change` でゴールを書き換え済みなので、hHeadIn をそのまま使える
              exact hHeadIn)
        exact False.elim contra

      | inr hrest =>
        cases hrest with
        | inl hL =>
          -- 左枝: X\Y={f}, Y\X=∅
          rcases hL with ⟨hXsingle, hYXempty⟩
          -- f ∈ X, f ∉ Y
          have hfX : f ∈ X := by
            have : f ∈ X \ Y := by
              have hh := mem_and_not_mem_of_sdiff_singleton_right
                (X := Y) (Y := X) (f := f) (h := by
                  -- X\Y={f} を Y\X={f} の形に渡すため対称に
                  -- ここは Y\X ではなく X\Y の形なので、直接には使わず
                  -- いったん「f ∈ X\Y」を構成してから左側だけ取り出します
                  exact hXsingle)
              exact mem_sdiff.mpr hh
            -- 上のやり方を避け、素直に membership の同値を使う
            -- X\Y = {f} → f∈X\Y
            exact by
              have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
              rename_i this_0
              have hfX : f ∈ X := (Finset.mem_sdiff.mp this_0).left
              exact hfX
          -- よって f ∈ stepPar (R.erase t) X
          have hf_in_stepX : f ∈ stepPar (R.erase t) X :=
            Finset.mem_union.mpr (Or.inl hfX)
          -- (k+1) 段で U 側に所属
          have hf_in_k1_U : f ∈ parIter (R.erase t) U (k+1) := by
            change f ∈ stepPar (R.erase t) (parIter (R.erase t) U k)
            exact hf_in_stepX

          -- hEqNext で V 側へ移す
          have hf_in_k1_V : f ∈ parIter (R.erase t) V (k+1) := by
            have hmem :
              (f ∈ parIter (R.erase t) U (k+1))
                = (f ∈ parIter (R.erase t) V (k+1)) :=
              congrArg (fun s => f ∈ s) hEqNext
            exact Eq.mp hmem hf_in_k1_U
          -- |α| 段（=syncCl）へ持ち上げ（今度は V 側）
          have hf_sync_V : f ∈ syncCl (R.erase t) V := by
            have hmono :
              parIter (R.erase t) V (k+1)
                ⊆ parIter (R.erase t) V (Fintype.card α) :=
              parIter_le_of_le (R.erase t) V hkBound
            have : f ∈ parIter (R.erase t) V (Fintype.card α) := hmono hf_in_k1_V
            change f ∈ syncCl (R.erase t) V
            rw [syncCl]; exact this
          -- f = t.head を代入して、t.head ∈ syncCl (R.erase t) V
          have hHeadIn :
            t.head ∈ syncCl (R.erase t) V := by
            cases hf_head; exact hf_sync_V
          -- violatesFirst と矛盾（hW2）
          have contra :=
            head_from_Rerase_contra_first
              (ρ := ρ) (R := R)
              (hUC := (UniqueChild_iff_UC R).mp hUC)
              (B := B) (S := S₂) (t := t)
              (hFirst := hW2.right)
              (hHead  := by
                -- V = B ∪ S₂ を戻す
                change t.head ∈ syncCl (R.erase t) (B ∪ S₂) at hHeadIn
                exact hHeadIn)
          exact False.elim contra

        | inr hdup =>
          -- “両側 {f}” は NoSwap + step 同一から矛盾
          -- hNS から step 同一なら片側差分は空
          have : X \ Y = ∅ ∨ Y \ X = ∅ := hNS X Y hStep
          -- これが (X\Y={f} ∧ Y\X={f}) と両立しない
          rcases hdup with ⟨hXsingle, hYsingle⟩
          cases this with
          | inl hXYempty =>
              -- 右側は {f} のままなので矛盾
              have : (∅ : Finset α) = ({f} : Finset α) := by
                rw [hXYempty] at hXsingle
                exact hXsingle
              -- ∅ ≠ {f}
              exact False.elim (by
                -- 明示に矛盾を作る（カードでも要素でも可）
                -- ここでは「f ∈ {f}」と「f ∉ ∅」で矛盾
                have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                have hnot : f ∉ (∅ : Finset α) := by exact Finset.notMem_empty f
                -- eq.mp で左辺に移す
                have : f ∈ (∅ : Finset α) := by
                  simp_all only [singleton_union, mem_singleton, not_true_eq_false, U, V, X, Y]
                exact hnot this)
          | inr hYXempty =>
              have : (∅ : Finset α) = ({f} : Finset α) := by
                rw [hYXempty] at hYsingle
                exact hYsingle

              exact False.elim (by
                have : f ∈ (∅ : Finset α) := by
                  have hm := congrArg (fun s => f ∈ s) this.symm
                  exact Eq.mp hm (Finset.mem_singleton_self f)
                exact (Finset.notMem_empty f) this)

/-古いバージョン。けしてよい
lemma multiplicity_le_one_addedFamily_noA
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (ρ : RuleOrder α) {R : Finset (Rule α)} {t : Rule α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R)
  (hNTF : NoTwoFreshHeads (R.erase t))
  (hNS  : NoSwap (R.erase t))
  (hA   : OnlyTLastDiff ρ R t)     -- ★ ここを復活
  {B S₁ S₂ : Finset α}
  (hD1 : Disjoint B S₁) (hD2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t) (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ :=
by
  classical
  -- 記号
  set U : Finset α := B ∪ S₁
  set V : Finset α := B ∪ S₂

  -- U=V → S₁=S₂
  have finish_eq : U = V → S₁ = S₂ :=
    disjoint_union_eq_implies_right_eq hD1 hD2

  -- (補助) UC を erase 側へ
  have hUC' : UniqueChild (α:=α) (R.erase t) := by
    intro r₁ r₂ hr₁ hr₂ hhd
    have hr₁R : r₁ ∈ R := (Finset.mem_erase.mp hr₁).2
    have hr₂R : r₂ ∈ R := (Finset.mem_erase.mp hr₂).2
    exact hUC hr₁R hr₂R hhd

  -- 「OnlyTLastDiff から右枝/左枝で f = t.head」を返す小補題を作る
  -- （あなたの OnlyTLastDiff の定義にそのまま一致するはず）

  have head_eq_right_from_A :
    ∀ {k f},
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) →
      parIter (R.erase t) U k \ parIter (R.erase t) V k = ∅ →
      (∃! r : Rule α,
        r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) U k ∧ r.head = f) →
      f = t.head :=
  by
    -- ★ ここは hA をそのまま適用するだけ（定義に依存）。
    --   もし hA が「この状況の時 f=t.head」をちょうど返す形なら `exact hA ...`。
    --   そうでなければ、あなたの環境の hA のインターフェースに合わせて束縛を並べ替えてください。
    intro k f hEqNext hXYempty hExu
    sorry
    --exact hA.right_branch  -- ← あなたの定義に合わせて差し替え

  have head_eq_left_from_A :
    ∀ {k f},
      parIter (R.erase t) U (k+1) = parIter (R.erase t) V (k+1) →
      parIter (R.erase t) V k \ parIter (R.erase t) U k = ∅ →
      (∃! r : Rule α,
        r ∈ R.erase t ∧ r.prem ⊆ parIter (R.erase t) V k ∧ r.head = f) →
      f = t.head :=
  by
    intro k f hEqNext hYXempty hExuY
    sorry
    --exact hA.left_branch   -- ← あなたの定義に合わせて差し替え

  -- 等閉包の等式 ⇒ 「U=V」or「最小段 k と単点 f」
  obtain hUV | ⟨k, f, hk, hEqNext, hSingle⟩ :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R' := R.erase t) hNTF hNS (U := U) (V := V) (hSync := hEq)
  · exact finish_eq hUV
  ·
    -- X,Y, step 同一
    set X : Finset α := parIter (R.erase t) U k
    set Y : Finset α := parIter (R.erase t) V k
    have hStep : stepPar (R.erase t) X = stepPar (R.erase t) Y := by
      change stepPar (R.erase t) (parIter (R.erase t) U k)
           = stepPar (R.erase t) (parIter (R.erase t) V k) at hEqNext
      simpa [X, Y] using hEqNext

    -- 対称差 = {f} の3分岐
    have hcases :=
      sdiff_union_singleton_cases (X := X) (Y := Y) (f := f)
        (by
          -- (X\Y) ∪ (Y\X) = {f}
          -- hSingle はまさにこれ（X,Y の定義を戻すだけ）
          -- rw/simp を避けたいなら、定義等式を展開せず `simpa [X, Y]` 相当で渡せます
          -- ここでは membership 等式にならないので `have := hSingle; exact this`
          simp [X, Y]
          exact hSingle
        )


    -- 場合分け
    cases hcases with
    | inl hRight =>
      -- 右枝：X\Y=∅, Y\X={f}
      rcases hRight with ⟨hXYempty, hYsingle⟩

      -- f ∈ Y\X
      have hfY : f ∈ Y ∧ f ∉ X := by
        let man := mem_and_not_mem_of_sdiff_singleton_right (X:=X) (Y:=Y) (f:=f)
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, not_false_eq_true, and_self, U,
          V, X, Y]

      -- 原因一意 (右枝側は「左の差分が空」→ cause_unique_on_left_of_step_eq を使う形)
      have hExu :
        ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ X ∧ r.head = f :=
        cause_unique_on_left_of_step_eq
          (R := R.erase t) (hUC := hUC') (hstep := hStep)
          (hg := by
            -- f ∈ Y \ X
            exact Finset.mem_sdiff.mpr ⟨hfY.left, hfY.right⟩)

      let hXYempty : X \ Y = ∅ := by
        simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

      -- OnlyTLastDiff から f = t.head
      have hf_head : f = t.head :=
        head_eq_right_from_A (k:=k) (f:=f) hEqNext hXYempty hExu

      -- 右枝は不可能
      have contra :
        False :=
          result_right_impossible ρ R t
            ((UniqueChild_iff_UC R).mp hUC) ht
            (B := B) (S₁ := S₁) hW1
            (k := k) (f := f)
            (U := U) (V := V) rfl
            (hEqNext := hEqNext)
            (X := X) (Y := Y) rfl rfl
            (hXYempty := hXYempty) (hExu := hExu)
            (hf_head := hf_head) (hkBound := hk)
      exact contra.elim

    | inr rest =>
      cases rest with
      | inl hLeft =>
        -- 左枝：X\Y={f}, Y\X=∅
        rcases hLeft with ⟨hXsingle, hYXempty⟩

        -- f ∈ X\Y
        have hfX : f ∈ X ∧ f ∉ Y := by
          let man := mem_and_not_mem_of_sdiff_singleton_right (X:=Y) (Y:=X) (f:=f)
          apply man
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, U, V, X, Y]


        -- 原因一意（左枝側は「右の差分が空」→ cause_unique_on_right_of_step_eq）
        have hExuY :
          ∃! r : Rule α, r ∈ R.erase t ∧ r.prem ⊆ Y ∧ r.head = f :=
          cause_unique_on_right_of_step_eq
            (R := R.erase t) (hUC := hUC') (hstep := hStep)
            (hf := by
              -- f ∈ X \ Y
              exact Finset.mem_sdiff.mpr ⟨hfX.left, hfX.right⟩)

        let hYXempty : Y \ X = ∅ := by
          simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, X, Y]

        -- OnlyTLastDiff から f = t.head
        have hf_head : f = t.head :=
          head_eq_left_from_A (k:=k) (f:=f) hEqNext hYXempty hExuY

        -- 左枝は不可能
        have contra :
          False :=
            result_left_impossible ρ R t
              ((UniqueChild_iff_UC R).mp hUC)
              (B := B) (S₁ := S₁) hW1
              (k := k) (f := f)
              (U := U) (V := V) rfl
              (hEqNext := hEqNext)
              (X := X) (Y := Y) rfl rfl
              (hYXempty := hYXempty) (hExuY := hExuY)
              (hf_head := hf_head) (hkBound := hk)
        exact contra.elim

      | inr hdup =>
        -- 両側 {f} は NoSwap と step 同一に反する
        have hEmpty : X \ Y = ∅ ∨ Y \ X = ∅ := hNS X Y hStep

        -- ところが今は X\Y = {f} かつ Y\X = {f} なので、どちらの枝でも矛盾
        have : False := by
          cases hEmpty with
          | inl hxy =>
              -- f ∈ X\Y （単点 {f} だから）だが、X\Y = ∅ なので矛盾
              have hfXY : f ∈ X \ Y := by
                have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                -- X\Y = {f}
                exact by simp [hdup.left]
              have : f ∈ (∅ : Finset α) := by
                simp [hxy]
                apply Finset.notMem_empty f
                simp_all only [sdiff_eq_empty_iff_subset, mem_erase, ne_eq, U, V, X, Y]
              exact Finset.notMem_empty f this
          | inr hyx =>
              -- f ∈ Y\X だが、Y\X = ∅ なので矛盾
              have hfYX : f ∈ Y \ X := by
                have : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                -- Y\X = {f}
                exact by
                  simp [hdup.right]
              have : f ∈ (∅ : Finset α) := by
                simp
                simp_all [U, V, X, Y]
                have hne : ({f} : Finset α) ≠ ∅ := by
                  -- 例えば「f は {f} に属するが、空集合には属さない」から示す
                  intro hE
                  have hf : f ∈ ({f} : Finset α) := Finset.mem_singleton_self f
                  have : f ∈ (∅ : Finset α) := by
                    simp [hE]
                    simp_all only [sdiff_eq_empty_iff_subset, and_true, singleton_ne_empty]
                  exact Finset.notMem_empty f this

                -- ところが hdup.right は ∅ = {f} を主張しているので矛盾
                exact hne (hdup.right.symm)

              exact Finset.notMem_empty f this

        -- 矛盾からは何でも従うので、S₁ = S₂ を得る
        exact this.elim
-/

/-必要か不明なので、コメントアウト
lemma iter2_stabilizes_at_card
  [DecidableEq α] [Fintype α] [LinearOrder α]
  (R : Finset (Rule α)) (I : Finset α) :
  iter2 R I (Fintype.card α) = iter2 R I (Fintype.card α + 1) := by
  classical
  -- 反証法：動くなら 1 段でサイズが 1 増える。|α| 回までしか増えないので矛盾
  by_contra hneq
  set N := Fintype.card α with hN

  -- まず、N 段目で nextHead? が none なら、その時点で凍結 ⇒ 矛盾
  cases hnh : nextHead? R (iter2 R I N) with
  | none =>
      -- あなたが証明済みの補題（例）:
      -- frozen_forever_of_none :
      --   nextHead? R (iter2 R I k) = none → iter2 R I k = iter2 R I (k+1)
      have hfreeze := frozen_forever_of_none (R:=R)   (h:=hnh)
      apply hneq
      have hstep_fixed : step2 R (iter2 R I N) = iter2 R I N := by
        -- f^[1] x = f x を使って簡約
        exact hfreeze 1

      -- 定義より iter2 の (N+1) 段は step2 を 1 回適用したもの
      have hfix : iter2 R I (N + 1) = iter2 R I N := by
        simpa [iter2] using hstep_fixed

      -- 目標は左右逆なので対称にして終了
      exact hfix.symm

  | some a =>
      -- 「最後の一歩が変化するなら、その前の全ステップも変化する」
      -- all_steps_increase_if_last_increases :
      --   iter2 R I N ≠ iter2 R I (N+1) → ∀ k ≤ N, iter2 R I k ≠ iter2 R I (k+1)
      have hall := all_steps_increase_if_last_increases (R:=R) (I:=I) (N:=N) hneq

      -- 各段で「（k → k+1）は包含」：step2_superset を使う
      -- step2_superset :
      --   ∀ k, iter2 R I k ⊆ iter2 R I (k+1)
      have hmono : ∀ k, iter2 R I k ⊆ iter2 R I (k+1) := by
        intro k
        let ss := step2_superset (R:=R) (I:=I)
        have step2_superset_any : ∀ J : Finset α, J ⊆ step2 R J := by
          intro J x hx
          cases h : nextHead? R J with
          | none =>
              -- step2 R J = J
              simpa [step2, h] using hx
          | some a =>
              -- step2 R J = insert a J
              simp_all only [le_refl, not_false_eq_true, ne_eq, N]
              rw [step2, h]
              simp_all only [mem_insert, or_true]

        -- 目標：iter2 R I k ⊆ iter2 R I (k+1)
        intro x hx
        have hx' : x ∈ step2 R (iter2 R I k) := by
          exact step2_superset_any (iter2 R I k) hx
        simpa [iter2] using hx'


      -- すると、0..N の各ステップで「厳密に増える」：card が毎回少なくとも +1
      -- これを合算して、(N+1) 段目の card ≥ (0 段目の card) + (N+1) ≥ N+1
      -- 一方、全て α の部分集合だから card ≤ |α| = N。矛盾。
      have hstrict_each :
        ∀ k ≤ N, (iter2 R I k).card < (iter2 R I (k+1)).card := by
        intro k hk
        -- 包含 & 不等号 ⇒ 真部分集合 ⇒ card は厳に増加
        have hsubset : iter2 R I k ⊆ iter2 R I (k+1) := hmono k
        have hne     : iter2 R I k ≠ iter2 R I (k+1) := hall k hk
        have hss     : iter2 R I k ⊂ iter2 R I (k+1) := by
          constructor
          · exact hmono k
          · intro h
            apply hne
            exact Subset.antisymm (hmono k) h

        exact Finset.card_lt_card hss

      -- これで「0..N の N+1 回の遷移」で毎回 card が 1 以上増える。
      -- 帰納でまとめる：
      have hsum :
        (iter2 R I (N+1)).card ≥ (iter2 R I 0).card + (N+1) := by
        -- 簡単な帰納（長くなるのでコンパクトに書きます）
        -- base: k=0 は (iter2 1).card ≥ (iter2 0).card + 1
        -- step: k → k+1 で一回分足す
        -- ここでは `Nat.le_of_lt` と加法単調性で積み上げ
        -- （詳しく書く場合は Nat.rec で k を 0..N まで回して積上げます）
        -- 手短版：
        have : ∀ k ≤ N, (iter2 R I (k+1)).card ≥ (iter2 R I 0).card + (k+1) := by
          intro k hk
          induction' k with k ih
          · -- k=0
            have hlt := hstrict_each 0 (Nat.zero_le _)
            have hle := Nat.le_of_lt hlt
            simp
            exact hstrict_each 0 hk
          · -- k+1
            have hkle : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
            have ih' := ih hkle
            sorry
            /-
            --have hlt := hstrict_each (k+1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
            have hle := Nat.le_of_lt hlt
            -- (k+2) 段の card ≥ (k+1) 段の card + 1 ≥ (iter2 0).card + (k+1) + 1
            calc
              (iter2 R I (k+2)).card
                ≥ (iter2 R I (k+1)).card + 1 := by
                      -- (k+1 → k+2) で 1 増
                      -- hstrict_each gives strict <, なので ≥ +1 は自明（Nat なので）
                      have : (iter2 R I (k+1)).card < (iter2 R I (k+2)).card := hstrict_each (k+1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
                      exact Nat.succ_le_of_lt this
            _ ≥ (iter2 R I 0).card + (k+1) + 1 := by exact Nat.add_le_add_right ih' 1
            _ = (iter2 R I 0).card + (k+2) := by omega
            -/
        -- これを k := N に適用
        simpa using this N (Nat.le_refl _)

      -- ところが (iter2 _ _ (N+1)) は α の有限部分集合なので card ≤ N
      have hupper : (iter2 R I (N+1)).card ≤ N := by
        simpa [hN] using Finset.card_le_univ (iter2 R I (N+1))
      -- 下限 N+1 と上限 N の矛盾
      have : N + 1 ≤ N := by
        -- (iter2 0).card ≥ 0 を使えば `hsum` から N+1 ≤ card(N+1) ≤ N
        have h0 : (iter2 R I 0).card ≥ 0 := Nat.zero_le _
        have hsum' : (iter2 R I (N+1)).card ≥ 0 + (N+1) := by
          sorry
          --simpa using (Nat.le_trans (Nat.add_le_add_left h0 _) hsum)
        sorry
        --exact (le_trans hsum' hupper)
      exact Nat.not_succ_le_self N this
-/

/-
-- UC + Two-Stem：addedFamily への写像は witness ごとに高々1本（単射）
--Witnessにも同名で同内容の補題があるので、そっちに移動か。
--一つ上の補題とも同内容。
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  (hUC : UniqueChild (α:=α) R)
  {B : Finset α} {t : Rule α} {S₁ S₂ : Finset α}
  -- 追加の前提: B と S の分離性
  (hDisj1 : Disjoint B S₁)
  (hDisj2 : Disjoint B S₂)
  (hW1 : isWitness ρ R B S₁ t)
  (hW2 : isWitness ρ R B S₂ t)
  (hEq : syncCl (R.erase t) (B ∪ S₁) = syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 差分集合
  let D : Finset α := ((B ∪ S₁) \ (B ∪ S₂)) ∪ ((B ∪ S₂) \ (B ∪ S₁))

  by_cases hD : D = ∅
  · -- 差分なし ⇒ B∪S₁ = B∪S₂ ⇒ S₁=S₂
    have hEqU : B ∪ S₁ = B ∪ S₂ := by
      ext x
      constructor <;> intro hx
      · by_cases h : x ∈ B ∪ S₂
        · exact h
        · have : x ∈ D := by
            apply mem_union_left
            exact mem_sdiff.mpr ⟨hx, h⟩
          rw [hD] at this
          exact absurd this (Finset.notMem_empty x)
      · by_cases h : x ∈ B ∪ S₁
        · exact h
        · have : x ∈ D := by
            apply mem_union_right
            exact mem_sdiff.mpr ⟨hx, h⟩
          rw [hD] at this
          exact absurd this (Finset.notMem_empty x)

    -- B∪S₁ = B∪S₂ かつ Disjoint B S₁, Disjoint B S₂ から S₁ = S₂
    ext x
    constructor <;> intro hx
    · have : x ∈ B ∪ S₂ := by rw [←hEqU]; exact mem_union_right B hx
      cases mem_union.mp this with
      | inl hxB =>
        -- x ∈ B ∩ S₁ は Disjoint B S₁ に矛盾
        exact absurd (mem_inter.mpr ⟨hxB, hx⟩) (disjoint_iff_inter_eq_empty.mp hDisj1 ▸ not_mem_empty x)
      | inr hxS2 => exact hxS2
    · have : x ∈ B ∪ S₁ := by rw [hEqU]; exact mem_union_right B hx
      cases mem_union.mp this with
      | inl hxB =>
        exact absurd (mem_inter.mpr ⟨hxB, hx⟩) (disjoint_iff_inter_eq_empty.mp hDisj2 ▸ not_mem_empty x)
      | inr hxS1 => exact hxS1
  · -- 差分が非空の場合
    -- Two-Stem を使って初回差分座標 f を特定
    obtain ⟨f, hfPred, huniq⟩ :=
      firstDiff_localizes_one_coordinate (α:=α) ρ (R:=R) hTS
        (t:=t) (B:=B) (S₁:=S₁) (S₂:=S₂) hW1 hW2

    -- f が唯一の差分。片側で f∈B∪S₁, f∉B∪S₂ (または逆) を仮定して矛盾を示す
    cases hfPred with
    | inl hL =>
      -- f ∈ B∪S₁ かつ f ∉ B∪S₂ の場合
      obtain ⟨hfU1, hfN2⟩ := hL

      -- syncCl は closure と同じと仮定（または適切な補題で変換）
      have hfCl1 : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
        apply subset_syncCl
        exact hfU1

      -- 閉包の等式から f ∈ syncCl (R.erase t) (B ∪ S₂)
      have hfCl2 : f ∈ syncCl (R.erase t) (B ∪ S₂) := by
        rw [←hEq]
        exact hfCl1

      -- 一方 f ∉ B ∪ S₂ なので、f を導出するには R\{t} の中に head=f のルールが必要
      -- しかし UC により head=f のルールは R 全体で高々1本

      -- f が closure に入るには、ある導出経路が必要
      obtain ⟨path, hpath⟩ := syncCl_has_derivation hfCl2

      -- path の最後のルールを r とする（f を直接導くルール）
      obtain ⟨r, hr_in, hr_head, hr_prem⟩ := derivation_final_step hpath

      -- r ∈ R.erase t かつ r.head = f
      have hr_in_R : r ∈ R := by
        exact erase_subset _ _ hr_in

      -- UC により、R 内で head=f のルールは高々1本
      -- もし t.head = f なら、r = t となるが r ∈ R.erase t に矛盾
      by_cases ht_head : t.head = f
      · -- t.head = f の場合
        have : r = t := hUC hr_in_R (isWitness_implies_t_in_R hW1) (hr_head.trans ht_head.symm)
        exact absurd hr_in (not_mem_erase this)

      · -- t.head ≠ f の場合
        -- r は t と異なり、かつ head = f
        -- しかし witness の最小性により、f は S₁ の最小要素であり、
        -- B∪(S₁\{f}) からは f が導けないはず

        -- これは witness の定義と矛盾
        have : f ∈ S₁ := by
          cases mem_union.mp hfU1 with
          | inl hB => exact absurd (mem_inter.mpr ⟨hB, by assumption⟩)
                            (disjoint_iff_inter_eq_empty.mp hDisj1 ▸ not_mem_empty f)
          | inr hS => exact hS

        have : ¬(f ∈ syncCl (R.erase t) (B ∪ (S₁.erase f))) :=
          witness_minimal hW1 this

        -- しかし r.prem ⊆ B ∪ S₂ ⊆ B ∪ (S₁ の f 以外の要素) となるはず（差分唯一性）
        have : r.prem ⊆ B ∪ (S₁.erase f) := by
          intro x hx
          -- x ∈ r.prem ⊆ B ∪ S₂
          have hx_in : x ∈ B ∪ S₂ := hr_prem hx
          -- x ≠ f なら（f は唯一の差分）、x ∈ B ∪ S₁
          by_cases hxf : x = f
          · -- x = f は r.prem に含まれるが、f ∉ B∪S₂ に矛盾
            rw [hxf] at hx_in
            exact absurd hx_in hfN2
          · -- x ≠ f なので差分集合に含まれない
            have : x ∉ D := huniq x hxf
            -- 従って x ∈ (B∪S₁) ∩ (B∪S₂)
            simp [D] at this
            push_neg at this
            obtain ⟨h1, h2⟩ := this
            cases mem_union.mp (h1 hx_in) with
            | inl hB => exact mem_union_left _ hB
            | inr hS1 => exact mem_union_right _ (mem_erase.mpr ⟨hxf, hS1⟩)

        -- これで r を使って f が B∪(S₁\{f}) から導ける
        exact absurd (syncCl_rule_fires hr_in this hr_head) ‹¬(f ∈ syncCl _ _)›

    | inr hR =>
      -- f ∉ B∪S₁ かつ f ∈ B∪S₂ の場合（対称的に同じ論法）
      obtain ⟨hfN1, hfU2⟩ := hR

      have hfCl2 : f ∈ syncCl (R.erase t) (B ∪ S₂) :=
        subset_syncCl hfU2
      have hfCl1 : f ∈ syncCl (R.erase t) (B ∪ S₁) := by
        rw [hEq]
        exact hfCl2

      -- 以下、上と対称的な論法で矛盾
      obtain ⟨path, hpath⟩ := syncCl_has_derivation hfCl1
      obtain ⟨r, hr_in, hr_head, hr_prem⟩ := derivation_final_step hpath

      have hr_in_R : r ∈ R := erase_subset _ _ hr_in

      by_cases ht_head : t.head = f
      · have : r = t := hUC hr_in_R (isWitness_implies_t_in_R hW1) (hr_head.trans ht_head.symm)
        exact absurd hr_in (not_mem_erase this)
      · have hf_in_S2 : f ∈ S₂ := by
          cases mem_union.mp hfU2 with
          | inl hB => exact absurd (mem_inter.mpr ⟨hB, by assumption⟩)
                            (disjoint_iff_inter_eq_empty.mp hDisj2 ▸ not_mem_empty f)
          | inr hS => exact hS

        have : ¬(f ∈ syncCl (R.erase t) (B ∪ (S₂.erase f))) :=
          witness_minimal hW2 hf_in_S2

        have : r.prem ⊆ B ∪ (S₂.erase f) := by
          intro x hx
          have hx_in : x ∈ B ∪ S₁ := hr_prem hx
          by_cases hxf : x = f
          · rw [hxf] at hx_in
            exact absurd hx_in hfN1
          · have : x ∉ D := huniq x hxf
            simp [D] at this
            push_neg at this
            obtain ⟨h1, h2⟩ := this
            cases mem_union.mp (h2 hx_in) with
            | inl hB => exact mem_union_left _ hB
            | inr hS2 => exact mem_union_right _ (mem_erase.mpr ⟨hxf, hS2⟩)

        exact absurd (syncCl_rule_fires hr_in this hr_head) ‹¬(f ∈ syncCl _ _)›
-/

/- first violation（定義は既存ファイル側のものを使う） -/
-- ここでは型だけ参照： violatesFirst ρ R t I



end Twostem
/-
---以下は検証用コード。しばらく残す。

namespace TestUC

-- ここでは Twostem の定義が Closure 名前空間から見える想定に合わせます
-- 必要なら Twostem. を付け替えてください。
-- 例：Twostem.UniqueChild_iff_UC など。

-- ---------- 具体例: α := Bool ----------
noncomputable instance : DecidableEq (Closure.Rule Bool) := Classical.decEq _
instance : DecidableEq Bool := inferInstance

open Finset

def r1 : Closure.Rule Bool := { head := true,  prem := (∅ : Finset Bool) }
def r2 : Closure.Rule Bool := { head := false, prem := (∅ : Finset Bool) }
def r3 : Closure.Rule Bool := { head := true,  prem := ({false} : Finset Bool) }

noncomputable def Rgood : Finset (Closure.Rule Bool) := insert r2 {r1}   -- = {r1, r2}
noncomputable def Rbad  : Finset (Closure.Rule Bool) := insert r3 {r1}   -- = {r1, r3}

@[simp] lemma mem_Rgood_iff {x : Closure.Rule Bool} :
    x ∈ Rgood ↔ x = r1 ∨ x = r2 := by
  constructor
  · intro hx
    have hx' : x = r2 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl hx2 =>
        right  -- x = r2 なので、ゴール (x = r1 ∨ x = r2) の右側
        exact hx2
    | inr hx1 =>
        have hxeq : x = r1 := (mem_singleton).1 hx1
        left  -- x = r1 なので、ゴール (x = r1 ∨ x = r2) の左側
        exact hxeq
  · intro h
    cases h with
    | inl hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        exact (mem_insert).2 (Or.inr this)
    | inr hx2 =>
        cases hx2
        exact (mem_insert_self r2 _)

@[simp] lemma mem_Rbad_iff {x : Closure.Rule Bool} :
    x ∈ Rbad ↔ x = r1 ∨ x = r3 := by
  constructor
  · intro hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl h =>
        right  -- x = r3 なので、ゴール (x = r1 ∨ x = r3) の右側
        exact h
    | inr h1 =>
        have : x = r1 := (mem_singleton).1 h1
        left  -- x = r1 なので、ゴール (x = r1 ∨ x = r3) の左側
        exact this
  · intro h
    cases h with
    | inl hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        exact (mem_insert).2 (Or.inr this)
    | inr hx3 =>
        cases hx3
        exact (mem_insert_self r3 _)


-- ---------- 一般形：等価の .mp / .mpr がそのまま使える ----------

section general
variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]
variable [DecidableEq (Closure.Rule α)]
variable {R : Finset (Closure.Rule α)}

example (h : Twostem.UniqueChild (α:=α) R) :
    Twostem.UC (α:=α) R :=
  (Twostem.UniqueChild_iff_UC (α:=α) R).mp h

example (h : Twostem.UC (α:=α) R) :
    Twostem.UniqueChild (α:=α) R :=
  (Twostem.UniqueChild_iff_UC (α:=α) R).mpr h
end general

-- ---------- 良い例：UC が成り立つ（＝ head ごとに高々1本） ----------

example : Twostem.UC (α:=Bool) Rgood := by
  intro a
  cases a with
  | false =>
      have hx :
        (Rgood.filter (fun t => t.head = false))
          = ({r2} : Finset (Closure.Rule Bool)) := by
        apply ext; intro x
        constructor
        · intro hxmem
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = false := (mem_filter).1 hxmem |>.2
          have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
          cases hx' with
          | inl h1 =>
              have : r1.head = true := rfl
              cases h1; cases this; cases hH
          | inr h2 => cases h2; exact (mem_singleton).2 rfl
        · intro hxmem
          have hx2 : x = r2 := (mem_singleton).1 hxmem
          have hR2 : r2 ∈ Rgood := by
            apply (mem_insert).2; left; rfl
          have hpair : r2 ∈ Rgood ∧ r2.head = false := And.intro hR2 rfl
          cases hx2; exact (mem_filter).2 hpair
      have hcard : (Rgood.filter (fun t => t.head = false)).card ≤ 1 := by
        have heq :
          (Rgood.filter (fun t => t.head = false)).card
            = ({r2} : Finset (Closure.Rule Bool)).card :=
          congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
        have hone : ({r2} : Finset (Closure.Rule Bool)).card = 1 :=
          card_singleton r2
        have : (Rgood.filter (fun t => t.head = false)).card = 1 :=
          Eq.trans heq hone
        exact Eq.le this
      exact hcard
  | true =>
      have hx :
        (Rgood.filter (fun t => t.head = true))
          = ({r1} : Finset (Closure.Rule Bool)) := by
        apply ext; intro x
        constructor
        · intro hxmem
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = true := (mem_filter).1 hxmem |>.2
          have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
          cases hx' with
          | inl h1 => cases h1; exact (mem_singleton).2 rfl
          | inr h2 => cases h2; cases hH
        · intro hxmem
          have hx1 : x = r1 := (mem_singleton).1 hxmem
          have hR1 : r1 ∈ Rgood :=
            (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
          have hpair : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
          cases hx1; exact (mem_filter).2 hpair
      have heq :
        (Rgood.filter (fun t => t.head = true)).card
          = ({r1} : Finset (Closure.Rule Bool)).card :=
        congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
      have hone : ({r1} : Finset (Closure.Rule Bool)).card = 1 :=
        card_singleton r1
      have hfin : (Rgood.filter (fun t => t.head = true)).card = 1 :=
        Eq.trans heq hone
      exact Eq.le hfin

-- UniqueChild も Rgood では成立（等価で変換）
example : Twostem.UniqueChild (α:=Bool) Rgood :=
  (Twostem.UniqueChild_iff_UC (α:=Bool) Rgood).mpr
    (by
      intro a
      cases a with
      | false =>
          -- a = false の場合
          have hx :
            (Rgood.filter (fun t => t.head = false))
              = ({r2} : Finset (Closure.Rule Bool)) := by
            apply ext; intro x
            constructor
            · intro hxmem
              have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
              have hH : x.head = false := (mem_filter).1 hxmem |>.2
              have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
              cases hx' with
              | inl h1 => cases h1; cases hH
              | inr h2 => cases h2; exact (mem_singleton).2 rfl
            · intro hxmem
              have hx2 : x = r2 := (mem_singleton).1 hxmem
              have hR2 : r2 ∈ Rgood := (mem_insert).2 (Or.inl rfl)
              have hpair : r2 ∈ Rgood ∧ r2.head = false := And.intro hR2 rfl
              cases hx2; exact (mem_filter).2 hpair
          have heq :
            (Rgood.filter (fun t => t.head = false)).card
              = ({r2} : Finset (Closure.Rule Bool)).card :=
            congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
          have hone : ({r2} : Finset (Closure.Rule Bool)).card = 1 :=
            card_singleton r2
          have hfin :
            (Rgood.filter (fun t => t.head = false)).card = 1 :=
            Eq.trans heq hone
          exact Eq.le hfin
      | true =>
          -- a = true の場合
          have hx :
            (Rgood.filter (fun t => t.head = true))
              = ({r1} : Finset (Closure.Rule Bool)) := by
            apply ext; intro x
            constructor
            · intro hxmem
              have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
              have hH : x.head = true := (mem_filter).1 hxmem |>.2
              have hx' : x = r1 ∨ x = r2 := (mem_Rgood_iff).1 hR
              cases hx' with
              | inl h1 => cases h1; exact (mem_singleton).2 rfl
              | inr h2 => cases h2; cases hH
            · intro hxmem
              have hx1 : x = r1 := (mem_singleton).1 hxmem
              have hR1 : r1 ∈ Rgood :=
                (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
              have hpair : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
              cases hx1; exact (mem_filter).2 hpair
          have heq :
            (Rgood.filter (fun t => t.head = true)).card
              = ({r1} : Finset (Closure.Rule Bool)).card :=
            congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
          have hone : ({r1} : Finset (Closure.Rule Bool)).card = 1 :=
            card_singleton r1
          have hfin :
            (Rgood.filter (fun t => t.head = true)).card = 1 :=
            Eq.trans heq hone
          exact Eq.le hfin
    )

-- ---------- 悪い例：UniqueChild も UC も成り立たない ----------

example : ¬ Twostem.UniqueChild (α:=Bool) Rbad := by
  intro hUC
  have hr1 : r1 ∈ Rbad :=
    (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
  have hr3 : r3 ∈ Rbad :=
    (mem_insert).2 (Or.inl rfl)
  have hhead : r1.head = r3.head := rfl
  have h_eq : r1 = r3 := hUC hr1 hr3 hhead
  have hprem : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h_eq
  have hneq : (∅ : Finset Bool) ≠ ({false} : Finset Bool) := by
    intro h
    have : false ∈ (∅ : Finset Bool) := by
      rw [h]; exact mem_singleton_self false
    exact (List.mem_nil_iff false).mp this
  exact hneq hprem


example : ¬ Twostem.UC (α:=Bool) Rbad := by
  intro hUC
  have hr1 : r1 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r1 ∈ Rbad :=
      (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
    have : r1 ∈ Rbad ∧ r1.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  have hr3 : r3 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r3 ∈ Rbad := (mem_insert).2 (Or.inl rfl)
    have : r3 ∈ Rbad ∧ r3.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  have hneq : r1 ≠ r3 := by
    intro h
    have : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h
    have : (∅ : Finset Bool) = ({false} : Finset Bool) := this
    have : false ∈ (∅ : Finset Bool) := by
      rw [this]; exact mem_singleton_self false
    exact (List.mem_nil_iff false).mp this

  have hsubset : insert r3 ({r1} : Finset (Closure.Rule Bool))
                  ⊆ Rbad.filter (fun t => t.head = true) := by
    intro x hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_insert).1 hx
    cases hx' with
    | inl hx3 => cases hx3; exact hr3
    | inr hx1 =>
        have : x = r1 := (mem_singleton).1 hx1
        cases this; exact hr1
  have hpair : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card = 2 := by
    have hnot : r3 ∉ ({r1} : Finset (Closure.Rule Bool)) := by
      intro hx; apply hneq; exact (mem_singleton).1 hx |>.symm
    have hbase : ({r1} : Finset (Closure.Rule Bool)).card = 1 := card_singleton r1
    have : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card
              = ({r1} : Finset (Closure.Rule Bool)).card + 1 :=
      card_insert_of_notMem hnot
    rw [hbase] at this
    exact this
  have hge2 : 2 ≤ (Rbad.filter (fun t => t.head = true)).card := by
    calc 2 = (insert r3 ({r1} : Finset (Closure.Rule Bool))).card := hpair.symm
         _ ≤ (Rbad.filter (fun t => t.head = true)).card := card_le_card hsubset

  have hle1 : (Rbad.filter (fun t => t.head = true)).card ≤ 1 := hUC true
  omega

end TestUC
-/


/-

--単射性の証明に使う？Unique Childはいらないのか。そのままではなりたたない。
/-- Two-Stem による「初回差の 1 座標局在」の仕様（抽象化）。
    実装では「B∪S と B∪S' の (R\{t})-closure を同期的に回したとき、
    最初に分岐する箇所は Free の 1 座標 f に限る」ことを述べる。 -/
private lemma firstDiff_localizes_one_coordinate
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (hTS : TwoStemR R) (B S S' : Finset α) (t : Rule α)
  (hS : isWitness (α:=α) ρ R B S t)
  (hS' : isWitness (α:=α) ρ R B S' t)
  (hne : S ≠ S')
  (hEq : syncCl (R.erase t) (B ∪ S) = syncCl (R.erase t) (B ∪ S')) :
  ∃ f,
    f ∈ (S ∆ S') ∧
    ((f ∈ B ∪ S ∧ f ∉ B ∪ S') ∨ (f ∉ B ∪ S ∧ f ∈ B ∪ S')) ∧
    (∀ g, g ≠ f → g ∉ ((B ∪ S) \ (B ∪ S') ∪ (B ∪ S') \ (B ∪ S))) := by
  classical

  -- 対称差が非空であることを確認
  have hNonempty : (S ∆ S').Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have : S = S' := by
      ext x
      constructor <;> intro hx
      · by_contra hnx
        have : x ∈ S ∆ S' := by
          simp [symmDiff_def, Finset.mem_sdiff]
          exact Or.inl ⟨hx, hnx⟩
        rw [h] at this
        exact Finset.notMem_empty x this
      · by_contra hnx
        have : x ∈ S ∆ S' := by
          simp [symmDiff_def, Finset.mem_sdiff]
          exact Or.inr ⟨hx, hnx⟩
        rw [h] at this
        exact Finset.notMem_empty x this
    exact hne this

  -- 対称差の最小要素を f とする
  obtain ⟨f, hf_mem, hf_min⟩ := (S ∆ S').exists_min_image id hNonempty

  use f

  constructor
  · exact hf_mem

  constructor
  · -- f は B∪S と B∪S' の一方にのみ属する
    simp [symmDiff_def, Finset.mem_sdiff] at hf_mem
    cases hf_mem with
    | inl h =>
      obtain ⟨hfS, hfnS'⟩ := h
      left
      constructor
      · exact Finset.mem_union_right B hfS
      · intro hf
        cases Finset.mem_union.mp hf with
        | inl hB =>
          -- f ∈ B ∩ S は分離性から矛盾（witness の性質）
          have : Disjoint B S := isWitness_disjoint hS
          exact absurd (Finset.mem_inter.mpr ⟨hB, hfS⟩)
            (Finset.disjoint_iff_inter_eq_empty.mp this ▸ Finset.notMem_empty f)
        | inr hS' => exact hfnS' hS'
    | inr h =>
      obtain ⟨hfS', hfnS⟩ := h
      right
      constructor
      · intro hf
        cases Finset.mem_union.mp hf with
        | inl hB =>
          have : Disjoint B S' := isWitness_disjoint hS'
          exact absurd (Finset.mem_inter.mpr ⟨hB, hfS'⟩)
            (Finset.disjoint_iff_inter_eq_empty.mp this ▸ Finset.not_mem_empty f)
        | inr hS => exact hfnS hS
      · exact Finset.mem_union_right B hfS'

  · -- f の一意性：g ≠ f なら g は差分に含まれない
    intro g hgf
    intro hg

    simp [Finset.mem_union, Finset.mem_sdiff] at hg

    -- g が差分集合に属するなら、g ∈ S ∆ S'
    have hg_symmDiff : g ∈ S ∆ S' := by

      cases hg with
      | inl h =>

        obtain ⟨⟨hgBS, hgnBS'⟩, _⟩ := h
        cases Finset.mem_union.mp hgBS with
        | inl hgB =>
          -- g ∈ B なら両側に属するはず（B は共通部分）
          have : g ∈ B ∪ S' := Finset.mem_union_left S' hgB
          exact absurd this hgnBS'
        | inr hgS =>
          cases Finset.mem_union.mp hgnBS' with
          | inl =>
            left
            constructor
            · exact hgS
            · intro hgS'
              exact absurd (Finset.mem_union_right B hgS') hgnBS'
          | inr =>
            left
            constructor
            · exact hgS
            · intro hgS'
              exact absurd (Finset.mem_union_right B hgS') hgnBS'
      | inr h =>
        obtain ⟨⟨hgBS', hgnBS⟩, _⟩ := h
        cases Finset.mem_union.mp hgBS' with
        | inl hgB =>
          have : g ∈ B ∪ S := Finset.mem_union_left S hgB
          exact absurd this hgnBS
        | inr hgS' =>
          right
          constructor
          · exact hgS'
          · intro hgS
            exact absurd (Finset.mem_union_right B hgS) hgnBS

    -- g ∈ S ∆ S' かつ f が最小 ⇒ f ≤ g
    have : ρ.toFun f ≤ ρ.toFun g := hf_min g hg_symmDiff

    -- しかし Two-Stem の下で、f より大きい g が本質的差分であることは不可能
    -- なぜなら：
    -- 1) B ∪ (S ∩ S') から出発して同期的閉包を構成
    -- 2) f を追加する/しないで最初の分岐が生じる
    -- 3) その後の g での差分は f の分岐の結果にすぎない

    -- 共通部分を定義
    let common := B ∪ (S ∩ S')

    -- f を含む側と含まない側の閉包を考える
    have hClosure_analysis :
      ∃ (step : ℕ),
        let cl_with_f := iterate_syncCl (R.erase t) (common ∪ {f}) step
        let cl_without_f := iterate_syncCl (R.erase t) common step
        g ∈ cl_with_f ∧ g ∉ cl_without_f := by
      sorry -- この部分は iterate_syncCl の詳細な性質が必要

    obtain ⟨step, hstep⟩ := hClosure_analysis

    -- g を導出するルール r が存在
    obtain ⟨r, hr_in, hr_head, hr_prem⟩ :=
      element_has_rule_in_closure hstep.1

    -- Two-Stem: r.prem.card ≤ 2
    have hTS_r : r.prem.card ≤ 2 := hTS r hr_in

    -- r.prem ⊆ cl_with_f かつ g = r.head
    -- r.prem の要素で cl_without_f に含まれないものを分析

    have : ∃ x ∈ r.prem, x ∈ cl_with_f ∧ x ∉ cl_without_f := by
      by_contra h
      push_neg at h
      -- すべての r.prem が cl_without_f に含まれるなら
      have : r.prem ⊆ cl_without_f := fun x hx =>
        (h x hx).2 (hr_prem hx)
      -- g = r.head も cl_without_f に含まれるはず
      have : g ∈ cl_without_f :=
        syncCl_rule_fires hr_in this hr_head
      exact hstep.2 this

    obtain ⟨x, hx_prem, hx_diff⟩ := this

    -- x での差分が f より小さい位置で生じる
    -- しかし f は最小差分なので矛盾

    -- x が f より小さいか f 自身かを判定
    by_cases hxf : x = f
    · -- x = f の場合：f が r.prem に直接含まれる
      -- これは許容（f が直接使われて g が導出される）
      -- しかし g ≠ f なので、g は f の後の段階で導出される
      -- つまり g は本質的差分ではなく派生的差分
      sorry -- 詳細な段階解析が必要
    · -- x ≠ f の場合：x も差分要素
      have : x ∈ S ∆ S' := by
        sorry -- x が差分であることを示す
      -- x ∈ S ∆ S' かつ x が f より先に差分を生じる
      -- しかし f は最小差分なので ρ.toFun f ≤ ρ.toFun x
      have : ρ.toFun f ≤ ρ.toFun x := hf_min x ‹x ∈ S ∆ S'›
      -- Two-Stem により |r.prem| ≤ 2 なので
      -- r.prem = {f, y} または {x, y} の形
      -- いずれにしても f より小さい本質的差分 x が存在することになり
      -- f の最小性に矛盾
      sorry
-/


/-証明はとおっているが、コメントアウトしたもので使っているだけ。消しても良い。
omit [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)] in
lemma in_symmDiff_ne_f_impossible
  [DecidableEq α]
  {R : Finset (Rule α)} {U V : Finset α} {m : ℕ} {f x : α}
  (hLast : (parIter R U m \ parIter R V m ∪ parIter R V m \ parIter R U m) ⊆ {f})
  (hx : x ∈ parIter R U m \ parIter R V m ∪ parIter R V m \ parIter R U m)
  (hxf : x ≠ f) : False := by
  classical
  have : x ∈ ({f} : Finset α) := hLast hx
  have : x = f := by simpa [Finset.mem_singleton] using this
  exact hxf this
-/

/-なりたたないかも
lemma symmDiff_mono_under_NoSwap'
  [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R)
  (U V : Finset α) (k : ℕ) (f : α)
  (hEqNext : parIter R U (k+1) = parIter R V (k+1))
  (hk : let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m);
        D k = {f}) :
  let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
  ∀ m ≤ k, D m ⊆ {f} := by
  classical
  -- 記法短縮
  let D : ℕ → Finset α :=
    fun n => (parIter R U n \ parIter R V n) ∪ (parIter R V n \ parIter R U n)
  intro D m hm
  -- 逆向き（k から m へ）の降順帰納を使うのが自然
  -- 命題 Q(n): D n ⊆ {f}
  -- Q(k) は仮定から成り立つ。
  -- n < k → Q(n+1) から Q(n) を示すのに必要なのは、
  --   D n ⊆ D (n+1) ∪ {f} という“1ステップ抑え込み”補題。
  -- これを NoSwap と「最終段(k+1)の一致」と組み合わせれば出せます。
  -- d := k - m を固定
  --set d : ℕ := k - m with hdm
  generalize hdm : k - m = d
  -- m を一般化して d で帰納
  revert m
  induction' d with d ih
  -- base : d = 0
  case zero =>
    intro m hm hdm
    -- k - m = 0 ⇒ k ≤ m。hm : m ≤ k と合わせて m = k
    have hkm0 : k - m = 0 := hdm
    have hkm : k ≤ m :=by exact Nat.le_of_sub_eq_zero hdm
    have : m = k := le_antisymm hm hkm
    subst this
    -- ここで P k を示す
    -- ...（あなたの目的に応じて書く）
    exact Finset.subset_of_eq hk

  -- step : d → d+1
  case succ _ _ _ _ _ ih =>
    -- k - m = d+1 > 0 ⇒ m < k
    intro m hm hdm
    have hm_lt : m < k := by
      have : 0 < d.succ := Nat.succ_pos d
      -- k - m > 0 ↔ m < k
      exact Nat.lt_of_sub_eq_succ hdm
    -- m+1 も k 以下
    have hm1 : m + 1 ≤ k := Nat.succ_le_of_lt hm_lt
    -- 算術：k - (m+1) = d
    have hdm1 : k - (m+1) = d := by
      -- k - (m+1) = (k - m) - 1, かつ k - m = d+1
      have : k - (m+1) = k - m - 1 := by
        simpa using (Nat.sub_sub k m 1).symm
      simp [this, hdm]   -- → d

    -- 帰納法で P (m+1)
    apply ih

    exact hm
    sorry
  -/

/-なりたたないよう。
-- 補助補題2：NoSwapの下での差分の非増加性
lemma symmDiff_mono_under_NoSwap [DecidableEq α]
  (R : Finset (Rule α)) (hNS : NoSwap R)
  (U V : Finset α) (m k : ℕ) (f : α)
  (hk : let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
        D k = {f}) :
  let D := fun m => (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)
  ∀ m ≤ k, D m ⊆ {f} := by
  classical
  -- D を束縛
  let D : ℕ → Finset α :=
    fun n =>
      (parIter R U n \ parIter R V n) ∪
      (parIter R V n \ parIter R U n)

  -- ゴール：∀ m ≤ k, D m ⊆ {f}
  intro D m hm

  -- 「set … with hd」は使わず generalize にするのが安定
  generalize hdm : k - m = d
  -- d で帰納（m を generalizing）
  induction' d with d ih generalizing m

  -- base: d = 0 → k - m = 0 → m = k
  · intro DD hm
    have hk_le_m : k ≤ m := by exact Nat.le_of_sub_eq_zero hdm--Nat.sub_eq_zero.mp hdm
    have hm_eq : m = k := by (expose_names; exact Nat.le_antisymm hm_1 hk_le_m)--(le_antisymm hm hk_le_m).symm
    have hk' : D k = ({f} : Finset α) := by simpa [D] using hk
    subst hm_eq
    simp_all only [mem_singleton, le_refl, tsub_self, D]

  -- step: d.succ → d
  · intro DD hm
    -- hdm : k - m = d.succ ⇒ m < k
    have hlt : m < k := by
      have : k - m ≠ 0 := by
        rename_i D_2 hm_1
        simp_all only [subset_singleton_iff, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
          not_false_eq_true]

      apply  Nat.lt_of_le_of_ne
      rename_i D_2 hm_1
      simp_all only [subset_singleton_iff, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true]
      intro hh
      rw [hh] at this
      simp at this

    -- 算術整形：k - (m+1) = d
    have hdm1 : k - (m+1) = d := by
      have h : k - (m+1) = k - m - 1 := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using (Nat.sub_sub k m 1).symm
      simpa [hdm, Nat.succ_sub_one] using h

    -- 帰納仮説を m+1 に適用：D (m+1) ⊆ {f}

    have ih' : D (m+1) ⊆ ({f} : Finset α) := by
      -- ih : ∀ m, m ≤ k → k - m = d → D m ⊆ {f}
      -- hdm1 を渡す
      exact ih (m + 1) hlt hdm1

    -- NoSwap 一歩補題：D m ⊆ D (m+1) ∪ {f}
    --have hstep : D m ⊆ D (m+1) ∪ ({f} : Finset α) := by
      -- ここはあなたの補題に差し替え
    let isn := @in_symmDiff_ne_f_impossible _ _ _ _ _ _ R U V m f

    search_proof


        --(or.inr True.intro)
        --(x:=x) (hx:=hx) (hxf:=hxf)


    -- 合成して D m ⊆ {f}
    have :D (m + 1) ∪ {f} = {f} := by
      exact union_eq_right.mpr (ih (m + 1) hlt hdm1)

    have : D m ⊆ ({f} : Finset α) := by
      rw [this] at hstep
      exact hstep
    exact this hm
-/


/- これもなりたたないっぽい
-- メイン補題での使用
lemma input_symmDiff_singleton_of_syncEq
  {R : Finset (Rule α)} (hNTF : NoTwoFreshHeads R) (hNS : NoSwap R)
  {U V : Finset α}
  (hSync : syncCl R U = syncCl R V) :
  U = V ∨ ∃ f, (U \ V) ∪ (V \ U) = {f} := by
  classical
  have hED :=
    exists_singleton_lastDiff_of_syncEq_strong
      (R':=R) hNTF hNS (U:=U) (V:=V) hSync
  cases hED with
  | inl hUV =>
    exact Or.inl hUV
  | inr hK =>
    rcases hK with ⟨k, f, hkBound, hEqNext, hSingle⟩

    let D : Nat → Finset α := fun m =>
      (parIter R U m \ parIter R V m) ∪ (parIter R V m \ parIter R U m)

    have hDk : D k = {f} := by
      simpa [D] using hSingle

    -- 切り出した補題を使用
    have hMono : ∀ m, m ≤ k → D m ⊆ {f} := by
      apply symmDiff_mono_under_NoSwap R hNS U V k
      intro D_1
      simp_all only [D, D_1]

    have hD0_sub : D 0 ⊆ ({f} : Finset α) :=
      hMono 0 (Nat.zero_le _)

    by_cases hD0_empty : D 0 = ∅
    · left
      have : (U \ V) ∪ (V \ U) = (∅ : Finset α) := by
        simpa [D, parIter] using hD0_empty
      ext x
      constructor <;> intro hx <;> by_contra hcontra
      · have : x ∈ U \ V := Finset.mem_sdiff.mpr ⟨hx, hcontra⟩
        have : x ∈ (U \ V) ∪ (V \ U) := Finset.mem_union_left _ this
        rw [‹(U \ V) ∪ (V \ U) = ∅›] at this
        exact Finset.notMem_empty x this
      · have : x ∈ V \ U := Finset.mem_sdiff.mpr ⟨hx, hcontra⟩
        have : x ∈ (U \ V) ∪ (V \ U) := Finset.mem_union_right _ this
        rw [‹(U \ V) ∪ (V \ U) = ∅›] at this
        exact Finset.notMem_empty x this

    · right
      use f
      have hD0_nonempty : (D 0).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hD0_empty
      have hEq : D 0 = {f} := by
        have : ∀ x ∈ D 0, x = f := by
          intro x hx
          have : x ∈ ({f} : Finset α) := hD0_sub hx
          simpa using this
        obtain ⟨y, hy⟩ := hD0_nonempty
        have : y = f := this y hy
        rw [this] at hy
        ext x
        simp
        constructor
        · intro hx
          (expose_names; exact this_1 x hx)
        · intro hx
          rw [hx]
          exact hy
      simpa [D, parIter] using hEq

omit [DecidableEq α] [Fintype α] [LinearOrder α] in
/-- 上の補題をそのまま使える形（`t ∈ R` を引数に含める版）。 -/
lemma erased_cause_head_ne_thead'
  {R : Finset (Rule α)} {t r : Rule α}
  (hUC : UniqueChild α R) (ht : t ∈ R) (hrErase : r ∈ R.erase t) :
  r.head ≠ t.head := by
  classical
  have hrR : r ∈ R := mem_of_mem_erase hrErase
  intro hEq
  have : r = t := hUC hrR ht hEq
  exact ne_of_mem_erase hrErase this
-/
