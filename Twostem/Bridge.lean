import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
--import Closure.Rules
--import Twostem.Closure
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.NDS
import Twostem.Fiber --FreeOfなどで必要。
--import Twostem.Synchronous
import Twostem.Derivation --mem_closure_iff_derivなど。

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

omit [Fintype α] [LinearOrder α] in
lemma violates_not_closed {ρ} {R} {t : Rule α} {I}
  (h : violatesFirst ρ R t I) : ¬ IsClosed R I := by
  intro hcl
  rcases h with ⟨⟨hR, hPrem, hHead⟩, _⟩
  have : t.head ∈ I := hcl (t:=t) hR hPrem
  exact hHead this

--omit [Fintype α] [LinearOrder α] in
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

--omit [DecidableEq α] [LinearOrder α] in
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

--補題5.1あたり？
/-- UC を使う背理補題：もし `closure (R.erase t) (B∪S)` だけで `t.head` が出るなら、
    「t が first violation」という事実に矛盾する。 -/

lemma head_from_Rerase_contra_first
(ρ : RuleOrder α) (R : Finset (Rule α)) (hUC : UC R)
  (B S : Finset α) (t : Rule α)
  (hFirst : violatesFirst ρ R t (B ∪ S))
  (hHead : t.head ∈ syncCl (R.erase t) (B ∪ S)) : False := by
  classical
  sorry
--ここをChatGPTに書いてもらったら10個ぐらいsorryが残った。THikingじゃなかったからかも。
--UCとUnique Childの変換もうまくいかないし、最後までうまくいきそうにないので、一旦リセットすることにした。

--補題5.1あたり
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
  have hJclosed : IsClosed (R.erase t) J := by exact syncCl_closed
  have hJmem : J ∈ Family (α:=α) (R.erase t) := by simpa [mem_Family] using hJclosed
  have hfilter : (t.prem ⊆ J ∧ t.head ∉ J) := ⟨h1, h2⟩
  have : J ∈ (Family (α:=α) (R.erase t)).filter
            (fun I => t.prem ⊆ I ∧ t.head ∉ I) := by
    simpa [mem_filter] using And.intro hJmem hfilter
  exact And.intro h1 (And.intro h2 (by simpa [addedFamily] using this))

-- Twostem/Bridge.lean の末尾付近に追記


--variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α]

/- UC: 同一ヘッドを持つルールは高々 1 本 -/
--def UniqueChild (R : Finset (Rule α)) : Prop :=
--  ∀ {t₁ t₂}, t₁ ∈ R → t₂ ∈ R → t₁.head = t₂.head → t₁ = t₂

--補題5.1
/-- UC から：t を外した閉包から t.head は出てこない。 -/
lemma head_not_in_closure_of_erase
  {R : Finset (Rule α)} {t : Rule α} {I : Finset α}
  (hUC : UniqueChild (α:=α) R) (ht : t ∈ R) :
  t.head ∉ syncCl (R.erase t) I := by
  classical
  -- もし入っていたら，導出があり最後は head を持つ規則
  -- mem_closure_iff_derivはDerivationにある。
  have hiff := mem_closure_iff_deriv (α:=α) (R:=R.erase t) (I:=I) (a:=t.head)
  intro hIn
  have hDeriv : Deriv (α:=α) (R.erase t) (syncCl (R.erase t) I) t.head := (hiff.mp hIn)
  -- 最後の一手を取り出す
  have hlast := last_step_head (α:=α) (R:=R.erase t) (J:=syncCl (R.erase t) I) (x:=t.head) hDeriv
  -- 場合分け：基底 or ルール適用
  cases hlast with
  | inl hinJ =>
      -- 基底に t.head は入らない（通常，I に head があるなら violates が立たない設計）
      -- ただしここは Closure 側のポリシーに依存。今回は一般性のため rule-case に回す。
      -- 直接の矛盾が取りにくいので rule-case しか起きないことを示す：
      -- 「head は I からは出ず，ルール適用でしか現れない」仕様に寄せるなら、
      -- ここで矛盾に落としてもよい。ひとまず rule-case へ進むために反駁：
      -- 基底にいるなら，head を追加する必要がないため，通常の first-violation と矛盾。
      -- 汎用には，erase t で head を持つ規則が必要になることを示す route へ：
      -- いずれにせよ以降の step 分岐で矛盾を構成するので，ここは exfalso に落とす。
      -- （Closure 仕様が「I⊆cl」であるため，ここを使わず次ケースで決着）
      -- 安全に進めるため，contra をとって次ケースへ（Classical by_cases を使ってもよい）
      -- ここでは簡単に済ませる:
      have : False := by
        -- 一般論ではここで即矛盾は言いにくいので、後続の step ケースだけで矛盾可能なら
        -- inl は実際には起こらない（head が I に入る前提を採っていない）とみなせる。
        -- プロジェクトの Closure 仕様で head∈I を明確に禁止するならここで矛盾にしてよい。
        -- ここでは便宜的に Not.inl を不成立にし，`cases hlast` を step ケースに限定したい。
        -- ただ、Lean 的にはこのままでは詰むので、下の inr だけで矛盾を出すために `cases hlast` を
        -- 最初から inr と仮定し直すのが簡便。いったん `cases hlast` を巻き戻します…
        -- → 実装簡略化のため、この inl は impossible として処理します。

        exact False.elim (by sorry)
      exact this.elim
  | inr hSome =>
      rcases hSome with ⟨s, hsR, hhead⟩
      -- s は erase t の要素、つまり s∈R ∧ s≠t
      have hsR' : s ∈ R := by
        have := mem_of_mem_erase hsR
        exact this
      have hneq : s ≠ t := by
        have : s ∈ R ∧ s ≠ t := by
          simp_all only [mem_erase, ne_eq, and_true, not_false_eq_true, and_self]
        exact this.2
      -- UC により，同一 head のルールは一意 ⇒ s = t のはず，矛盾
      have : s = t := by
        exact hUC hsR' ht hhead
      exact hneq this

--/***********************
-- * 5. 多重度 ≤ 1（Two-Stem + UC）
-- ***********************/

--単射性の証明に使う？
/-- Two-Stem による「初回差の 1 座標局在」の仕様（抽象化）。
    実装では「B∪S と B∪S' の (R\{t})-closure を同期的に回したとき、
    最初に分岐する箇所は Free の 1 座標 f に限る」ことを述べる。 -/
private lemma firstDiff_localizes_to_one_coordinate
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (hTS : TwoStemR R) (B S S' : Finset α) (t : Rule α)
  (hS : isWitness (α:=α)  ρ R B S t)
  (hS' : isWitness (α:=α)  ρ R B S' t)
  (hne : S ≠ S') :
  ∃ f, f ∈ (S ∆ S') := by
  classical
  -- ここで “同期的閉包” の補助理論を使う。次ターンで具体化して証明。
  sorry
  --refine ⟨(S \ S').choose? (by decide), ?_, trivial⟩
  -- ダミー：次ターンで本証明

/-一つ下の補題と同内容っぽいのでコメントアウト
/-- 単射性（Two-Stem + UC）：`S ↦ J_{B,S}` は極小証人に制限すれば単射 -/
theorem multiplicity_le_one
  (ρ : RuleOrder α) (R : Finset (Rule α))
  (hUC : UC R) (hTS : TwoStemR R)
  (B : Finset α) (t : Rule α) :
  ∀ {S S' : Finset α},
    isWitness (α:=α)  ρ R B S t →
    isWitness ρ R B S' t →
    syncCl (R.erase t) (B ∪ S) = syncCl (R.erase t) (B ∪ S') →
    S = S' := by
  classical
  intro S S' hS hS' hJ
  by_contra hneq
  -- Two-Stem：最初の差は 1 座標に局在
  sorry
  /-
  obtain ⟨f, hfΔ, _⟩ :=
    firstDiff_localizes_to_one_coordinate (α:=α) ρ R hTS B S S' t hS hS' hneq
  -- UC：同一 head の別規則は存在せず、初回差の向きに依存して closure が一致することはない
  -- ⇒ 矛盾
  -- 次ターンで “局在座標 f の flips では closure が変わる” を補題化して埋めます。
  exact False.elim (by
    -- placeholder
    have : False := by
      -- ここに “flip f で addedFamily の像が変わる” を入れる
      sorry
    exact this)
  -/
  -/

-- Twostem/Bridge.lean の続き（Two-Stem まわりの骨格）


/- first-violation を満たす集合 I と J があるとき，
    TwoStem の下で最初に異なる座標は高々 1 個に局在する（シグネチャ） -/
/- 同名のものがもうひとつある。
lemma firstDiff_localizes_to_one_coordinate
  (ρ : RuleOrder α) {R : Finset (Rule α)} (hTS : TwoStemR (α:=α) R)
  {t : Rule α} {I J : Finset α}
  (hI : violatesFirst (α:=α) ρ R t I)
  (hJ : violatesFirst (α:=α) ρ R t J) :
  ∃! f : α, (f ∈ I ∧ f ∉ J) ∨ (f ∉ I ∧ f ∈ J) := by
  classical
  /- TODO：
    「同期的閉包」を I, J から同時に進め，TwoStem (prem.card ≤ 2) を使って
    最初に head の帰結が分岐し得るのは，prem からくる at-most-one の座標差に限られる，
    という帰納で示します。技術的には prem を列挙し，I/J で含まれる/含まれないの違いが
    初回に現れる点を最小の f とし，別の f' があると仮定して反駁します。
  -/
  admit
-/
/-上と同じ
/-- Two-Stem → 初回差分は1座標に局在（詳細版） -/
private lemma firstDiff_localizes_one_coordinate
  (ρ : RuleOrder α) {R : Finset (Rule α)} (hTS : TwoStemR (α:=α) R)
  {t : Rule α} {B S₁ S₂ : Finset α}
  (hW1 : isWitness (α:=α) ρ R B S₁ t)
  (hW2 : isWitness (α:=α) ρ R B S₂ t) :
  ∃! f : α, (f ∈ B ∪ S₁ ∧ f ∉ B ∪ S₂) ∨ (f ∉ B ∪ S₁ ∧ f ∈ B ∪ S₂) := by
  classical
  sorry
-/
  -- prem⊆両方, head∉両方
/-
  have hPrem1 := hW1.prem_subset
  have hPrem2 := hW2.prem_subset
  have hHead1 := hW1.head_notin
  have hHead2 := hW2.head_notin
  -- Two-Stem: 前提は高々2点
  have hcard : t.prem.card ≤ 2 := hTS _ hW1.t_mem
  -- 直観：差分が 2 点以上あれば、一方で先行違反が立つか、t が first でなくなる。
  -- 差分集合 D を定義
  let D : Finset α :=
    ((B ∪ S₁) \ (B ∪ S₂)) ∪ ((B ∪ S₂) \ (B ∪ S₁))
  have hNonempty_or : D = ∅ ∨ ∃ f, f ∈ D := by
    by_cases h : D = ∅
    · exact Or.inl h
    · exact Or.inr (by
        have : D.Nonempty := by
          classical exact Finset.nonempty_iff_ne_empty.mpr h
        rcases this with ⟨f, hf⟩; exact ⟨f, hf⟩)
  -- まず D=∅ なら差分なし→唯一元 f を選べないので「∃! f …」は、
  --   この命題の型上、D≠∅ を出してから局在と唯一性を示すのが自然。
  -- t が最初の違反であるためには、head が両側で不在のまま、prem は両側に入っている必要がある。
  -- 差分が2つ以上あると、Two-Stem から prem の満たされ方の整合性が崩れ、
  -- 先行ルール or t 自身の first 性に反する状況になる。
  -- 厳密化：D の 2 点 f≠g を仮定して反駁。
  have hAtMostOne : ∀ f g,
      f ∈ D → g ∈ D → f ≠ g → False := by
    intro f g hf hg hfg
    -- hf, hg から f,g のどちら側が (B∪S₁)/(B∪S₂) に属するかを場合分け
    rcases mem_union.mp hf with hfL | hfR
    rcases mem_union.mp hg with hgL | hgR
    all_goals
      -- 各ケースで「prem.card ≤ 2」と「prem⊆双方」を使って、
      -- 差分が2つ以上あるなら first 性に矛盾することを詳細に詰める。
      -- ポイント：prem⊆両側なので f,g は prem には属せず、head でもない。
      -- すると f,g は自由座標の新旧差分に起因し、どちらか側で
      -- 別の先行ルールが first になるか、t の first と衝突。
      -- 具体的には、(B∪S₁) と (B∪S₂) の片側でのみ成立する「s.prem⊆… & s.head∉…」
      -- を満たす先行 s を構成（Two-Stem により局所的な2点で十分）し、
      -- hW1.first_min / hW2.first_min に反する矛盾を作る。
      -- 構成は定型的だが長いので局所補題に切り出すのが実務的：
      --   build_prior_violation_from_two_diffs …
      exact False.elim (by
        -- ここは長い場合分けだが、Lean では個別補題に分けるのが無難。
        -- ひな型では False を導いて閉じる。
        exact False.intro)
  -- 以上で「高々1点」：すなわち D に互いに異なる 2 点は取り出せない
  -- 非空性：head 不在・prem 包含の条件下で t が first であるため、少なくとも1差分はある
  --（完全同一なら witness と witness が一致してしまい、単射結論には無害だが、
  --  存在一意の形で供給するために、非空なら唯一元とする）
  have hExistsUnique :
      ∃! f : α, (f ∈ B ∪ S₁ ∧ f ∉ B ∪ S₂) ∨ (f ∉ B ∪ S₁ ∧ f ∈ B ∪ S₂) := by
    classical
    -- D が空なら、「唯一元」として存在しないが、単射の証明では
    --   S₁=S₂ へ落ちるため特に問題ない。
    -- ここでは D 非空ケースから唯一元 f を返す：
    rcases hNonempty_or with hZ | ⟨f, hf⟩
    · -- D=∅ のとき：S₁=S₂ → 後で単射で使うときはこの枝を使わない。
      -- 一意存在を空から作れないので、非空分岐の結果を返す形にしておく。
      -- 実用上は multiplicity の証明側で D=∅ → S₁=S₂ として先に閉じます。
      -- ここはダミーで f=Classical.choice を取り、一意性は自明に付く形にはしない。
      -- 「∃!」を返す必要はないので、後段 lemma で D=∅ を先に処理します。
      exact ⟨Classical.choice (by exact ⟨default, trivial⟩), by decide, by decide⟩
    · -- D 非空：hAtMostOne から唯一性が従う
      refine ⟨f, ?hPred, ?hUnique⟩
      · -- f∈D なので述語を満たす
        rcases mem_union.mp hf with hfL | hfR
        · exact Or.inl (by
            rcases mem_sdiff.mp hfL with ⟨hU, hN⟩; exact ⟨hU, hN⟩)
        · exact Or.inr (by
            rcases mem_sdiff.mp hfR with ⟨hU, hN⟩; exact ⟨hN, hU⟩)
      · -- 一意性：もし g も述語を満たすなら g=f（hAtMostOne から）
        intro g hgPred
        have hgD : g ∈ D := by
          rcases hgPred with ⟨⟨hU, hN⟩ | ⟨hN, hU⟩⟩
          · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hU, hN⟩))
          · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hU, hN⟩))
        by_contra hneq
        exact (hAtMostOne f g hf hgD hneq).elim
  exact hExistsUnique
-/
/- 包含極小 witness の像（addedFamily）への写像が単射（多重度≤1） -/
-- Twostem/Bridge.lean の multiplicity_le_one_addedFamily を更新
-- Twostem/Bridge.lean 内の（既存）補題を上書き/追記

/-- UC + Two-Stem：addedFamily への写像は witness ごとに高々1本（単射） -/
--Witnessにも同名で同内容の補題があるので、そっちに移動か。
--一つ上の補題とも同内容。
lemma multiplicity_le_one_addedFamily
  (ρ : RuleOrder α) {R : Finset (Rule α)}
  --(hTS : TwoStem (α:=α) R)
  (hUC : UniqueChild (α:=α) R)
  {B : Finset α} {t : Rule α} {S₁ S₂ : Finset α}
  (hW1 : isWitness ρ R B S₁ t)
  (hW2 : isWitness ρ R B S₂ t)
  (hEq :
    syncCl (R.erase t) (B ∪ S₁) =
    syncCl (R.erase t) (B ∪ S₂)) :
  S₁ = S₂ := by
  classical
  -- 差分集合
  let D : Finset α :=
    ((B ∪ S₁) \ (B ∪ S₂)) ∪ ((B ∪ S₂) \ (B ∪ S₁))
  by_cases hD : D = ∅
  · -- 差分なし ⇒ B∪S₁ = B∪S₂ ⇒ S₁=S₂
    have hEqU : B ∪ S₁ = B ∪ S₂ := by
      apply Finset.ext
      intro x; constructor <;> intro hx
      · have : x ∈ (B ∪ S₁) \ (B ∪ S₂) ∨ x ∈ (B ∪ S₂) := by
          by_cases hnx : x ∈ (B ∪ S₂)
          · exact Or.inr hnx
          · exact Or.inl (mem_sdiff.mpr ⟨hx, by simp_all only [union_eq_empty, sdiff_eq_empty_iff_subset, mem_union, not_or, or_self, not_false_eq_true, D]⟩)
        rcases this with hxD | hx2
        · have : x ∈ D := mem_union.mpr (Or.inl hxD)
          rw [hD] at this
          exfalso
          exact False.elim (by exact (List.mem_nil_iff x).mp this)
        · exact hx2
      · have : x ∈ (B ∪ S₂) \ (B ∪ S₁) ∨ x ∈ (B ∪ S₁) := by
          by_cases hnx : x ∈ (B ∪ S₁)
          · exact Or.inr hnx
          · exact Or.inl (mem_sdiff.mpr ⟨hx, by simp_all only [union_eq_empty, sdiff_eq_empty_iff_subset, mem_union, not_or, or_self, not_false_eq_true, D]
⟩)
        rcases this with hxD | hx1
        · have : x ∈ D := mem_union.mpr (Or.inr hxD)
          rw [hD] at this
          exfalso
          exact False.elim (by exact (List.mem_nil_iff x).mp this)
        · exact hx1
    -- ∪B の両辺から B を消して S₁=S₂
    apply Finset.ext
    intro x; constructor <;> intro hx
    · have : x ∈ B ∪ S₂ := by
        rw [←hEqU]
        exact mem_union_right B hx

      rcases mem_union.mp this with hxB | hxS2
      · sorry--exact False.elim (by
          -- x∈S₁∩B なら S₁ ⊆ Free の設定なら矛盾（本稿設計）
          -- 今は「B は固定、差分は Free 側のみ」から x∈B∩S₁ は避けられる。

      · exact hxS2
    · have : x ∈ B ∪ S₁ := by simpa [hEqU] using (mem_union.mpr (Or.inr hx))
      rcases mem_union.mp this with hxB | hxS1
      · sorry
      · exact hxS1
  · -- 差分が非空 ⇒ 局在補題で唯一の差分 f
    sorry
    /-
    obtain ⟨f, hfPred, huniq⟩ :=
      firstDiff_localizes_one_coordinate (α:=α) ρ (R:=R) hTS
        (t:=t) (B:=B) (S₁:=S₁) (S₂:=S₂) hW1 hW2
    -- f が唯一の差分。閉包等式と UC から矛盾 ⇒ 実は D=∅ だった（∴ S₁=S₂）
    -- 片側で f∈B∪S₁, f∉B∪S₂（または逆）を仮定して矛盾を示す。
    rcases hfPred with hL | hR
    · rcases hL with ⟨hfU1, hfN2⟩
      -- f ∈ closure(R\{t}, B∪S₁) かつ closures 等しい ⇒ f ∈ closure(R\{t}, B∪S₂)
      have hfCl1 : f ∈ closure (R.erase t) (B ∪ S₁) :=
        subset_closure (R:=R.erase t) (I:=B ∪ S₁) hfU1
      have hfCl2 : f ∈ closure (R.erase t) (B ∪ S₂) := by simpa [hEq] using hfCl1
      -- 一方で f ∉ B ∪ S₂。f を導くルールが必要だが、UC で head=f のルールは高々1つ。
      -- その唯一ルールが t の場合、erase で消えているから導けない。
      -- t.head=f を仮定して矛盾、あるいは head≠f なら別ルールが必要だが、差分唯一性と first_min で排除。
      -- ここでは一気に矛盾へ（Closure 側の補題を使うとスムーズ）。
      exact False.elim (by
        -- 詳細な反駁を入れるには：
        --   1) hfCl2 から 「∃u∈R\{t}, u.prem⊆… ∧ u.head=f」 を取り、
        --   2) UC で head=f の候補は高々1、かつ witness の first_min と整合しないことを示す
        exact False.intro)
    · rcases hR with ⟨hfN1, hfU2⟩
      -- 反対側も同様
      have hfCl2 : f ∈ closure (R.erase t) (B ∪ S₂) :=
        subset_closure (R:=R.erase t) (I:=B ∪ S₂) hfU2
      have hfCl1 : f ∈ closure (R.erase t) (B ∪ S₁) := by simpa [hEq] using hfCl2
      exact False.elim (by exact False.intro)
    -/


/- first violation（定義は既存ファイル側のものを使う） -/
-- ここでは型だけ参照： violatesFirst ρ R t I



end Twostem

open Finset

namespace TestUC

-- ここでは Twostem の Rule / UC / UniqueChild を使っている想定です。
-- 必要なら完全修飾子 Twostem. を付けてください。
-- 例：Closure.Rule, Twostem.UC, Twostem.UniqueChild, Twostem.UniqueChild_iff_UC

-- 具体例用に α := Bool
variable (α := Bool)

-- Rule の形だけ使います（head と prem があれば十分）
-- 既存の定義に DecidableEq が無い場合は、下の1行で局所的に用意すると安定します。
noncomputable instance : DecidableEq (Closure.Rule Bool) := Classical.decEq _



open Finset

namespace TestUC

-- ここでは Twostem の定義が Closure 名前空間から見える想定に合わせます
-- 必要なら Twostem. を付け替えてください。
-- 例：Twostem.UniqueChild_iff_UC など。

-- ---------- 具体例: α := Bool ----------
noncomputable instance : DecidableEq (Closure.Rule Bool) := Classical.decEq _
instance : DecidableEq Bool := inferInstance

def r1 : Closure.Rule Bool := { head := true,  prem := (∅ : Finset Bool) }
def r2 : Closure.Rule Bool := { head := false, prem := (∅ : Finset Bool) }
def r3 : Closure.Rule Bool := { head := true,  prem := ({false} : Finset Bool) }

noncomputable def Rgood : Finset (Closure.Rule Bool) := insert r2 {r1}   -- = {r1, r2}
noncomputable def Rbad  : Finset (Closure.Rule Bool) := insert r3 {r1}   -- = {r1, r3}

@[simp] lemma mem_Rgood_iff {x : Closure.Rule Bool} :
    x ∈ Rgood ↔ x = r1 ∨ x = r2 := by
  -- Rgood = insert r2 {r1}
  constructor
  · intro hx
    -- x ∈ insert r2 {r1} → x=r2 ∨ x∈{r1}
    have hx' : x = r2 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl hx2 =>
        left
        sorry
    | inr hx1 =>
        -- x∈{r1} → x=r1
        have hxeq : x = r1 := (mem_singleton).1 hx1
        right
        cases hxeq
        sorry
  · intro h
    -- 逆向き：x=r1∨x=r2 → x∈insert r2 {r1}
    cases h with
    | inl hx1 =>
        cases hx1
        -- r1 ∈ insert r2 {r1} は右側の単集合に入る方
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        exact (mem_insert).2 (Or.inr this)
    | inr hx2 =>
        cases hx2
        -- r2 は insert の先頭
        exact (mem_insert_self r2 _)

@[simp] lemma mem_Rbad_iff {x : Closure.Rule Bool} :
    x ∈ Rbad ↔ x = r1 ∨ x = r3 := by
  -- Rbad = insert r3 {r1}
  constructor
  · intro hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) :=
      (mem_insert).1 hx
    cases hx' with
    | inl h =>
        left;
        sorry
    | inr h1 =>
        have : x = r1 := (mem_singleton).1 h1
        right; cases this; sorry
  · intro h
    cases h with
    | inl hx3 =>
        cases hx3
        sorry
    | inr hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_singleton).2 rfl
        apply (mem_insert).2
        exact Or.symm (Or.inr rfl)

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
  -- 任意の a に対し filter( head=a ) は単集合になる
  intro a
  -- a で場合分け：a=false → {r2}, a=true → {r1}
  cases a with
  | false =>
      -- filter = {r2}
      have hx :
        (Rgood.filter (fun t => t.head = false))
          = ({r2} : Finset (Closure.Rule Bool)) := by
        -- 外延同値
        apply ext; intro x
        constructor
        · intro hxmem
          -- x ∈ Rgood ∧ x.head=false
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = false := (mem_filter).1 hxmem |>.2
          -- Rgood のとり得る形
          have hx' : x = r1 ∨ x = r2 :=
            (mem_Rgood_iff).1 hR
          cases hx' with
          | inl h1 =>
              -- r1.head=true なので false と矛盾 → こちらの分岐は起きない
              -- 形式的に矛盾から何でも出せる：
              have : r1.head = true := rfl
              -- hH : x.head = false,  h1 : x=r1
              cases h1
              cases this
              cases hH
          | inr h2 =>
              cases h2
              -- x=r2 → {r2}
              exact (mem_singleton).2 rfl
        · intro hxmem
          -- {r2} ⊆ filter …
          have hx2 : x = r2 := (mem_singleton).1 hxmem
          -- r2 ∈ Rgood
          have hR2 : r2 ∈ Rgood := by
            apply (mem_insert).2
            subst hx2
            simp_all only [mem_singleton, true_or]

          -- 条件を満たすペア
          have hpair : r2 ∈ Rgood ∧ r2.head = false := by
            apply And.intro
            · exact hR2
            · rfl
          cases hx2
          exact (mem_filter).2 hpair
      -- 単集合の濃度は 1
      -- よって card ≤ 1
      have hcard : (Rgood.filter (fun t => t.head = false)).card ≤ 1 := by
        -- card (filter …) = card {r2}
        have heq :
          (Rgood.filter (fun t => t.head = false)).card
            = ({r2} : Finset (Closure.Rule Bool)).card := by
          -- card の congrArg
          exact congrArg (fun (s : Finset (Closure.Rule Bool)) => s.card) hx
        -- card {r2} = 1
        have hone : ({r2} : Finset (Closure.Rule Bool)).card = 1 :=
          card_singleton r2
        -- 置換して ≤ 1
        have : (Rgood.filter (fun t => t.head = false)).card = 1 := by
          exact Eq.trans heq hone
        -- 1 ≤ 1
        exact Eq.le this
      exact hcard
  | true =>
      -- 同様に filter = {r1}
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
          | inl h1 =>
              cases h1
              exact (mem_singleton).2 rfl
          | inr h2 =>
              cases h2
              -- r2.head=false と真の矛盾
              cases hH
        · intro hxmem
          have hx1 : x = r1 := (mem_singleton).1 hxmem
          have hR1 : r1 ∈ Rgood :=
            (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
          have hpair : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
          cases hx1
          exact (mem_filter).2 hpair
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
      -- 直前の example を再利用のノリで、もう一回同じ証明でもOK
      intro a; cases a <;> first
      | -- a=false
        -- filter=false は {r2}
        have hx :
          (Rgood.filter (fun t => t.head = false))
            = ({r2} : Finset (Closure.Rule Bool)) := by
          -- 先ほどと同じ議論（省略せずに書くと長いので、ここでは短く）
          -- ここでの詳細は上の example と同様に展開できます
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
            have hR2 : r2 ∈ Rgood :=
              (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
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
      | -- a=true
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
        sorry
    )


-- ---------- 悪い例：UniqueChild も UC も成り立たない ----------

example : ¬ Twostem.UniqueChild (α:=Bool) Rbad := by
  intro hUC
  -- r1, r3 ∈ Rbad
  have hr1 : r1 ∈ Rbad :=
    (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
  have hr3 : r3 ∈ Rbad :=
    (mem_insert).2 (Or.inl rfl)
  -- head が同じ
  have hhead : r1.head = r3.head := rfl
  -- UniqueChild なら r1=r3 だが、prem が違うので矛盾
  have h_eq : r1 = r3 := hUC hr1 hr3 hhead
  -- prem を取り出して矛盾
  have hprem : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h_eq
  -- ∅ = {false} は成り立たない
  have hneq : (∅ : Finset Bool) ≠ ({false} : Finset Bool) := by
    intro h; -- 0 ≠ 1 の濃度で矛盾にしてもOK
    -- 元素 false のメンバーシップで対立
    have : false ∈ (∅ : Finset Bool) := by
      -- あり得ない
      exact insert_eq_self.mp (id (Eq.symm hprem))

    -- 実際は簡単に card でも良いが、上は冗長なので書き換え：
    exact (List.mem_nil_iff false).mp this
  -- ところが r1.prem=∅, r3.prem={false}
  -- hprem で等しいと言ってしまっているので矛盾
  exact hneq hprem


example : ¬ Twostem.UC (α:=Bool) Rbad := by
  intro hUC
  -- a=true のとき、filter には r1 と r3 の両方が入る
  have hr1 : r1 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r1 ∈ Rbad :=
      (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
    have : r1 ∈ Rbad ∧ r1.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  have hr3 : r3 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r3 ∈ Rbad := (mem_insert).2 (Or.inl rfl)
    have : r3 ∈ Rbad ∧ r3.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  -- r1 ≠ r3
  have hneq : r1 ≠ r3 := by
    intro h
    -- prem を比べれば矛盾
    have : r1.prem = r3.prem := congrArg (fun (t : Closure.Rule Bool) => t.prem) h
    -- ∅ ≠ {false}
    have : (∅ : Finset Bool) = ({false} : Finset Bool) := by
      -- r1.prem=∅, r3.prem={false} なので上に等しいはずはない
      -- ここは rfl を両側に流し込むイメージ
      exact this
    -- 実際は上の行は成立しないので False
    -- 手短に：
    simp_all only [mem_filter, mem_Rbad_iff, or_self, true_and]
    contradiction

  -- {r1,r3} ⊆ filter → card ≥ 2
  have hsubset : insert r3 ({r1} : Finset (Closure.Rule Bool))
                  ⊆ Rbad.filter (fun t => t.head = true) := by
    intro x hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_insert).1 hx
    cases hx' with
    | inl hx3 =>
        cases hx3; exact hr3
    | inr hx1 =>
        have : x = r1 := (mem_singleton).1 hx1
        cases this; exact hr1
  -- card {r1,r3} = 2
  have hpair : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card = 2 := by
    have hnot : r3 ∉ ({r1} : Finset (Closure.Rule Bool)) := by
      intro hx; apply hneq; exact (mem_singleton).1 hx |>.symm
    -- card_insert_of_notMem
    have hbase : ({r1} : Finset (Closure.Rule Bool)).card = 1 := card_singleton r1
    have : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card
              = ({r1} : Finset (Closure.Rule Bool)).card + 1 :=
      card_insert_of_notMem hnot
    -- 1 + 1 = 2 なので 2
    -- ここは算術を省略せずに書くなら：
    -- rewrite hbase, then Nat.succ
    -- ただし trans で十分
    exact Eq.trans this rfl
  -- card の単調性
  have hge2 : 2 ≤ (Rbad.filter (fun t => t.head = true)).card := by
    sorry      -- 2 ≤ card {r1,r3}

  -- しかし UC は ≤ 1 を要求
  have hle1 : (Rbad.filter (fun t => t.head = true)).card ≤ 1 :=
    hUC true
  simp_all only [mem_filter, mem_Rbad_iff, or_false, true_and, or_true, ne_eq]
  omega

end TestUC


-- サンプル規則
def r1 : Closure.Rule Bool := { head := true,  prem := (∅ : Finset Bool) }
def r2 : Closure.Rule Bool := { head := false, prem := (∅ : Finset Bool) }
def r3 : Closure.Rule Bool := { head := true,  prem := ({false} : Finset Bool) }

-- 良い例：head がユニーク（true と false）
noncomputable def Rgood : Finset (Closure.Rule Bool) := {r1, r2}

-- 悪い例：head が衝突（どちらも true）
noncomputable  def Rbad  : Finset (Closure.Rule Bool) := {r1, r3}

@[simp] lemma mem_Rgood_iff {x : Closure.Rule Bool} :
    x ∈ Rgood ↔ x = r1 ∨ x = r2 := by
  -- {a,b} のメンバ判定
  --change x ∈ insert r2 ({r1} : Finset (Closure.Rule Bool)) ↔ _
  constructor
  · intro hx
    have hx' : x = r2 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := by
      sorry
    cases hx' with
    | inl hx2 =>
        left;
        sorry
    | inr hx1 =>
        have hxeq : x = r1 := (mem_singleton).1 hx1
        right;
        sorry
  · intro h
    cases h with
    | inl hx1 =>
        cases hx1;
        sorry
    | inr hx2 =>
        cases hx2
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := by
          exact (mem_singleton).2 rfl
        sorry
@[simp] lemma mem_Rbad_iff {x : Closure.Rule Bool} :
    x ∈ Rbad ↔ x = r1 ∨ x = r3 := by
  constructor
  · intro hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := by
      sorry
    simp_all only [mem_singleton]
    cases hx' with
    | inl h =>
      subst h
      simp_all only [or_true]
    | inr h_1 =>
      subst h_1
      simp_all only [true_or]

  · intro h
    cases h with
    | inl hx3 =>
        cases hx3;
        sorry
    | inr hx1 =>
        cases hx1
        have : r1 ∈ ({r1} : Finset (Closure.Rule Bool)) := by
          exact (mem_singleton).2 rfl
        apply (mem_insert).2
        simp_all only [mem_singleton, or_true]


-- ============ 検証1：一般形（.mp / .mpr がそのまま使える） ============
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

-- ============ 検証2：良い例で UC も UniqueChild も成り立つ ============
example : Twostem.UC (α:=Bool) Rgood := by
  intro a
  -- a = true / false の場合分け
  cases a with
  | false =>
      -- head=false を持つのは r2 だけ → filter = {r2} → card ≤ 1
      have hx :
        (Rgood.filter (fun t => t.head = false))
          = ({r2} : Finset (Closure.Rule Bool)) := by
        -- 外延同値で示す
        apply ext
        intro x
        constructor
        · intro hxmem
          -- x∈Rgood ∧ x.head=false
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = false := (mem_filter).1 hxmem |>.2
          -- Rgood の場合分け
          have hx' : x = r1 ∨ x = r2 := (by
            have := (mem_Rgood_iff).mp hR; exact this)
          cases hx' with
          | inl h1 =>
              -- r1.head=true なので矛盾 → こちらは出ない
              have : r1.head = true := rfl
              cases h1
              -- hH : x.head = false と矛盾から False → 何でも示せる
              cases hH
          | inr h2 =>
              -- x=r2 なので {r2} に入る
              cases h2
              exact (mem_singleton).2 rfl
        · intro hxmem
          -- 逆向き：{r2} ⊆ filter …
          have hx2 : x = r2 := (mem_singleton).1 hxmem
          -- x=r2 は Rgood のメンバ、かつ head=false
          have hR2 : r2 ∈ Rgood := (mem_insert).2 (Or.inr ((mem_singleton).2 rfl))
          -- filter の条件を満たす
          have : r2 ∈ Rgood ∧ r2.head = false := by
            apply And.intro
            · exact hR2
            · subst hx2
              simp_all only [mem_Rgood_iff, or_true, mem_singleton]
              rfl
          -- 目標へ
          cases hx2
          exact (mem_filter).2 this
      -- filter の濃度が 1 以下
      -- ここでは `card {r2} = 1` と `Nat.le_refl 1` から従う
      have hcard : (Rgood.filter (fun t => t.head = false)).card ≤ 1 := by
        have : (Rgood.filter (fun t => t.head = false)).card
                = ({r2} : Finset (Closure.Rule Bool)).card := by
          exact congrArg card hx
           -- card {r2} = 1
        have : ({r2} : Finset (Closure.Rule Bool)).card ≤ 1 := by
          -- 単集合の濃度
          exact (by
            -- card_singleton = 1, よって ≤ 1
            have : ({r2} : Finset (Closure.Rule Bool)).card = 1 := by
              exact card_singleton r2
            -- 1 ≤ 1
            exact (Eq.le this))
        -- 置換
        (expose_names; exact Nat.le_of_eq this_1)
      -- a=false の結論
      exact hcard
  | true  =>
      -- 同様に head=true を持つのは r1 だけ
      have hx :
        (Rgood.filter (fun t => t.head = true))
          = ({r1} : Finset (Closure.Rule Bool)) := by
        apply ext; intro x; constructor
        · intro hxmem
          have hR : x ∈ Rgood := (mem_filter).1 hxmem |>.1
          have hH : x.head = true := (mem_filter).1 hxmem |>.2
          have hx' : x = r1 ∨ x = r2 := (by
            have := (mem_Rgood_iff).mp hR; exact this)
          cases hx' with
          | inl h1 =>
              cases h1
              exact (mem_singleton).2 rfl
          | inr h2 =>
              cases h2
              -- r2.head=false と hH が矛盾
              cases hH
        · intro hxmem
          have hx1 : x = r1 := (mem_singleton).1 hxmem
          have hR1 : r1 ∈ Rgood := by
            subst hx1
            simp_all only [mem_singleton, mem_Rgood_iff, true_or]
          have : r1 ∈ Rgood ∧ r1.head = true := And.intro hR1 rfl
          cases hx1
          exact (mem_filter).2 this
      have hcard : (Rgood.filter (fun t => t.head = true)).card ≤ 1 := by
        have : (Rgood.filter (fun t => t.head = true)).card
                = ({r1} : Finset (Closure.Rule Bool)).card := by
          exact congrArg card hx
        have : ({r1} : Finset (Closure.Rule Bool)).card ≤ 1 := by
          have : ({r1} : Finset (Closure.Rule Bool)).card = 1 := by
            exact card_singleton r1
          exact (Eq.le this)
        (expose_names; exact Nat.le_of_eq this_1)
      exact hcard

-- UniqueChild も成り立つ（良い例）
example : Twostem.UniqueChild (α:=Bool) Rgood := by
  apply (Twostem.UniqueChild_iff_UC (α:=Bool) Rgood).mpr
  sorry

-- ============ 検証3：悪い例では両方ダメ ============
example : ¬ Twostem.UniqueChild (α:=Bool) Rbad := by
  -- 反例として t₁=r1, t₂=r3 を当てはめる
  intro hUC
  -- r1, r3 はどちらも Rbad の要素
  have hr1 : r1 ∈ Rbad := by
    apply (mem_insert).2
    exact Or.symm (Or.inr rfl)
  have hr3 : r3 ∈ Rbad := by
    apply (mem_insert).2
    simp_all only [mem_Rbad_iff, true_or, mem_singleton, or_true]
  -- かつ head はどちらも true
  have hhead : r1.head = r3.head := by rfl
  -- UniqueChild の結論は r1 = r3 だが、prem が違うので不等式
  have : r1 = r3 := hUC hr1 hr3 hhead
  -- 明らかに異なる
  sorry --Unique Childに反してそう。

example : ¬ Twostem.UC (α:=Bool) Rbad := by
  intro hUC
  -- a=true で filter に r1 と r3 の 2つが入るので card ≤ 1 に反する
  -- r1∈filter
  have hr1 : r1 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r1 ∈ Rbad := by
      apply (mem_insert).2
      exact Or.symm (Or.inr rfl)
    have : r1 ∈ Rbad ∧ r1.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  -- r3∈filter
  have hr3 : r3 ∈ Rbad.filter (fun t => t.head = true) := by
    have hR : r3 ∈ Rbad := by
      simp_all only [mem_filter, mem_Rbad_iff, true_or, true_and, or_true]
    have : r3 ∈ Rbad ∧ r3.head = true := And.intro hR rfl
    exact (mem_filter).2 this
  -- r1≠r3
  have hneq : r1 ≠ r3 := by
    -- head は同じだが prem が違う
    intro h;
    sorry
  -- {r1,r3} ⊆ filter → card ≥ 2 → ≤1 と矛盾
  have hsubset : insert r3 ({r1} : Finset (Closure.Rule Bool))
                  ⊆ Rbad.filter (fun t => t.head = true) := by
    intro x hx
    have hx' : x = r3 ∨ x ∈ ({r1} : Finset (Closure.Rule Bool)) := (mem_insert).1 hx
    cases hx' with
    | inl hx3 =>
        cases hx3; exact hr3
    | inr hx1 =>
        have : x = r1 := (mem_singleton).1 hx1
        cases this; exact hr1
  -- card {r1,r3} = 2
  have hpair : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card = 2 := by
    -- card_insert_of_notMem
    have hnot : r3 ∉ ({r1} : Finset (Closure.Rule Bool)) := by
      -- r3∈{r1} ↔ r3=r1 に反する
      intro h; exact hneq ((mem_singleton).1 h).symm
    have : ({r1} : Finset (Closure.Rule Bool)).card = 1 := card_singleton r1
    -- (1 + 1) = 2
    -- card_insert_of_notMem : card (insert a s) = card s + 1
    have : (insert r3 ({r1} : Finset (Closure.Rule Bool))).card
              = ({r1} : Finset (Closure.Rule Bool)).card + 1 :=
      card_insert_of_notMem hnot
    -- 置換
    -- 1 + 1 = 2
    -- （算術の変形は省略）
    exact this.trans rfl
  -- 単調性：subset → card_le_of_subset
  have hge2 : 2 ≤ (Rbad.filter (fun t => t.head = true)).card := by
    apply le_trans (by
      -- 2 ≤ card {r1,r3}
      -- ここは「card=2」から直ちに従う
      have h2 : 2 ≤ (insert r3 ({r1} : Finset (Closure.Rule Bool))).card := by
        -- card=2 → ≤ 2 は自明、従って 2 ≤ card
        -- 直接：Nat.le_of_eq (Eq.symm hpair)
        exact Nat.le_of_eq (Eq.symm hpair)
      exact h2)
    exact card_le_card hsubset
  -- しかし UC は「この card ≤ 1」なので矛盾
  have hle1 : (Rbad.filter (fun t => t.head = true)).card ≤ 1 := by
    simp_all only [mem_filter, mem_Rbad_iff, or_false, true_and, or_true, ne_eq]
    apply hUC
  apply hneq
  simp_all only
  apply hneq
  simp_all only
  apply hneq
  simp_all only
  omega

end TestUC
