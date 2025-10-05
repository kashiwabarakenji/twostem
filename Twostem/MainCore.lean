import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Order.SymmDiff
import Twostem.Closure.Abstract
import Twostem.Closure.Core
import Twostem.Closure.Sync
--import Twostem.Synchronous
--import Twostem.Derivation --mem_closure_iff_derivなど。

namespace Twostem

open Closure
open Finset

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] [DecidableEq (Rule α)]



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



--分岐専用補題ではないという判断。
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

--omit [DecidableEq α] [Fintype α] [LinearOrder α] in
@[simp] lemma result_right_impossible
  --[DecidableEq α] [Fintype α] [LinearOrder α]
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
            -- U を引数にもつ syncCl の等式に持ち上げる
            have hHead' : t.head ∈ syncCl (R.erase t) (B ∪ S₁) := by
              simpa [hU] using this
            convert hHead'
            )

  exact Eq.mpr_not (congrArg (Membership.mem X) hr_head) hf_notinX



--使われている。
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
    (hHead  := by convert hthead_in_syncUS1)

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
    (hHead  := by convert this)


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

---OnlyTLastDiff.head_eq_of_symmDiff_singletonを使うと短く証明がかけるらしい。
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
              convert hHeadIn)
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
                convert hHeadIn)
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
