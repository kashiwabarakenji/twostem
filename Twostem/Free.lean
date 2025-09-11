import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Int
import Twostem.General
import Twostem.Basic
import Twostem.ProblemCC
import Twostem.ProblemC
import LeanCopilot

--微妙に使っている。

open scoped BigOperators
open ThreadC_Fiber
open Finset
universe u
variable {α : Type u} [DecidableEq α]

lemma NDS2_nonpos_when_rules_empty
  {α : Type u} [DecidableEq α]
  (V : Finset α) :
  NDS2 V (family V (∅ : Finset (Rule α))) ≤ 0 := by
  -- 既存: NDS2_family_empty_zero : NDS2 V (family V ∅) = 0
  have h0 : NDS2 V (family V (∅ : Finset (Rule α))) = 0 :=
    NDS2_family_empty_zero (V := V)
  -- =0 ⇒ ≤0
  exact le_of_eq h0

/-- V=∅ かつ supportedOn V R なら R=∅。 -/
lemma rules_empty_of_supportedOn_and_V_empty
  {α : Type u} [DecidableEq α]
  (R : Finset (Rule α))
  (hV : supportedOn (∅ : Finset α) R) :
  R = ∅ := by
  classical
  by_contra hne
  obtain ⟨t, ht⟩ := Finset.nonempty_of_ne_empty hne
  have h := hV (by exact ht)
  rcases h with ⟨h1, _, _⟩
  -- h1 : t.1 ∈ ∅ の矛盾
  exact (by exact (List.mem_nil_iff t.1).mp h1 )

/-- ★ R=∅ を仮定形で受け取る版（メインから使い勝手が良い） -/
lemma hRempty
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  --(hV : supportedOn V R)
  (hR : R = ∅) :
  NDS2 V (family V R) ≤ 0 := by
  -- R=∅ へ書き換え
  have : NDS2 V (family V R) = NDS2 V (family V (∅ : Finset (Rule α))) := by
    -- ただの置換
    -- family V R = family V ∅ を R=∅ で書き換え
    -- 「simpa using」を使わず、`rw` 一発
    rw [hR]
  -- 右を ≤0 に落とす
  have hle : NDS2 V (family V (∅ : Finset (Rule α))) ≤ 0 :=
    NDS2_nonpos_when_rules_empty (V := V)
  -- 連結
  exact (by
    -- `NDS2 V (family V R) ≤ 0` を出したい
    -- まず `NDS2 V (family V R) = ...` を置換
    --   (= ...) ≤ 0 へ
    -- `calc` で丁寧に
    calc
      NDS2 V (family V R)
          = NDS2 V (family V (∅ : Finset (Rule α))) := by exact this
      _ ≤ 0 := by exact hle)


lemma V_nonempty_of_supported_of_ne_empty
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hne : R ≠ ∅) :
  V.Nonempty := by
  classical
  -- R から1本とる
  have : ∃ t, t ∈ R := by
    contrapose! hne
    ext a : 1
    simp_all only [Finset.notMem_empty]

  rcases this with ⟨t, htR⟩
  -- supportedOn から t の各成分は V に入る
  have htV := hV (by exact htR)
  rcases htV with ⟨ha, hb, hr⟩
  -- 例えば t.1 ∈ V を使って V.Nonempty
  exact ⟨t.1, ha⟩

lemma image_const_eq_singleton_of_nonempty
  {α : Type u} [DecidableEq α]
  (V : Finset α) (x : α) (h : V.Nonempty) :
  V.image (fun _ : α => x) = ({x} : Finset α) := by
  classical
  -- 包含両方向
  exact Finset.image_const h x

/-- ★ メイン：`R≠∅` のとき Free を必ず非空にできる SCCQuot を構成（rep を定数化） -/
noncomputable def buildSCCQuot_with_free
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hne : R ≠ ∅) :
  SCCQuot α V R :=
by
  classical
  -- choose t ∈ R
  let t := (Finset.nonempty_of_ne_empty hne).choose
  let ht := (Finset.nonempty_of_ne_empty hne).choose_spec
  -- x0 := t.1 ∈ V
  have h_supp := by (expose_names; exact α_1) --hV t ht
  let x0 : α := t.1
  have hx0V : x0 ∈ V := by
    dsimp [supportedOn] at hV
    simp_all only [Prod.forall, x0, t]
    exact (hV _ _ _ ht).1
  -- 定義：β=ULift Unit, π≡(), σ≡x0
  let β := ULift Unit  -- 型注釈なし → 型推論に任せる（安全）
  let π : α → β := fun _ => ULift.up ()
  let σ : β → α := fun _ => x0
  have hσV : ∀ b : β, σ b ∈ V := fun _ => hx0V
  have βdec : DecidableEq β := inferInstance
  exact { β := β, βdec := βdec, π := π, σ := σ, σ_in_V := hσV }



lemma Rep_eq_singleton_for_build
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hne : R ≠ ∅) :
  ∃ x0 ∈ V,
    Rep  (Q := buildSCCQuot_with_free (α := α) V R hV hne) = ({x0} : Finset α) := by
  classical
  -- 取り出した x0
  let t := (Finset.nonempty_of_ne_empty hne).choose
  let ht := (Finset.nonempty_of_ne_empty hne).choose_spec
  rcases hV (by exact ht) with ⟨hx0, _, _⟩
  let x0 : α := t.1
  have hx0V : x0 ∈ V := hx0
  -- V 非空
  have hVne : V.Nonempty :=
    V_nonempty_of_supported_of_ne_empty (V := V) (R := R) hV hne
  -- rep は定数 x0 ⇒ Rep = V.image (const x0) = {x0}
  have : Rep (Q := buildSCCQuot_with_free (α := α) V R hV hne)
            = V.image (fun _ : α => x0) := by rfl
  have himg : V.image (fun _ : α => x0) = ({x0} : Finset α) :=
    image_const_eq_singleton_of_nonempty (V := V) (x := x0) (h := hVne)
  refine ⟨x0, hx0V, ?_⟩
  -- 連結
  calc
    Rep (Q := buildSCCQuot_with_free V R hV hne)
        = V.image (fun _ : α => x0) := by rfl
    _   = ({x0} : Finset α) := by exact himg

/-- `x0 ∈ V` かつ `2 ≤ |V|` なら `V.erase x0` は非空。 -/
lemma erase_nonempty_of_card_ge_two
  {α : Type u} [DecidableEq α]
  {V : Finset α} {x0 : α}
  (hx0V : x0 ∈ V) (h2 : 2 ≤ V.card) :
  (V.erase x0).Nonempty := by
  classical
  by_contra h
  -- V ⊆ {x0}
  have V_subset_singleton : V ⊆ ({x0} : Finset α) := by
    intro y hyV
    by_contra hneq
    have hneq':y ≠ x0 := by exact List.ne_of_not_mem_cons hneq
    have : y ∈ V.erase x0 := mem_erase.mpr ⟨hneq', hyV⟩
    exact h ⟨y, this⟩
  -- {x0} ⊆ V は自明
  have incl₂ : ({x0} : Finset α) ⊆ V := by
    intro y hy
    cases mem_singleton.mp hy
    exact hx0V
  -- よって V = {x0}
  have V_eq_singleton : V = ({x0} : Finset α) := by
    apply Finset.Subset.antisymm_iff.mpr
    exact ⟨V_subset_singleton, incl₂⟩
  -- すると |V|=1 に矛盾
  have : V.card = 1 := by
    exact congrArg Finset.card V_eq_singleton ▸ card_singleton x0
  have : 2 ≤ 1 := by
    subst V_eq_singleton
    simp_all only [mem_singleton, Nat.not_ofNat_le_one]

  exact Nat.not_succ_le_self 1 this

--Mainから参照
/-- ★ Free 非空（`|V|≥2` なら `V \ {x0}` 非空）。 -/
lemma Free_nonempty_for_build_of_two_or_more
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hne : R ≠ ∅)
  (h2 : 2 ≤ V.card) :
  (Free (Q := buildSCCQuot_with_free (α := α) V R hV hne)).Nonempty := by
  classical
  rcases Rep_eq_singleton_for_build (V := V) (R := R) (hV := hV) (hne := hne)
    with ⟨x0, hx0V, hRep⟩
  -- Free = V \ Rep = V \ {x0}
  have hFree :
    Free (Q := buildSCCQuot_with_free (α := α) V R hV hne)
        = V \ ({x0} : Finset α) := by
    change V \ (Rep (Q := buildSCCQuot_with_free (α := α) V R hV hne))
          = V \ ({x0} : Finset α)
    exact congrArg (fun (S : Finset α) => V \ S) hRep
  -- `V.erase x0` 非空 ⇒ `V \ {x0}` 非空（明らかな包含）
  have hErase : (V.erase x0).Nonempty :=
    erase_nonempty_of_card_ge_two (V := V) (x0 := x0) (hx0V := hx0V) (h2 := h2)
  rcases hErase with ⟨y, hy⟩
  have hy' : y ∈ V \ ({x0} : Finset α) := by
    rcases mem_erase.mp hy with ⟨hyne, hyV⟩
    exact mem_sdiff.mpr ⟨hyV, by
      intro hmem; exact hyne (mem_singleton.mp hmem)⟩
  -- 仕上げ
  have : (V \ ({x0} : Finset α)).Nonempty := ⟨y, hy'⟩
  -- Free に戻す
  change (Free (Q := buildSCCQuot_with_free V R hV hne)).Nonempty
  -- `rw [hFree]` 相当（simpa は使わない方針ならそのまま exact）
  exact ⟨y, by
    -- y ∈ Free
    -- `simp [hFree]` で十分
    simpa [hFree] using hy'⟩

/-- |V|=1 のとき、∅ と {a} は常に閉（定義次第だが Horn 条件では自明） -/
private lemma empty_and_singleton_are_closed
  {α : Type u} [DecidableEq α]
  (a : α) (R : Finset (Rule α)) (hV : supportedOn ({a} : Finset α) R) :
  isClosed R (∅ : Finset α) ∧ isClosed R ({a} : Finset α) := by
  classical
  -- 1) ∅ は自明（前件が偽）
  have hEmpty : isClosed R (∅ : Finset α) := by

    intro t ht hParents
    rcases hParents with ⟨ha, hb⟩
    simp_all only [notMem_empty]

  -- 2) {a} は a しか含まないので、前件が成り立つなら r も a であり ∈ {a}
  --    （厳密には supportedOn が V={a} を保証している場面で使います）
  have hSing : isClosed R ({a} : Finset α) := by
    dsimp [isClosed]
    dsimp [supportedOn] at hV
    intro t ht
    intro a_1
    simp_all only [mem_singleton, Prod.forall]
    obtain ⟨fst, snd⟩ := t
    obtain ⟨fst_1, snd⟩ := snd
    obtain ⟨left, right⟩ := a_1
    subst right
    simp_all only
    simpa using hV _ _ _ ht
  exact And.intro hEmpty hSing

/-- |V|=1 なら NDS2=0（∅ と {a} の2点のみ） -/
private lemma TwoStem_card_eq_one
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (h1 : V.card = 1) :
  NDS2 V (family V R) ≤ 0 := by
  classical
  -- V={a}
  obtain ⟨a, hVa⟩ : ∃ a, V = ({a} : Finset α) := by
    -- `card_eq_one` から
    have := Finset.card_eq_one.mp h1
    exact this


  have hClosed := empty_and_singleton_are_closed (a := a) (R := R)
  have hEmptyClosed : isClosed R (∅ : Finset α) := by simp_all only [forall_const, card_singleton]
  have hSingClosed  : isClosed R ({a} : Finset α) := by
    -- ここは上の補題の「supportedOn_singleton 版」に差し替えると堅い
    -- 今回は `V={a}` を使って補強する：
    -- 任意の t∈R は supportedOn より全成分が V に属する → = a
    intro t ht hParents
    rcases hParents with ⟨ha, hb⟩
    have htV := hV (by exact ht)
    have : t.2.2 ∈ V := htV.right.right
    -- V={a} から t.2.2=a
    have : t.2.2 = a := by
      -- `V = {a}` を使って単元化
      have : t.2.2 ∈ ({a} : Finset α) := by simpa [hVa] using this
      exact mem_singleton.mp this
    -- {a} に入る
    exact (by simp [this])
  -- つぎに family の元は V の部分集合なので、∅ か {a} のどちらか
  have family_ground :
      ∀ {I : Finset α}, I ∈ family V R → I ⊆ V := by

    intro I hI
    -- TODO: 既存補題に差し替え：`family_mem_iff` など
    -- 仮の実装：`I ⊆ V` を直接使えるようにしておきます。
    exact (by
      exact (by

        exact by cases hVa; exact family_subsets ({a} : Finset α) R hI))
  -- family = {∅, {a}} を示す
  have hEmpty_mem : (∅ : Finset α) ∈ family V R := by

    exact empty_mem_family V R
  have hSing_mem : ({a} : Finset α) ∈ family V R := by
    -- 同様に `subset` と `hSingClosed` で入れる
    -- `subset` は `by intro x hx; exact by cases mem_singleton.mp hx; simpa [hVa]`
    --ステムの大きさが1のときはシングルトンはhyperedgeでないがどうなっているのか？
    apply (mem_family_iff V R).mpr
    constructor
    · intro x hx
      simp_all only [and_self, imp_self, mem_singleton, card_singleton, subset_singleton_iff]
    · exact hSingClosed

  -- 逆包含：任意 I∈family は I⊆V= {a} なので I=∅ または I={a}
  have hFamily_two :
    family V R = ({∅, {a}} : Finset (Finset α)) := by
    classical
    -- 包含両方向
    apply Finset.Subset.antisymm_iff.mpr
    constructor
    · intro I hI
      have hIV : I ⊆ V := family_ground (hI)
      -- V={a} より I⊆{a}
      have hI_sub : I ⊆ ({a} : Finset α) := by simpa [hVa] using hIV
      -- I=∅ ∨ I={a}
      by_cases ha : a ∈ I
      · -- I={a}
        have : I = ({a} : Finset α) := by
          -- `Finset.subset_singleton_iff` 相当を手作り：
          -- `I ⊆ {a}` かつ `a ∈ I` ⇒ I={a}
          apply Finset.Subset.antisymm_iff.mpr
          constructor
          · exact hI_sub
          · intro y hy
            -- y ∈ {a} ⇒ y=a ⇒ a∈I ⇒ y∈I
            have : y = a := by exact mem_singleton.mp hy
            cases this; exact ha
        -- 2点集合に入る
        -- `{∅, {a}}` への membership
        -- `by` で
        have : I ∈ ({∅, {a}} : Finset (Finset α)) := by
          -- `mem_insert`, `mem_singleton`
          -- `simp` で一行
          simp [this]
        exact this
      · -- a∉I ⇒ I=∅
        have : I = (∅ : Finset α) := by
          -- `I ⊆ {a}` かつ `a ∉ I` ⇒ 何も入らない
          -- 直接 `eq_empty_iff_forall_not_mem` を使います
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          have hy' : y ∈ ({a} : Finset α) := hI_sub hy
          have : y = a := mem_singleton.mp hy'
          cases this; exact ha.elim (by exact hy)
        -- 2点集合に入る
        have : I ∈ ({∅, {a}} : Finset (Finset α)) := by
          simp [this]
        exact this
    · -- 逆包含：{∅, {a}} ⊆ family
      intro I hI
      -- `I=∅` か `I={a}`
      rcases mem_insert.mp hI with hI | hI
      · -- I=∅
        cases hI
        exact hEmpty_mem
      · -- I={a} ∈ { {a} }
        have : I = ({a} : Finset α) := by exact mem_singleton.mp hI
        -- 置換して hSing_mem
        cases this; exact hSing_mem
  -- これで NDS2 を計算
  have hNDS2 :
    NDS2 V (family V R)
      = ∑ I ∈ ({∅, {a}} : Finset (Finset α)),
          ((2 : Int) * (I.card : Int) - (V.card : Int)) := by
    -- `NDS2_sum_formula` + 上の同値
    have := NDS2_sum_formula (V := V) (F := family V R)

    simp_all only [and_self, imp_self, card_singleton, mem_singleton, subset_singleton_iff,
      implies_true, Nat.cast_one, sum_sub_distrib, card_empty, Nat.cast_zero, mul_zero,
      sum_insert_of_eq_zero_if_notMem, sum_singleton, mul_one, sum_const, Int.nsmul_eq_mul]


  have : NDS2 V (family V R) = 0 := by

    have := NDS2_sum_formula (V := V) (F := family V R)
    -- family を置換
    -- tactic を減らすため、`calc` で順に評価します
    calc
      NDS2 V (family V R)
          = ∑ I ∈ family V R,
              ((2 : Int) * (I.card : Int) - (V.card : Int)) := by
            exact NDS2_sum_formula (V := V) (F := family V R)
      _   = ∑ I ∈ ({∅, {a}} : Finset (Finset α)),
              ((2 : Int) * (I.card : Int) - (V.card : Int)) := by

            exact congrArg (fun S => ∑ I ∈ S, ((2 : Int) * (I.card : Int) - (V.card : Int))) hFamily_two
      _   = 0 := by

            simp_all only [and_self, imp_self, card_singleton, mem_insert, mem_singleton, subset_singleton_iff, implies_true,
              true_or, singleton_ne_empty, or_true, Nat.cast_one, sum_sub_distrib, card_empty, Nat.cast_zero, mul_zero,
              sum_insert_of_eq_zero_if_notMem, sum_singleton, mul_one, sum_const, Int.nsmul_eq_mul]
            exact hNDS2

  exact le_of_eq this

--参照されている。
/-- |V| ≤ 1 版のまとめ -/
lemma TwoStem_card_le_one
  {α : Type u} [DecidableEq α]
  (V : Finset α) (R : Finset (Rule α))
  (hV : supportedOn V R) (hle : V.card ≤ 1) :
  NDS2 V (family V R) ≤ 0 := by
  classical
  -- `V.card = 0 ∨ V.card = 1`
  have h := Nat.le_one_iff_eq_zero_or_eq_one.mp hle
  cases h with
  | inl h0 =>
      -- V.card = 0 ⇒ V=∅ ⇒ supportedOn(∅,R) から R=∅
      have Vempty : V = (∅ : Finset α) := Finset.card_eq_zero.mp h0
      -- `supportedOn ∅ R` を作るために書き換え
      have hVempty : supportedOn (∅ : Finset α) R := by
        intro t ht
        have := hV (by exact ht)

        simpa [Vempty]
      have hR0 : R = ∅ := rules_empty_of_supportedOn_and_V_empty (R := R) (hV := hVempty)
      exact hRempty (V := V) (R := R) (hR := hR0)
  | inr h1 =>
      -- V.card = 1
      exact TwoStem_card_eq_one (V := V) (R := R) (hV := hV) (h1 := h1)
