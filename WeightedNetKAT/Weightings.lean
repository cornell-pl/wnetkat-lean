import Mathlib.Data.Set.Countable
import WeightedNetKAT.Domain
import WeightedNetKAT.WeightedFinsum

section

variable {X : Type} {𝒮 : Type} [WeightedPreSemiring 𝒮]

noncomputable def W.mass [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (m : W X 𝒮) [Encodable m.supp] :=
  ⨁' x : m.supp, m x.val

structure 𝒲 (𝒮 X : Type) [WeightedPreSemiring 𝒮] where
  toFun : W X 𝒮
  countable : Countable toFun.supp

structure 𝒞 (𝒮 X : Type) [WeightedPreSemiring 𝒮] extends 𝒲 𝒮 X where
  finSupp : Finset X
  finSupp_eq_supp : finSupp = toFun.supp

abbrev 𝒲.supp (m : 𝒲 𝒮 X) := m.toFun.supp

instance : FunLike (𝒲 𝒮 X) X 𝒮 where
  coe m := m.toFun
  coe_injective' := by intro ⟨_, _, _⟩ ⟨_, _, _⟩; simp_all

@[ext]
theorem 𝒲.ext (C₁ C₂ : 𝒲 𝒮 X)
    (h : ∀ i, C₁ i = C₂ i) : C₁ = C₂ := by cases C₁; cases C₂; congr; ext; apply h

@[simp]
theorem 𝒲.mk_apply {X : Type} {f : X → 𝒮} {x : X} (h : Countable ↑(W.supp f)) :
  DFunLike.coe (F:=𝒲 𝒮 X) ⟨f, h⟩ x = f x := by rfl
@[simp]
theorem 𝒲.toFun_apply {X : Type} (m : 𝒲 𝒮 X) {x : X} :
  m.toFun x = m x := by rfl

instance {m : 𝒲 𝒮 X} : Countable m.supp := m.countable
noncomputable instance {m : 𝒲 𝒮 X} : Encodable m.supp := Encodable.ofCountable _

instance 𝒲.instWeightedAdd : WeightedAdd (𝒲 𝒮 X) where
  wAdd := fun a b ↦ ⟨a ⨁ b, by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    apply Set.Countable.mono _ (Set.Countable.union ha hb)
    intro
    contrapose!
    simp +contextual [WeightedAdd.wAdd]⟩

@[simp] theorem 𝒲.instWeightedAdd_apply (m m' : 𝒲 𝒮 X) {x : X} : (m ⨁ m') x = m x ⨁ m' x := rfl

instance 𝒲.instWeightedMul : WeightedMul (𝒲 𝒮 X) where
  wMul := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    ⟨a ⨀ b, by
      apply @Function.Injective.countable (W.supp (a ⨀ b)) (Prod a.supp b.supp) _
      case f =>
        intro ⟨ m_val, m_prop ⟩
        simp at m_prop
        refine ⟨ ⟨ m_val, ?goal1 ⟩, ⟨ m_val, ?goal2 ⟩⟩
        all_goals (simp ; grind only [WeightedMul.wMul, WeightedMul.instPi, cases WeightedPreSemiring, cases
          WeightedMonotonePreSemiring, cases WeightedOmegaContinuousPreSemiring])
      case hf =>
        intro ⟨v₁, p₁⟩ ⟨v₂, p₂ ⟩
        grind only⟩

@[simp] theorem 𝒲.instWeightedMul_apply (m m' : 𝒲 𝒮 X) {x : X} : (m ⨀ m') x = m x ⨀ m' x := rfl

instance 𝒲.instWeightedZero : WeightedZero (𝒲 𝒮 X) where
  wZero := by
    refine ⟨ fun x => 𝟘, ?_⟩
    refine ⟨ fun x => 0, ?_ ⟩
    intro ⟨v1, p1⟩ ⟨v2, p2⟩
    trivial

@[simp] theorem 𝒲.instWeightedZero_apply {x : X} : (𝟘 : 𝒲 𝒮 X) x = 𝟘 := rfl

def 𝒲.wNsmul (n : ℕ) (w : 𝒲 𝒮 X) : 𝒲 𝒮 X := match n with
  | 0 => 𝟘
  | n + 1 => wNsmul n w ⨁ w

open WeightedPreSemiring in
instance 𝒲.instWeightedPreSemiring : WeightedPreSemiring (𝒲 𝒮 X) where
  wAdd_assoc _ _ _ := by ext x; apply wAdd_assoc
  wZero_add _ := by ext X; apply wZero_add
  add_wZero _ := by ext X; apply add_wZero
  wNsmul := 𝒲.wNsmul
  wNsmul_wZero _ := by rfl
  wNsmul_succ _ _ := by rfl
  wAdd_comm _ _ := by ext x; apply wAdd_comm
  left_distrib _ _ _ := by ext x; apply WeightedPreSemiring.left_distrib
  right_distrib _ _ _ := by ext x; apply WeightedPreSemiring.right_distrib
  wZero_mul _ := by ext x; apply wZero_mul
  mul_wZero _ := by ext x; apply mul_wZero
  mul_assoc _ _ _ := by ext x; apply WeightedPreSemiring.mul_assoc

instance 𝒲.instWeightedLE [WeightedLE 𝒮] : WeightedLE (𝒲 𝒮 X) where
  wle := fun ⟨a, _⟩ ⟨ b, _ ⟩ => a ≼ b

open WeightedPartialOrder in
instance 𝒲.instWeightedPartialOrder [WeightedPartialOrder 𝒮] : WeightedPartialOrder (𝒲 𝒮 X) where
  wle_refl a x := by simp
  wle_trans {a b c} hab hbc x := wle_trans (hab x) (hbc x)
  wle_antisymm { a b} hab hba := by
    have ⟨ a_val, a_prop ⟩ := a
    have ⟨ b_val, b_prop ⟩ := b
    suffices a_val = b_val by
      grind only
    ext x
    exact wle_antisymm (hab x) (hba x)

@[reducible]
instance [WeightedPartialOrder 𝒮] : Trans (· ≼ · : 𝒲 𝒮 X → 𝒲 𝒮 X → Prop) (· ≼ · : 𝒲 𝒮 X → 𝒲 𝒮 X → Prop) (· ≼ · : 𝒲 𝒮 X → 𝒲 𝒮 X → Prop) where
  trans := WeightedPartialOrder.wle_trans

open WeightedOmegaCompletePartialOrder in
instance 𝒲.instWeightedOmegaCompletePartialOrder [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] :
    WeightedOmegaCompletePartialOrder (𝒲 𝒮 X) where
  wSup C := ⟨fun i ↦ wSup (C.map (· i) (· i)), by
    simp
    let s : Set _ := ⋃ n : ℕ, (C n).supp
    have s_countable : Countable s := by
      simp only [Set.countable_coe_iff, Set.countable_iUnion_iff, s]
      exact fun n => (C n).countable
    apply Set.Countable.mono _ s_countable
    intro x mem
    simp only [Set.mem_iUnion, W.supp_mem_iff, ne_eq, s]
    simp only [W.supp_mem_iff, ne_eq, wSup_eq_zero_iff, not_forall, s] at mem
    obtain ⟨p, hp⟩ := mem
    exists p⟩
  le_wSup i p := by
    simp
    apply WeightedPartialOrder.wle_trans _ (le_wSup i)
    simp only [WeightedChain.map, WeightedChain.val_apply]
    simp only [DFunLike.coe]
    simp
  wSup_le h x := by
    simp
    apply wSup_le
    intro n
    simp only [WeightedChain.map, DFunLike.coe]
    simp
    specialize h n x
    exact h

open WeightedOmegaCompletePartialOrder in
@[simp]
theorem 𝒲.wSup_apply [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (C : WeightedChain (𝒲 𝒮 X)) (x) : (wSup C) x = wSup (C.map (· x) (· x)) := rfl

open WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring in
instance 𝒲.instWeightedOmegaContinuousPreSemiring [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] :
    WeightedOmegaContinuousPreSemiring (𝒲 𝒮 X) where
  wle_positive _ _ := by simp
  wAdd_mono _ _ _ _ _ := by apply wAdd_mono_left; apply_assumption
  wMul_mono_left _ _ _ _ _ := by apply wMul_mono_left; apply_assumption
  wMul_mono_right  _ _ _ _ _ := by apply wMul_mono_right; apply_assumption
  wAdd_wSup _ _ := by ext x; apply wAdd_wSup
  wSup_wAdd _ _ := by ext x; apply wSup_wAdd
  wMul_wSup _ _ := by ext x; apply wMul_wSup
  wSup_wMul _ _ := by ext x; apply wSup_wMul

@[simp]
instance {X : Type} : WeightedHMul 𝒮 (𝒲 𝒮 X) (𝒲 𝒮 X) where
  wHMul w m := ⟨fun h' ↦ w ⨀ m h', by
    apply Set.Countable.mono _ m.countable; intro; contrapose!; simp +contextual⟩
@[simp]
instance {X : Type} : WeightedHMul (𝒲 𝒮 X) 𝒮 (𝒲 𝒮 X) where
  wHMul m w := ⟨fun h' ↦ m h' ⨀ w, by
    apply Set.Countable.mono _ m.countable; intro; contrapose!; simp +contextual⟩

@[simp] theorem 𝒲.sMul_apply {X : Type} (m : 𝒲 𝒮 X) (w : 𝒮) (x : X) : (w ⨀ m) x = w ⨀ m x := rfl
@[simp] theorem 𝒲.one_sMul {𝒮 : Type} [WeightedSemiring 𝒮] {X : Type} (m : 𝒲 𝒮 X) : (𝟙 : 𝒮) ⨀ m = m := by ext; simp
@[simp] theorem 𝒲.zero_sMul {X : Type} (m : 𝒲 𝒮 X) : (𝟘 : 𝒮) ⨀ m = 𝟘 := by ext; simp
@[simp] theorem 𝒲.sMul'_apply {X : Type} (m : 𝒲 𝒮 X) (w : 𝒮) (x : X) : (m ⨀ w) x = m x ⨀ w := rfl
@[simp] theorem 𝒲.sMul_one {𝒮 : Type} [WeightedSemiring 𝒮] {X : Type} (m : 𝒲 𝒮 X) : m ⨀ (𝟙 : 𝒮) = m := by ext; simp
@[simp] theorem 𝒲.sMul_zero {X : Type} (m : 𝒲 𝒮 X) : m ⨀ (𝟘 : 𝒮) = 𝟘 := by ext; simp

end

section

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮]

def η [DecidableEq X] (x : X) : 𝒲 𝒮 X := ⟨fun y ↦ if x = y then 𝟙 else 𝟘, by
  suffices Finite (W.supp (𝒮:=𝒮) fun y ↦ if x = y then 𝟙 else 𝟘) by apply Finite.to_countable
  if (𝟙 : 𝒮) = 𝟘 then
    apply Set.Finite.ofFinset {}
    simpa
  else
    apply Set.Finite.ofFinset {x}
    simpa [eq_comm]⟩

notation "η[" 𝒮 "]" => η (𝒮:=𝒮)

-- TODO: these should be moved somewhere more appropriate
theorem wMul_eq_zero_of {α : Type} [WeightedPreSemiring α] {a b : α} :
    a = 𝟘 ∨ b = 𝟘 → a ⨀ b = 𝟘 := by rintro (h | h) <;> subst_eqs <;> simp
@[simp]
theorem nonzero_wMul_nonzero {α : Type} [WeightedPreSemiring α] {a b : α} :
    ¬a ⨀ b = 𝟘 → ¬a = 𝟘 ∧ ¬b = 𝟘 := by
  contrapose
  exact fun h ↦ not_ne_iff.mpr (wMul_eq_zero_of (or_iff_not_and_not.mpr h))

variable [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

noncomputable def 𝒲.bind {Y : Type} (m : 𝒲 𝒮 X) (f : X → 𝒲 𝒮 Y) :
    𝒲 𝒮 Y :=
  ⟨fun y ↦ ⨁' x : m.supp, m x ⨀ f x y, by
    let s : Set _ := ⋃ x ∈ m.supp, (f x).supp
    apply Set.Countable.mono _ (Set.Countable.biUnion m.countable fun a _ ↦ (f a).countable : Countable s)
    intro y
    simp only [W.supp_mem_iff, ne_eq, WeightedSum_eq_zero_iff, Subtype.forall, not_forall,
      Classical.not_imp, Set.mem_iUnion, exists_prop, forall_exists_index, and_imp, s]
    intro x h₁ h₂
    use x, h₁
    contrapose! h₂
    replace h₂ : f x y = 𝟘 := h₂
    simp [h₂]⟩

infixr:50 " ≫= " => 𝒲.bind

instance {Y : Type} [Countable X] {m : 𝒲 𝒮 X} (f : X → 𝒲 𝒮 Y) :
    Countable (m ≫= f).supp := (m ≫= f).countable

open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono (f : 𝒲 𝒮 X) : WeightedMonotone (ι:=X → 𝒲 𝒮 X) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono_right (f : 𝒲 𝒮 X) : WeightedMonotone (ι:=X → 𝒲 𝒮 X) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono_left (g : X → 𝒲 𝒮 X) : WeightedMonotone (ι:=𝒲 𝒮 X) (· ≫= g) := by
  intro a b hab h
  simp
  have : DecidableEq X := Classical.typeDecidableEq _
  apply WeightedSum_le_of_finset fun Sa ↦ ?_
  have : ∀ x, ¬a x = 𝟘 → ¬b x = 𝟘 := by
    intro x hx
    contrapose! hx
    have := hab x
    simp_all
  let S : Finset X := Sa.map ⟨(·.val), by simp⟩
  let Sb : Finset ↑b.supp := Sa.map ⟨(fun ⟨x, h⟩ ↦ ⟨x, this x h⟩), by intro; simp [Subtype.val_inj]⟩
  apply WeightedPartialOrder.wle_trans _ (WeightedSum_finset_le Sb)
  rw [WeightedFinsum_bij (Sι:=Sa) (Sγ:=S) (fγ:=fun x ↦ a x ⨀ g x h) (fun x _ ↦ x.val)]
  · rw [WeightedFinsum_bij (Sι:=Sb) (Sγ:=S) (fγ:=fun x ↦ b x ⨀ g x h) (fun x _ ↦ x.val)]
    · apply WeightedFinsum_mono
      intro x
      simp
      apply wMul_mono_right _ (hab x)
    · simp_all [Sb, S]
      rintro x hbx y hax hy' ⟨_⟩
      simp_all
    · simp_all [Sb, S]
    · simp_all [Sb, S]
    · simp_all [Sb, S]
  · simp_all [Sb, S]
  · simp_all [Sb]
  · simp_all [Sb, S]
  · simp_all [Sb, S]

open WeightedOmegaCompletePartialOrder in
theorem 𝒲.bind_continuous (f : 𝒲 𝒮 X) : WeightedOmegaContinuous (f ≫= ·) f.bind_mono := by
  intro C
  ext h
  simp [bind, WeightedOmegaContinuousMulRight]
  have :=  @WeightedSum_cont f.supp 𝒮 _ _ _
  unfold WeightedOmegaContinuous at this
  simp only [WeightedChain.map, DFunLike.coe] at this
  simp [wSup] at this
  simp only [WeightedChain.map, DFunLike.coe] at this
  simp at this
  convert this _
  rotate_right
  . exact ⟨fun n x ↦ f x ⨀ (C n x) h, by
      intro j k le point
      simp
      apply wMul_gconr
      . simp
      . exact C.prop le point h
      ⟩
  . ext; simp; magic_simp
  . simp only [WeightedChain.map, DFunLike.coe]

open WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring

theorem 𝒲.bind_continuous'' [Countable X] (g : X → 𝒮) (C : WeightedChain (𝒲 𝒮 X)) :
      wSup ⟨fun n ↦ ⨁' (i : (wSup C).supp), C n i ⨀ g i, by
        intro a b hab; apply WeightedSum_mono
        apply wMul_mono_right
        intro i
        apply C.prop hab⟩
    = wSup ⟨fun n ↦ ⨁' (x : (C n).supp), C n x ⨀ g x, by
      intro a b hab
      simp only
      letI : Encodable X := Encodable.ofCountable X
      have q := fun a ↦
        WeightedSum_eq_WeightedSum_of_ne_one_bij
          (ι:=(C a).supp) (γ:=X) (f:=fun x ↦ C a x ⨀ g x) (g:=fun x ↦ C a x ⨀ g x)
          (fun ⟨x, hx⟩ ↦ ⟨x, by contrapose hx; simp at hx; replace hx : C a x = 𝟘 := hx; simp [hx]⟩)
      rw [q a, q b]
      · apply WeightedSum_mono
        apply wMul_mono_right
        exact C.prop hab
      all_goals intro ⟨_, _⟩; simp_all⟩ := by
  congr with n
  have : (C n).supp ⊆ (wSup C).supp := by
    intro x
    simp only [W.supp_mem_iff, ne_eq, 𝒲.instWeightedOmegaCompletePartialOrder,
      wSup_eq_zero_iff, not_forall]
    magic_simp
    intro h'
    use n
  apply WeightedSum_eq_WeightedSum_of_ne_one_bij (fun ⟨x, hx⟩ ↦ ⟨x.val, this x.prop⟩)
  · intro ⟨⟨a, _⟩, ha⟩ ⟨b, hb⟩; simp_all
  · intro ⟨a, ha⟩
    simp_all
    simp_all
    contrapose!
    intro h
    have : C n a = 𝟘 := h
    simp [this]
  · simp

theorem 𝒲.bind_continuous' [Countable X] (g : X → 𝒲 𝒮 X) :
    WeightedOmegaContinuous (· ≫= g) (𝒲.bind_mono_left g) := by
  intro C
  ext h
  simp only
  magic_simp [bind]
  letI : Encodable (wSup C).supp := by exact instEncodableElemSupp
  simp
  -- have : ∀ (x : (wSup C).supp), wSup C x = wSup ⟨(C · x), (C.prop · x)⟩ := by
  --   simp [𝒲.instWeightedOmegaCompletePartialOrder]
  --   magic_simp
  --   simp
  -- simp [this]; clear this
  simp [WeightedOmegaContinuousMulLeft]
  magic_simp
  simp
  have := WeightedSum_cont (X:=(wSup C).supp) (𝒮:=𝒮) ⟨fun n x ↦ (C n) ↑x ⨀ (g x) h, by
    intro a b hab i
    apply wMul_mono_right
    apply C.prop hab⟩
  simp only [_root_.wSup_apply] at this
  simp only [DFunLike.coe, wSup_apply, WeightedChain.map] at this
  simp only [WeightedChain.val_apply, toFun_apply] at this
  simp [this]; clear this
  conv =>
    right
    simp
  magic_simp
  simp
  apply 𝒲.bind_continuous'' (g · h)

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem WeightedFinsum_apply_𝒲 {α : Type} [DecidableEq α] (S : Finset α) (f : α → 𝒲 𝒮 X) (i : X) :
    (⨁ᶠ x ∈ S, f x) i = ⨁ᶠ x ∈ S, f x i := by
  simp [WeightedFinsum]
  induction S using Finset.induction with
  | empty => simp
  | insert x S hx ih =>
    simp_all [WeightedAdd.wAdd]

@[simp]
theorem WeightedSum_apply_𝒲 {α : Type} [Encodable α]
    (f : α → 𝒲 𝒮 X) (i : X) :
    (⨁' (x : α), f x) i = ⨁' (x : α), f x i := by
  simp [WeightedSum]
  simp [WeightedChain.map, WeightedSum_chain]
  magic_simp
  simp
  congr! with a b
  split <;> rfl

theorem 𝒲.bind_sum [DecidableEq X] {f : 𝒲 𝒮 X} {g : ℕ → X → 𝒲 𝒮 X} :
    (f ≫= ⨁' (x : ℕ), g x) = (⨁' (x : ℕ), (f ≫= g x)) := by
  simp [𝒲.bind]
  ext h
  simp
  magic_simp
  simp [← WeightedSum_mul_left]
  rw [WeightedSum_comm]

open WeightedPartialOrder

theorem 𝒲.bind_apply (f : 𝒲 𝒮 X) (g : X → 𝒲 𝒮 X) (x : X) :
    (f ≫= g) x = ⨁' (i : f.supp), f i ⨀ g i x := by
  simp [bind]
