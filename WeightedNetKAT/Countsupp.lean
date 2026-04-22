module

public import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
public import Mathlib.Data.Set.Countable

@[expose] public section

open OmegaCompletePartialOrder

/-- `Countsupp α M`, denoted `α →c M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but countably many `x`.  -/
structure Countsupp (α M : Type*) [Zero M] where
  toFun : α → M
  countable : toFun.support.Countable

@[inherit_doc]
infixr:25 " →c " => Countsupp

namespace Countsupp

section Basic

variable {α M : Type*}

variable [Zero M]

def support (f : α →c M) : Set α := f.toFun.support

instance instFunLike : FunLike (α →c M) α M :=
  ⟨toFun, by rintro ⟨f, s⟩ ⟨g, t⟩ (rfl : f = g); congr⟩

@[ext]
theorem ext {f g : α →c M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

lemma ne_iff {f g : α →c M} : f ≠ g ↔ ∃ a, f a ≠ g a := DFunLike.ne_iff

theorem toFun_apply (c : α →c M) (x : α) : c.toFun x = c x := rfl

@[simp, norm_cast]
theorem coe_mk (f : α → M) (h : (Function.support f).Countable) : ⇑(⟨f, h⟩ : α →c M) = f :=
  rfl

instance instZero : Zero (α →c M) :=
  ⟨⟨0, by simp⟩⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : α →c M) = 0 := rfl

theorem zero_apply {a : α} : (0 : α →c M) a = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : α →c M).support = ∅ := by simp [support]; rfl

theorem ite_apply {p} [Decidable p] {f g : α →c M} {a : α} :
    (if p then f else g) a = if p then f a else g a := by
  split_ifs <;> rfl

instance instInhabited : Inhabited (α →c M) :=
  ⟨0⟩

@[simp]
theorem mem_support_iff {f : α →c M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 := by rfl

@[simp, norm_cast]
theorem fun_support_eq (f : α →c M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem notMem_support_iff {f : α →c M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

theorem support_countable {f : α →c M} : f.support.Countable := f.countable
instance support_countable' {f : α →c M} : Countable f.support := f.countable

@[simp, norm_cast]
theorem coe_eq_zero {f : α →c M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

theorem ext_iff' {f g : α →c M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := notMem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, notMem_support_iff] at h
        rw [hf, hg]⟩

end Basic

section OmegaContinuousNonUnitalSemiring

variable {X : Type*}
variable {𝒮 : Type*}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]

instance : Add (X →c 𝒮) where
  add a b := ⟨fun x ↦ a x + b x,
    Set.Countable.mono (by intro; simp; grind)
      (Set.countable_union.mpr ⟨a.support_countable, b.support_countable⟩)⟩
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
@[simp] theorem add_apply (a b : X →c 𝒮) (x : X) : (a + b) x = a x + b x := rfl
instance : Mul (X →c 𝒮) where
  mul a b := ⟨fun x ↦ a x * b x,
    Set.Countable.mono (by intro; contrapose!; simp +contextual)
      (Set.countable_union.mpr ⟨a.support_countable, b.support_countable⟩)⟩
omit [OmegaCompletePartialOrder 𝒮] in
@[simp] theorem mul_apply (a b : X →c 𝒮) (x : X) : (a * b) x = a x * b x := rfl

instance : HMul 𝒮 (X →c 𝒮) (X →c 𝒮) where
  hMul a b := ⟨fun x ↦ a * b x,
    Set.Countable.mono (by intro; contrapose!; simp +contextual) b.support_countable⟩
omit [OmegaCompletePartialOrder 𝒮] in
@[simp] theorem hMul_apply_left (a : 𝒮) (b : X →c 𝒮) (x : X) : (a * b) x = a * b x := rfl

instance : HMul (X →c 𝒮) 𝒮 (X →c 𝒮) where
  hMul a b := ⟨fun x ↦ a x * b,
    Set.Countable.mono (by intro; contrapose!; simp +contextual) a.support_countable⟩
omit [OmegaCompletePartialOrder 𝒮] in
@[simp] theorem hMul_apply_right (a : X →c 𝒮) (b : 𝒮) (x : X) : (a * b) x = a x * b := rfl

instance : NonUnitalSemiring (X →c 𝒮) where
  add_assoc _ _ _ := by ext i; apply add_assoc
  zero_add _ := by ext i; apply zero_add
  add_zero _ := by ext i; apply add_zero
  nsmul := fun n C ↦
    ⟨fun i ↦ n * C i,
      Set.Countable.mono (fun x ↦ by contrapose!; simp +contextual) C.support_countable⟩
  add_comm _ _ := by ext i; apply add_comm
  left_distrib _ _ _ := by ext i; apply left_distrib
  right_distrib _ _ _ := by ext i; apply right_distrib
  zero_mul _ := by ext i; apply zero_mul
  mul_zero _ := by ext i; apply mul_zero
  mul_assoc _ _ _ := by ext i; apply mul_assoc
  nsmul_zero _ := by simp; rfl
  nsmul_succ n c := by ext; simp; simp [right_distrib]

instance : LE (X →c 𝒮) where
  le f g := ∀ x, f x ≤ g x

instance : PartialOrder (X →c 𝒮) where
  le_refl _ _ := by simp
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)
  le_antisymm _ _ h₁ h₂ := by ext i; apply le_antisymm (h₁ i) (h₂ i)

instance : OmegaCompletePartialOrder (X →c 𝒮) where
  ωSup C := ⟨fun x ↦ ωSup (C.map ⟨(· x), fun ⦃_ _⦄ a ↦ a x⟩), by
    apply Set.Countable.mono _ (Set.countable_iUnion fun i ↦ (C i).support_countable)
    intro x
    simp⟩
  ωSup_le := by
    intro C f h x
    simp only [coe_mk, ωSup_le_iff]
    exact fun i ↦ h i x
  le_ωSup := by
    intro C i X
    refine le_ωSup_of_le i ?_
    simp only [Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, le_refl]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
@[simp]
theorem ωSup_apply {X : Type*} [Fintype X] [DecidableEq 𝒮] (C : Chain (X →c 𝒮)) (x : X) :
    (ωSup C) x = ωSup (C.map ⟨(· x), (fun ⦃_ _⦄ a ↦ a x)⟩) := rfl

instance : OrderBot (X →c 𝒮) where
  bot := 0
  bot_le C x := by simp

instance : MulLeftMono (X →c 𝒮) := ⟨fun C _ _ h x ↦ mul_le_mul_right (h x) (C x)⟩
instance : MulRightMono (X →c 𝒮) := ⟨fun C _ _ h x ↦ mul_le_mul_left (h x) (C x)⟩

instance : IsPositiveOrderedAddMonoid (X →c 𝒮) where
  add_le_add_left _ _ h C x := add_le_add_left (h x) (C x)
  bot_eq_zero := rfl

variable [OmegaContinuousNonUnitalSemiring 𝒮]

open OmegaContinuousNonUnitalSemiring in
instance {X : Type*} : OmegaContinuousNonUnitalSemiring (X →c 𝒮) where
  ωScottContinuous_add_left := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, fun C ↦ ?_⟩
    ext x
    simp only [add_apply, ωSup_apply, add_ωSup]
    rfl
  ωScottContinuous_add_right := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, fun C ↦ ?_⟩
    ext x
    simp only [add_apply, ωSup_apply, ωSup_add]
    rfl
  ωScottContinuous_mul_left := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨(mul_right_mono), fun C ↦ ?_⟩
    ext x
    simp only [mul_apply, ωSup_apply, mul_ωSup]
    rfl
  ωScottContinuous_mul_right := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, fun C ↦ ?_⟩
    ext x
    simp only [mul_apply, ωSup_apply, ωSup_mul]
    rfl

noncomputable def bind {Y : Type*} (f : X →c 𝒮) (g : X → Y →c 𝒮) : Y →c 𝒮 :=
  ⟨fun y ↦ ω∑ x : f.support, f x * g x y, by
    let s : Set _ := ⋃ x ∈ f.support, (g x).support
    apply Set.Countable.mono _ (Set.Countable.biUnion f.countable fun a _ ↦ (g a).countable : Countable s)
    intro y
    simp only [Function.mem_support, ne_eq, ωSum_eq_zero_iff, Subtype.forall, mem_support_iff,
      not_forall, Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
    intro x h₁ h₂
    use x, h₁
    contrapose! h₂
    replace h₂ : g x y = 0 := h₂
    simp [h₂]⟩

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem bind_apply {Y : Type*} (f : X →c 𝒮) (g : X → Y →c 𝒮) (y : Y) :
    f.bind g y = ω∑ (i : f.support), f i * g i y := by rfl

omit [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem bind_mono_right {Y : Type*} (f : X →c 𝒮) (g₁ g₂ : X → Y →c 𝒮) (h : g₁ ≤ g₂) :
    f.bind g₁ ≤ f.bind g₂ := by
  intro y
  simp [bind]
  apply ωSum_mono fun n ↦ ?_
  gcongr
  exact h n y

omit [MulLeftMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem bind_mono_left {Y : Type*} {f₁ f₂ : X →c 𝒮} (g : X → Y →c 𝒮) (h : f₁ ≤ f₂) :
    f₁.bind g ≤ f₂.bind g := by
  intro y
  simp [bind]
  refine ωSum_le_of_finset fun S ↦ ?_
  classical
  let S' : Finset ↑f₂.support := S.filterMap (fun ⟨x, _⟩ ↦ if h' : f₂ x = 0 then none else some ⟨x, h'⟩) (by simp_all)
  apply le_trans _ (le_ωSum_of_finset S')
  rw [Finset.sum_bij (t:=S.image (·.val)) (g:=fun x ↦ f₁ x * (g x) y) (fun x _ ↦ x.val)]
  · rw [Finset.sum_bij (s:=S') (t:=S'.image (·.val)) (g:=fun x ↦ f₂ x * (g x) y) (fun x _ ↦ x)]
    · have : S.image (·.val) ⊆ S'.image (·.val) := by
        intro x
        simp_all [S']
        intro hx hx'
        clear hx'
        contrapose! hx
        have := h x
        simp_all
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg this _)
      · simp
        gcongr with x hx
        exact h x
      · simp
    · simp [S']; grind
    · grind
    · simp only [Finset.mem_image, Subtype.exists, mem_support_iff, ne_eq, exists_and_right,
      exists_eq_right, exists_prop, imp_self, implies_true]
    · intro _ _; rfl
  · simp +contextual
  · grind
  · simp only [Finset.mem_image, Subtype.exists, mem_support_iff, ne_eq, exists_and_right,
    exists_eq_right, exists_prop, imp_self, implies_true]
  · intro _ _; rfl

theorem bind_continuous_right {Y : Type*} (f : X →c 𝒮) :
    ωScottContinuous (f.bind (Y:=Y)) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨bind_mono_right f, ?_⟩
  intro C
  ext h
  simp only [bind, asdsad, ωSup_apply, mul_ωSup, ωSum_ωSup', coe_mk]
  congr

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem sum_apply [DecidableEq X] {Y : Type*} {f : X → Y →c 𝒮} {y : Y} (S : Finset X) :
    (∑ x ∈ S, f x) y = ∑ x ∈ S, f x y := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S hx ih => simp_all

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem ωSum_apply [Countable X] {Y : Type*} {f : X → Y →c 𝒮} {y : Y} :
    (ω∑ (x : X), f x) y = ω∑ (x : X), f x y := by
  simp [ωSum, Chain.map]
  congr!
  simp only [Function.comp_apply, sum_apply]
  congr!
  split <;> simp_all

theorem bind_continuous_left {Y : Type*} (g : X → Y →c 𝒮) :
    ωScottContinuous (bind (g:=g)) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun f₁ f₂ ↦ bind_mono_left g, ?_⟩
  intro C
  ext h
  simp only [bind, ωSup_apply, Chain.map, ωSup_mul, ωSum_ωSup', coe_mk]
  congr with i
  simp [OrderHom.comp]
  apply le_antisymm
  · refine ωSum_le_of_finset fun S ↦ ?_
    classical
    let S' : Finset ((C i).support) := (S.filterMap (fun ⟨x, hx⟩ ↦ if h : _ then some ⟨x, h⟩ else none) (by simp +contextual))
    apply le_trans (le_of_eq _) (le_ωSum_of_finset S')
    apply Finset.sum_bij_ne_zero (fun ⟨x, _⟩ _ hx ↦ ⟨x, by
      simp only [mem_support_iff, ne_eq]; contrapose! hx; exact mul_eq_zero_of_left hx ((g x).toFun h)⟩)
    · simp_all only [ne_eq, mem_support_iff, dite_not, Finset.mem_filterMap,
      Option.dite_none_left_eq_some, Option.some.injEq, Subtype.mk.injEq, exists_prop,
      Subtype.exists, ωSup_apply, ωSup_eq_zero_iff, Chain.coe_map, OrderHom.coe_mk,
      Function.comp_apply, not_forall, exists_and_right, exists_eq_right_right, Subtype.coe_eta,
      and_true, Subtype.forall, true_and, forall_exists_index, S']
      intro x n h h' h''
      clear h'
      contrapose! h
      grind [zero_mul]
    · grind only [cases eager Subtype]
    · simp_all only [mem_support_iff, ne_eq, dite_not, Finset.mem_filterMap,
      Option.dite_none_left_eq_some, Option.some.injEq, Subtype.exists, ωSup_apply,
      ωSup_eq_zero_iff, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, not_forall,
      exists_prop, forall_exists_index, and_imp, Subtype.forall, Subtype.mk.injEq, exists_and_right,
      exists_eq_right_right, not_false_eq_true, and_true, S']
      rintro x hx x' n hn h h' ⟨_⟩ h''
      apply Exists.intro ⟨i, hx⟩ h
    · grind
  · refine ωSum_le_of_finset fun S ↦ ?_
    classical
    let S' : Finset ((ωSup C).support) := (S.filterMap (fun ⟨x, hx⟩ ↦ if h : _ then some ⟨x, h⟩ else none) (by simp +contextual))
    apply le_trans (le_of_eq _) (le_ωSum_of_finset S')
    apply Finset.sum_bij_ne_zero (fun ⟨x, h₀⟩ _ hx ↦ ⟨x, by
      simp only [mem_support_iff, ωSup_apply, ne_eq, ωSup_eq_zero_iff, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, not_forall]
      exact Decidable.not_forall.mp fun a ↦ h₀ (a i)⟩)
    · simp_all only [ne_eq, mem_support_iff, ωSup_apply, ωSup_eq_zero_iff, Chain.coe_map,
      OrderHom.coe_mk, Function.comp_apply, not_forall, Finset.mem_filterMap,
      Option.dite_none_right_eq_some, Option.some.injEq, Subtype.mk.injEq, exists_prop,
      Subtype.exists, exists_and_right, exists_eq_right_right, Subtype.coe_eta, and_true,
      Subtype.forall, not_false_eq_true, true_and, S']
      intro x n h h'
      use i
    · grind only [cases eager Subtype]
    · grind only [Finset.mem_filterMap, Option.some.injEq, mem_support_iff, Subtype.mk.injEq,
        ωSup_eq_zero_iff, cases eager Subtype, cases Or]
    · grind

end OmegaContinuousNonUnitalSemiring

end Countsupp
