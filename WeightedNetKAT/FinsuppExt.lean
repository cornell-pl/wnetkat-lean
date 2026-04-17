module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order

@[expose] public section

open OmegaCompletePartialOrder

namespace Finsupp

def η' {X α : Type} [DecidableEq X] [DecidableEq α] [Zero α] [One α] (x : X) : X →₀ α := ⟨
  if (1 : α) = 0 then ∅ else {x}, fun y ↦ if x = y then 1 else 0, by intro x; split_ifs <;> simp_all; grind⟩

notation "η'[" α "]" => η' (α:=α)

section η'

variable {X α : Type} [DecidableEq X] [DecidableEq α] [Zero α] [One α]

@[simp]
theorem η'_apply (x y : X) :
    η'[α] x y = if x = y then 1 else 0 :=
  rfl

@[simp]
theorem η'_finSupp (x : X) : (η'[α] x).support = if (1 : α) = 0 then ∅ else {x} := rfl

end η'

section One

variable {α X : Type} [Fintype X] [Zero α] [One α] [DecidableEq α]

instance instOne : One (X →₀ α) :=
  ⟨if (1 : α) = 0 then ∅ else Fintype.elems, fun _ ↦ 1, by intro x; split_ifs <;> simp_all [Fintype.complete]⟩

@[simp]
theorem one_apply {x : X} : (1 : X →₀ α) x = 1 := rfl

end One

section zipWith'

variable {α β γ ι M M' N P G H R S : Type}

variable {M N P : Type}

variable [Zero M] [Zero N] [Zero P]

variable [DecidableEq α] [DecidableEq P]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith' (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  ⟨(g₁.support ∪ g₂.support).filter (fun x ↦ f (g₁ x) (g₂ x) ≠ 0),
    fun x ↦ f (g₁ x) (g₂ x), by intro x; simp; grind⟩

@[simp]
theorem zipWith'_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith' f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zipWith' {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith' f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  intro a; simp; grind

end zipWith'

section Basic

variable {ι F M N G H : Type}

section AddZeroClass
variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

variable [DecidableEq ι] [DecidableEq M]

instance (priority:=high) instAdd' : Add (ι →₀ M) where add := zipWith' (· + ·) (add_zero 0)

@[simp, norm_cast] lemma coe_add' (f g : ι →₀ M) : ⇑(f + g) = f + g := coe_add f g

instance instAddZeroClass' : AddZeroClass (ι →₀ M) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add'

instance instIsLeftCancelAdd' [IsLeftCancelAdd M] : IsLeftCancelAdd (ι →₀ M) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

end AddZeroClass

section

variable {α : Type} {β : Type} {γ : Type} {δ : Type} {ι : Type}

variable [MulZeroClass β]

variable [DecidableEq α] [DecidableEq β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : Mul (α →₀ β) :=
  ⟨zipWith' (· * ·) (mul_zero 0)⟩

theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

lemma support_mul_subset_left {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support := fun x hx => by
  aesop

lemma support_mul_subset_right {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₂.support := fun x hx => by
  aesop

omit [DecidableEq α] in
theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
  Finset.subset_inter support_mul_subset_left support_mul_subset_right

instance : MulZeroClass (α →₀ β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

instance : HMul β (α →₀ β) (α →₀ β) where
  hMul s f := ⟨f.support.filter (s * f · ≠ 0), (s * f ·), fun i ↦ by simp; contrapose; simp +contextual⟩

instance : HMul (α →₀ β) β (α →₀ β) where
  hMul f s := ⟨f.support.filter (f · * s ≠ 0), (f · * s), fun i ↦ by simp; contrapose; simp +contextual⟩

omit [DecidableEq α] in
theorem coe_hMul_left (s : β) (g : α →₀ β) : ⇑(s * g) = s * g :=
  rfl

omit [DecidableEq α] in
@[simp]
theorem hMul_left_apply {s : β} {g : α →₀ β} {a : α} : (s * g) a = s * g a :=
  rfl

-- lemma support_hMul_left_subset_left {s : β} {g : α →₀ β} :
--     (s * g).support ⊆ s.support := fun x hx => by
--   aesop

omit [DecidableEq α] in
lemma support_hMul_left_subset_right {s : β} {g : α →₀ β} :
    (s * g).support ⊆ g.support := fun x hx => by
  aesop

omit [DecidableEq α] in
theorem support_hMul_left [DecidableEq α] {s : β} {g : α →₀ β} :
    (s * g).support ⊆ g.support := by
  exact support_hMul_left_subset_right
  -- Finset.subset_inter support_mul_subset_left support_mul_subset_right

omit [DecidableEq α] in
theorem coe_hMul_right (s : β) (g : α →₀ β) : ⇑(g * s) = g * s :=
  rfl

omit [DecidableEq α] in
@[simp]
theorem hMul_right_apply {s : β} {g : α →₀ β} {a : α} : (g * s) a = g a * s :=
  rfl

-- lemma support_hMul_right_subset_left {s : β} {g : α →₀ β} :
--     (g * s).support ⊆ s.support := fun x hx => by
--   aesop

omit [DecidableEq α] in
lemma support_hMul_right_subset_right {s : β} {g : α →₀ β} :
    (g * s).support ⊆ g.support := fun x hx => by
  aesop

omit [DecidableEq α] in
theorem support_hMul_right [DecidableEq α] {s : β} {g : α →₀ β} :
    (g * s).support ⊆ g.support := by
  exact support_hMul_right_subset_right
  -- Finset.subset_inter support_mul_subset_left support_mul_subset_right

end

end Basic

section Basic

variable {M : Type}
  [Semiring M]
  [PartialOrder M]
  [OrderBot M]
  [MulLeftMono M]
  [MulRightMono M]
  [IsPositiveOrderedAddMonoid M]

variable {ι : Type}

variable [DecidableEq ι] [DecidableEq M]

instance : LE (ι →₀ M) where
  le f g := ∀ x, f x ≤ g x

instance {f : ι →₀ M} {p : ι → Prop} [DecidablePred p] : Decidable (∀ x ∈ f.support, p x) :=
  if h : f.support.filter p = f.support then
    .isTrue (by simp [Finset.filter_eq_self] at h; simp; exact h)
  else
    .isFalse (by simp [Finset.filter_eq_self] at h; simp; exact h)

instance : PartialOrder (ι →₀ M) where
  le_refl _ _  := by simp
  le_antisymm f g hfg hgf := by ext i; apply le_antisymm (hfg i) (hgf i)
  le_trans f g h hfg hgh i := le_trans (hfg i) (hgh i)

instance : OrderBot (ι →₀ M) where
  bot := 0
  bot_le a i := by simp

instance : MulLeftMono (ι →₀ M) := ⟨fun a _ _ h i ↦ mul_le_mul_right (h i) (a i)⟩
instance : MulRightMono (ι →₀ M) := ⟨fun a _ _ h i ↦ mul_le_mul_left (h i) (a i)⟩

instance : AddCommMonoid (ι →₀ M) where
  add_assoc _ _ _ := by ext; apply add_assoc
  add_comm _ _ := by ext; apply add_comm
  nsmul n f := if h₀ : n = 0 then 0 else ⟨f.support.filter (fun i ↦ n * f i ≠ 0), fun i ↦ n * f i, by
    intro i
    simp only [ne_eq, Finset.mem_filter, mem_support_iff, and_iff_right_iff_imp]
    contrapose!
    simp +contextual⟩
  nsmul_succ n f := by
    ext i
    simp
    split_ifs <;> simp_all [right_distrib]

omit [PartialOrder M] [OrderBot M] [MulLeftMono M] [MulRightMono M] [IsPositiveOrderedAddMonoid M] in
@[simp]
theorem sum_apply''' {Y : Type} [DecidableEq Y] {S : Finset ι} {f : ι → Y →₀ M} {a : Y} :
    (∑ x ∈ S, f x) a = ∑ x ∈ S, f x a := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S hx ih => simp_all

omit [OrderBot M] [IsPositiveOrderedAddMonoid M] in
instance : IsPositiveOrderedAddMonoid (ι →₀ M) where
  add_le_add_left _ _ hfg c i := add_le_add_left (hfg i) (c i)
  bot_eq_zero := rfl

instance : NonUnitalSemiring (ι →₀ M) where
  left_distrib f g h := by ext i; exact LeftDistribClass.left_distrib (f i) (g i) (h i)
  right_distrib f g h := by ext i; exact RightDistribClass.right_distrib (f i) (g i) (h i)
  mul_assoc a b c := by ext i; exact mul_assoc (a i) (b i) (c i)

variable {ι : Type} {Y : Type}

def bind [DecidableEq M] [DecidableEq Y] (f : ι →₀ M) (g : ι → Y →₀ M) : Y →₀ M :=
  ⟨(f.support.biUnion (fun x ↦ (g x).support.filter (fun y ↦ f x * g x y ≠ 0))),
    fun y ↦ ∑ x : f.support, f x * g x y, by
    intro y
    simp
    congr! 2 with x
    simp
    intro h h'
    contrapose! h'
    simp_all⟩

end Basic

section OmegaCompletePartialOrder

variable {M : Type}
  [Semiring M]
  [OmegaCompletePartialOrder M]
  [OrderBot M]
  [MulLeftMono M]
  [MulRightMono M]
  [IsPositiveOrderedAddMonoid M]
  [OmegaContinuousNonUnitalSemiring M]

variable {ι : Type}

variable [DecidableEq ι] [DecidableEq M]

omit [OrderBot M] [IsPositiveOrderedAddMonoid M] in
instance [Fintype ι] : OmegaCompletePartialOrder (ι →₀ M) where
  ωSup C :=
    let C' : ι → M := fun x ↦ ωSup (C.map ⟨(· x), (fun ⦃_ _ ⦄ a ↦ a x)⟩)
    ⟨Fintype.elems.filter (C' · ≠ 0), C', (by simp [C', Fintype.complete])⟩
  le_ωSup C i hi := le_ωSup_of_le i (by simp)
  ωSup_le C m hm i := by
    simp only [ne_eq, coe_mk, ωSup_le_iff]
    exact fun j ↦ hm j i

omit [MulLeftMono M] [MulRightMono M] [OmegaContinuousNonUnitalSemiring M] [DecidableEq M] in
@[simp]
theorem ωSup_apply {ι : Type} [Fintype ι] [DecidableEq M] (C : Chain (ι →₀ M)) (x : ι) :
    (ωSup C) x = ωSup (C.map ⟨(· x), (fun ⦃_ _⦄ a ↦ a x)⟩) := rfl

open OmegaContinuousNonUnitalSemiring in
instance [Fintype ι] : OmegaContinuousNonUnitalSemiring (ι →₀ M) where
  ωScottContinuous_add_left := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, fun C ↦ ?_⟩
    ext x
    simp only [coe_add', Pi.add_apply, ωSup_apply, add_ωSup]
    congr
  ωScottContinuous_add_right := by
    refine fun m ↦ ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, fun C ↦ ?_⟩
    ext x
    simp only [coe_add', Pi.add_apply, ωSup_apply, ωSup_add]
    congr
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

omit [MulLeftMono M] [MulRightMono M] [OmegaContinuousNonUnitalSemiring M] [DecidableEq ι] in
@[simp]
theorem ωSum_apply [Countable ι] {Y : Type} [DecidableEq Y] [Fintype Y] {f : ι → Y →₀ M} {y : Y} :
    (ω∑ (x : ι), f x) y = ω∑ (x : ι), f x y := by
  simp [ωSum, Chain.map]
  congr!
  simp only [Function.comp_apply, sum_apply''']
  congr!
  split <;> simp_all

end OmegaCompletePartialOrder

end Finsupp
