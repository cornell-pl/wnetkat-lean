import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring.RingNF

set_option grind.warning false

class WeightedAdd (α : Type) where
  /-- Weighted addition. Type `a ⨁ b` using `\O+`. -/
  wAdd : α → α → α

class WeightedMul (α : Type) where
  /-- Weighted multiplication. Type `a ⨀ b` using `\O.`. -/
  wMul : α → α → α

@[inherit_doc] infixl:65 " ⨁ " => WeightedAdd.wAdd
@[inherit_doc] infixl:70 " ⨀ " => WeightedMul.wMul

@[simp] instance : WeightedAdd ℕ := ⟨(· + ·)⟩
@[simp] instance : WeightedMul ℕ := ⟨(· * ·)⟩

/-- info: 1 ⨁ 2 ⨀ 3 : ℕ -/
#guard_msgs in
#check 1 ⨁ 2 ⨀ 3

  /-- Weighted zero. Type `𝟘` using `\b0`. -/
class WeightedZero (α : Type) where wZero : α
  /-- Weighted one. Type `𝟙` using `\b1`. -/
class WeightedOne (α : Type) where wOne : α

notation "𝟘" => WeightedZero.wZero
notation "𝟙" => WeightedOne.wOne

class WeightedPreSemiring (α : Type) extends
    WeightedAdd α, WeightedMul α, WeightedZero α where
  wAdd_assoc (a b c : α) : a ⨁ b ⨁ c = a ⨁ (b ⨁ c)
  wZero_add (a : α) : 𝟘 ⨁ a = a
  add_wZero (a : α) : a ⨁ 𝟘 = a
  wNsmul : ℕ → α → α
  wNsmul_wZero (a : α) : wNsmul 0 a = 𝟘
  wNsmul_succ (n : ℕ) (x : α) : wNsmul (n + 1) x = wNsmul n x ⨁ x
  wAdd_comm (a b : α) : a ⨁ b = b ⨁ a
  left_distrib (a b c : α) : a ⨀ (b ⨁ c) = a ⨀ b ⨁ a ⨀ c
  right_distrib (a b c : α) : (a ⨁ b) ⨀ c = a ⨀ c ⨁ b ⨀ c
  wZero_mul (a : α) : 𝟘 ⨀ a = 𝟘
  mul_wZero (a : α) : a ⨀ 𝟘 = 𝟘
  mul_assoc (a b c : α) : a ⨀ b ⨀ c = a ⨀ (b ⨀ c)

class WeightedSemiring (α : Type) extends WeightedPreSemiring α, WeightedOne α where
  wOne_mul (a : α) : 𝟙 ⨀ a = a
  mul_wOne (a : α) : a ⨀ 𝟙 = a
  natCast : ℕ → α
  natCast_zero : natCast 0 = 𝟘
  natCast_succ (n : ℕ) : natCast (n + 1) = natCast n ⨁ 𝟙
  wNpow : ℕ → α → α
  wNpow_succ (n : ℕ) (x : α) : wNpow (n + 1) x = wNpow n x ⨀ x
  wNpow_zero (x : α) : wNpow 0 x = 𝟙

attribute [simp] WeightedPreSemiring.wZero_add
attribute [simp] WeightedPreSemiring.add_wZero
attribute [simp] WeightedSemiring.wOne_mul
attribute [simp] WeightedSemiring.mul_wOne
attribute [simp] WeightedPreSemiring.wZero_mul
attribute [simp] WeightedPreSemiring.mul_wZero

variable {α : Type}

instance [WeightedPreSemiring α] : Std.Commutative (fun (a b : α) ↦ a ⨁ b) :=
  ⟨WeightedPreSemiring.wAdd_comm⟩
instance [WeightedPreSemiring α] : Std.Associative (fun (a b : α) ↦ a ⨁ b) :=
  ⟨WeightedPreSemiring.wAdd_assoc⟩

def WeightedPreSemiring.toAddCommMonoid (α : Type) [i : WeightedPreSemiring α] :
    AddCommMonoid α where
  add := i.wAdd
  add_assoc := i.wAdd_assoc
  zero := i.wZero
  zero_add := i.wZero_add
  add_zero := i.add_wZero
  nsmul := i.wNsmul
  nsmul_zero := i.wNsmul_wZero
  nsmul_succ := i.wNsmul_succ
  add_comm := i.wAdd_comm

def WeightedSemiring.toSemiring (α : Type) [i : WeightedSemiring α] : Semiring α where
  add := i.wAdd
  add_assoc := i.wAdd_assoc
  zero := i.wZero
  zero_add := i.wZero_add
  add_zero := i.add_wZero
  nsmul := i.wNsmul
  nsmul_zero := i.wNsmul_wZero
  nsmul_succ := i.wNsmul_succ
  add_comm := i.wAdd_comm
  mul := i.wMul
  left_distrib := i.left_distrib
  right_distrib := i.right_distrib
  zero_mul := i.wZero_mul
  mul_zero := i.mul_wZero
  mul_assoc := i.mul_assoc
  one := i.wOne
  one_mul := i.wOne_mul
  mul_one := i.mul_wOne
  natCast := i.natCast
  natCast_zero := i.natCast_zero
  natCast_succ := i.natCast_succ
  npow := i.wNpow
  npow_zero := i.wNpow_zero
  npow_succ := i.wNpow_succ

def WeightedSemiring.ofSemiring (α : Type) [i : Semiring α] : WeightedSemiring α where
  wAdd := i.add
  wAdd_assoc := i.add_assoc
  wZero := i.zero
  wZero_add := i.zero_add
  add_wZero := i.add_zero
  wNsmul := i.nsmul
  wNsmul_wZero := i.nsmul_zero
  wNsmul_succ := i.nsmul_succ
  wAdd_comm := i.add_comm
  wMul := i.mul
  left_distrib := i.left_distrib
  right_distrib := i.right_distrib
  wZero_mul := i.zero_mul
  mul_wZero := i.mul_zero
  mul_assoc := i.mul_assoc
  wOne := i.one
  wOne_mul := i.one_mul
  mul_wOne := i.mul_one
  natCast := i.natCast
  natCast_zero := i.natCast_zero
  natCast_succ := i.natCast_succ
  wNpow := i.npow
  wNpow_zero := i.npow_zero
  wNpow_succ := i.npow_succ

instance (priority := 100) : WeightedSemiring ℕ := WeightedSemiring.ofSemiring ℕ

class WeightedLE (α : Type) where
  wle : α → α → Prop

/-- Weighted less-than-or-equal defined by the natural order. -/
@[reducible] def wLe {α : Type} [WeightedLE α] (a b : α) := WeightedLE.wle a b
@[inherit_doc] infix:50 " ≼ " => wLe

/-- Weighted greater-than-or-equal defined by the natural order. -/
@[reducible] def wGe {α : Type} [WeightedLE α] (a b : α) := b ≼ a
@[inherit_doc] infix:50 " ≽ " => wGe


/-- Weighted less-than-or-equal defined by the natural order. -/
@[reducible] def wLt {α : Type} [WeightedLE α] (a b : α) := a ≼ b ∧ a ≠ b
@[inherit_doc] infix:50 " ≺ " => wLt

instance (priority := 100) : WeightedLE ℕ := ⟨LE.le⟩

@[simp] theorem WeightedLE.nat_wle_iff {a b : ℕ} : a ≼ b ↔ a ≤ b := by rfl

/-- info: 1 ≼ 2 : Prop -/
#guard_msgs in
#check 1 ≼ 2

class WeightedPartialOrder (α) extends WeightedLE α where
  wle_refl (a : α) : a ≼ a
  wle_trans {a b c : α} : a ≼ b → b ≼ c → a ≼ c
  wle_antisymm {a b : α} : a ≼ b → b ≼ a → a = b

attribute [simp] WeightedPartialOrder.wle_refl
attribute [refl] WeightedPartialOrder.wle_refl

theorem WeightedPartialOrder.wle_antisymm_iff [WeightedPartialOrder α] {a b : α} :
    a = b ↔ a ≼ b ∧ b ≼ a := ⟨by simp_all, fun h ↦ wle_antisymm h.left h.right⟩

class WeightedNaturalPartialOrder (α) [WeightedSemiring α] extends WeightedPartialOrder α where
  wle_natural (a b : α) : a ≼ b ↔ ∃ c, a ⨁ c = b

def WeightedMonotone [WeightedLE α] {ι : Type} [WeightedLE ι] (f : ι → α) : Prop :=
  ∀ {s₁ s₂}, s₁ ≼ s₂ → f s₁ ≼ f s₂
def WeightedAntitone [WeightedLE α] {ι : Type} [WeightedLE ι] (f : ι → α) : Prop :=
  ∀ {s₁ s₂}, s₁ ≼ s₂ → f s₂ ≼ f s₁

def WeightedChain (α : Type) [WeightedPartialOrder α] :=
  { f : ℕ → α // WeightedMonotone f }
def WeightedChain' (α : Type) [WeightedPartialOrder α] :=
  { f : ℕ → α // WeightedAntitone f }

instance [WeightedPartialOrder α] : FunLike (WeightedChain α) ℕ α :=
  ⟨(·.val), by intro ⟨a, ha⟩ ⟨b, hb⟩ c; simp_all⟩
instance [WeightedPartialOrder α] : FunLike (WeightedChain' α) ℕ α :=
  ⟨(·.val), by intro ⟨a, ha⟩ ⟨b, hb⟩ c; simp_all⟩

@[ext]
theorem WeightedChain.ext {α : Type} [WeightedPartialOrder α] (C₁ C₂ : WeightedChain α)
    (h : ∀ i, C₁ i = C₂ i) : C₁ = C₂ := by cases C₁; cases C₂; congr; ext; simp_all [DFunLike.coe]

theorem WeightedChain.val_apply {α : Type} [WeightedPartialOrder α] (C : WeightedChain α) (n : ℕ) :
    C.val n = C n := rfl
@[simp]
theorem WeightedChain.mk_val_apply {α : Type} [WeightedPartialOrder α] {f : ℕ → α}
    (hf : WeightedMonotone f) (n : ℕ) : (⟨f, hf⟩ : WeightedChain α).val n = f n := rfl

def WeightedChain.map {α β : Type} [WeightedPartialOrder α] [WeightedPartialOrder β]
    (C : WeightedChain α) (f : α → β) (hf : WeightedMonotone f) : WeightedChain β :=
  ⟨fun n ↦ f (C n), fun hab ↦ hf (C.property hab)⟩

class WeightedOmegaCompletePartialOrder (α : Type) extends
    WeightedPartialOrder α where
  wSup : WeightedChain α → α
  /-- wSup is an upper bound of the increasing sequence -/
  le_wSup (c : WeightedChain α) (i : ℕ) : c i ≼ wSup c
  /-- wSup is a lower bound of the set of upper bounds of the increasing sequence -/
  wSup_le (c : WeightedChain α) (x : α) : (∀ (i : ℕ), c i ≼ x) → wSup c ≼ x

theorem WeightedOmegaCompletePartialOrder.le_wSup_of_le {α : Type}
    [WeightedOmegaCompletePartialOrder α] {a : α} {C : WeightedChain α} (i : ℕ) (h : a ≼ C i) :
    a ≼ wSup C :=
  WeightedPartialOrder.wle_trans h (le_wSup C i)

@[gcongr]
theorem WeightedOmegaCompletePartialOrder.wsup_le_of_le {α : Type} [WeightedOmegaCompletePartialOrder α] (C₁ C₂ : WeightedChain α)
    (h : ∀ i, C₁ i ≼ C₂ i) : wSup C₁ ≼ wSup C₂ := by
    cases C₁
    cases C₂
    apply wSup_le
    intro i
    apply le_wSup_of_le i
    apply_assumption

open WeightedOmegaCompletePartialOrder in
def WeightedOmegaContinuous {ι : Type} [WeightedOmegaCompletePartialOrder ι]
    [WeightedOmegaCompletePartialOrder α]
    (f : ι → α) (h : WeightedMonotone f) : Prop :=
  ∀ C, f (wSup C) = wSup (C.map f h)

/--
A weighted semiring is _ω-bicontinuous_ iff

1. ≼ is positive, i.e., 𝟘 is the least element.
2. both ⨁ and ⨀ are monotonic in both arguments, i.e. for all s₁,s₂s₃ ∈ α,

  s₂ ≼ s₃ implies s₁ ⨁ s₂ ≼ s₁ ⨁ s₃ and s₁ ⨀ s₂ ≼ s₁ ⨀ s₃ and s₂ ⨀ s₁ ≼ s₃ ⨀ s₁.

3. both ⨁ and ⨀ are ω-continuous in both arguments, i.e. for ∘ ∈ {⨁,⨀}, we have

  ∀ ω-chains C = {s₀ ≼ s₁ ≼ ⋯}, ∀ s ∈ α,
    s ∘ wSup C = wSup (C.map fun s' ↦ s ∘ s')) and wSup C ∘ s = wSup (C.map fun s' ↦ s' ∘ s))
-/
class WeightedOmegaContinuousPreSemiring (α : Type) [WeightedPreSemiring α] extends
    WeightedOmegaCompletePartialOrder α where
  /-- 1. ≼ is positive. -/
  wle_positive (a : α) : 𝟘 ≼ a
  /-- 2. both ⨁ and ⨀ are monotonic in both arguments. -/
  wAdd_mono (s₁ : α) : WeightedMonotone (s₁ ⨁ ·)
  wMul_mono_left (s₁ : α) : WeightedMonotone (s₁ ⨀ ·)
  -- wMul_mono_right (s₁ s₂ s₃ : α) (hab : s₂ ≼ s₃) : s₂ ⨀ s₁ ≼ s₃ ⨀ s₁
  wMul_mono_right (s₁ : α) : WeightedMonotone (· ⨀ s₁)
  /-- 3. both ⨁ and ⨀ are ω-continuous in both arguments. -/
  wAdd_wSup (s : α) : WeightedOmegaContinuous (s ⨁ ·) (wAdd_mono s)
  wSup_wAdd (s : α) : WeightedOmegaContinuous (· ⨁ s) (by
    simp only [WeightedPreSemiring.wAdd_comm]; exact wAdd_mono _)
  wMul_wSup (s : α) : WeightedOmegaContinuous (s ⨀ ·) (wMul_mono_left s)
  wSup_wMul (s : α) : WeightedOmegaContinuous (· ⨀ s) (wMul_mono_right s)

def WeightedOmegaContinuousPreSemiring.wAdd_mono_left {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] := i.wAdd_mono
theorem WeightedOmegaContinuousPreSemiring.wAdd_mono_right {α : Type} [WeightedPreSemiring α]
    [WeightedOmegaContinuousPreSemiring α] (s₁ : α) : WeightedMonotone (· ⨁ s₁) := by
  simp [WeightedPreSemiring.wAdd_comm]; exact wAdd_mono s₁

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem WeightedOmegaContinuousAddLeft {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} {s : α}: (wSup C) ⨁ s = wSup (C.map (· ⨁ s) (wAdd_mono_right _)) := by
    apply wSup_wAdd
open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem WeightedOmegaContinuousAddRight {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} {s : α}: s ⨁ (wSup C) = wSup (C.map (s ⨁ ·) (wAdd_mono_left _)) := by
    apply wAdd_wSup
open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem WeightedOmegaContinuousAddRight' {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} {s : α} :
    s ⨁ (wSup C) = wSup ⟨fun i ↦ s ⨁ C i, fun hab ↦ wAdd_mono_left _ (C.prop hab)⟩ := by
    apply wAdd_wSup

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem WeightedOmegaContinuousMulLeft {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} {s : α}: (wSup C) ⨀ s = wSup (C.map (· ⨀ s) (wMul_mono_right _)) := by
    apply wSup_wMul
open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem WeightedOmegaContinuousMulRight {α : Type} [WeightedPreSemiring α]
    [i : WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} {s : α}: s ⨀ (wSup C) = wSup (C.map (s ⨀ ·) (wMul_mono_left _)) := by
    apply wMul_wSup

@[simp]
theorem wZero_wLe [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] {x : α} : 𝟘 ≼ x :=
  WeightedOmegaContinuousPreSemiring.wle_positive x
@[simp]
theorem wLe_wZero_iff [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] {x : α} : x ≼ 𝟘 ↔ x = 𝟘 := by
  constructor
  · intro h
    apply WeightedPartialOrder.wle_antisymm h (WeightedOmegaContinuousPreSemiring.wle_positive x)
  · rintro ⟨_⟩; simp

def WeightedLE.wle.trans_eq {a b c : α} [WeightedPartialOrder α] (h : a ≼ b) (h' : b = c) :
    a ≼ c := by
  subst_eqs
  assumption

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
@[simp]
theorem wSup_eq_zero_iff [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] {C : WeightedChain α} :
    wSup C = 𝟘 ↔ ∀ i, C i = 𝟘 :=
  ⟨fun h i ↦ wLe_wZero_iff.mp <| (le_wSup C i).trans_eq h,
    fun h ↦ wle_antisymm (wSup_le C 𝟘 (wLe_wZero_iff.mpr <| h ·)) (wle_positive (wSup C))⟩

section Pi

variable {X : Type} {𝒮 : Type}

instance WeightedZero.instPi [WeightedZero 𝒮] : WeightedZero (X → 𝒮) where wZero := fun _ ↦ 𝟘
instance WeightedOne.instPi [WeightedOne 𝒮] : WeightedOne (X → 𝒮) where wOne := fun _ ↦ 𝟙

instance WeightedAdd.instPi [WeightedAdd 𝒮] : WeightedAdd (X → 𝒮) where wAdd a b x := a x ⨁ b x
instance WeightedMul.instPi [WeightedMul 𝒮] : WeightedMul (X → 𝒮) where wMul a b x := a x ⨀ b x

attribute [local simp] WeightedAdd.instPi
attribute [local simp] WeightedMul.instPi

instance WeightedPreSemiring.instPi [WeightedPreSemiring 𝒮] : WeightedPreSemiring (X → 𝒮) where
  wZero := fun _ ↦ 𝟘
  wAdd_assoc := by simp [wAdd_assoc]
  wZero_add := by simp [wZero_add]
  add_wZero := by simp [wZero_add]
  wNsmul n a x := wNsmul n (a x)
  wNsmul_wZero := by simp [wNsmul_wZero]
  wNsmul_succ := by simp [wNsmul_succ]
  wAdd_comm := by simp [wAdd_comm]
  left_distrib := by simp [left_distrib]
  right_distrib := by simp [right_distrib]
  wZero_mul := by simp [wZero_mul]
  mul_wZero := by simp [mul_wZero]
  mul_assoc := by simp [mul_assoc]

attribute [local simp] WeightedPreSemiring.instPi

open WeightedPreSemiring in
instance WeightedSemiring.instPi [WeightedSemiring 𝒮] : WeightedSemiring (X → 𝒮) := {
  WeightedPreSemiring.instPi with
  wOne_mul _ := by ext; apply wOne_mul
  mul_wOne _ := by ext; apply mul_wOne
  natCast_succ _ := by ext; apply natCast_succ
  wNpow_succ _ _ := by ext; apply wNpow_succ
  wNpow_zero _ := by ext; apply wNpow_zero
  natCast n _ := natCast n
  natCast_zero := by simp [natCast_zero]
  wNpow n a b := wNpow n (a b)
}

attribute [local simp] WeightedSemiring.instPi

instance WeightedLE.instPi [WeightedLE 𝒮] : WeightedLE (X → 𝒮) where
  wle a b := ∀ x, a x ≼ b x

open WeightedPartialOrder in
instance WeightedPartialOrder.instPi [WeightedPartialOrder 𝒮] : WeightedPartialOrder (X → 𝒮) where
  wle_refl a x := by simp
  wle_trans {a b c} hab hbc x := wle_trans (hab x) (hbc x)
  wle_antisymm {a b} hab hba := by ext x; exact wle_antisymm (hab x) (hba x)

instance WeightedOmegaCompletePartialOrder.instPi [WeightedOmegaCompletePartialOrder 𝒮] :
    WeightedOmegaCompletePartialOrder (X → 𝒮) where
  wSup C x := wSup ⟨(C · x), (C.prop · x)⟩
  le_wSup C i x := le_wSup ⟨(C · x), (C.prop · x)⟩ i
  wSup_le C _ h x := wSup_le ⟨(C · x), (C.prop · x)⟩ _ (h · x)

open WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
instance WeightedOmegaContinuousPreSemiring.instPi [WeightedPreSemiring 𝒮]
    [WeightedOmegaContinuousPreSemiring 𝒮] : WeightedOmegaContinuousPreSemiring (X → 𝒮) where
  wle_positive _ _ := by simp [wle_positive]
  wAdd_mono s₁ s₂ s₃ h x := wAdd_mono (s₁ x) (h x)
  wMul_mono_left s₁ s₂ s₃ h x := wMul_mono_left (s₁ x) (h x)
  wMul_mono_right s₁ s₂ s₃ h x := wMul_mono_right (s₁ x) (h x)
  wAdd_wSup s C := by ext x; exact wAdd_wSup (s x) (C.map (· x) (· x))
  wSup_wAdd s C := by ext x; exact wSup_wAdd (s x) (C.map (· x) (· x))
  wMul_wSup s C := by ext x; exact wMul_wSup (s x) (C.map (· x) (· x))
  wSup_wMul s C := by ext x; exact wSup_wMul (s x) (C.map (· x) (· x))

end Pi

theorem WeightedPartialOrder.wlt_trans {α : Type} [WeightedPartialOrder α] {a b c : α}
    (hab : a ≺ b) (hbc : b ≺ c) : a ≺ c := by
  simp_all [wLt]
  constructor
  · exact wle_trans hab.left hbc.left
  · have : ¬a = b ∧ ¬b = c := by simp_all only [not_false_eq_true, and_self]
    contrapose! this; subst_eqs
    exact fun _ ↦ wle_antisymm hbc.left hab.left

@[simp]
theorem WeightedPartialOrder.not_lt_refl {α : Type} [WeightedPartialOrder α] {a : α} : ¬a ≺ a := by
  simp_all [wLt]
@[simp]
theorem WeightedPartialOrder.lt_not_symm {α : Type} [WeightedPartialOrder α] {a b : α}
    (hab : a ≺ b) (hba : b ≺ a) : False := by
  simp_all [wLt]
  suffices a = b by subst_eqs; simp_all
  exact wle_antisymm hab.left hba.left

def WeightedPartialOrder.lex (α β : Type)
  [WeightedPartialOrder α] [WeightedPartialOrder β] :
    WeightedPartialOrder (α × β) where
  wle := fun (a₁, b₁) (a₂, b₂) ↦ a₁ ≺ a₂ ∨ a₁ = a₂ ∧ b₁ ≼ b₂
  wle_refl := by intro; right; simp
  wle_trans := by
    simp
    intro a₁ b₁ a₂ b₂ a₃ b₃ h₁₂ h₂₃
    simp_all [wLe]
    rcases h₁₂ with h₁₂ | h₁₂ <;> rcases h₂₃ with h₂₃ | h₂₃
    · left; apply wlt_trans h₁₂ h₂₃
    · simp_all; assumption
    · simp_all; assumption
    · simp_all; apply wle_trans h₁₂.right h₂₃.right
  wle_antisymm := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁₂ h₂₁
    rcases h₁₂ with h₁₂ | h₁₂ <;> rcases h₂₁ with h₂₁ | h₂₁ <;> simp_all
    · exact lt_not_symm h₁₂ h₂₁
    · exact wle_antisymm h₁₂ h₂₁.right

instance WeightedPartialOrder.instWithBot {α : Type} [WeightedPartialOrder α] :
    WeightedPartialOrder (WithBot α) where
  wle a b :=
    match a, b with
    | ⊥, _ => true
    | _, ⊥ => false
    | some a, some b => a ≼ b
  wle_refl a := by simp [wLe]; split <;> simp
  wle_trans := by
    intro a b c hab hbc
    simp_all [wLe]
    split at * <;> split at * <;> simp_all
    apply wle_trans hab hbc
  wle_antisymm := by
    intro a b hab hba
    simp_all [wLe]
    split at * <;> split at * <;> simp_all
    exact congrArg some (wle_antisymm hab hba)

instance WeightedPartialOrder.instOption {α : Type} [WeightedPartialOrder α] :
    WeightedPartialOrder (Option α) where
  wle a b :=
    match a, b with
    | none, _ => true
    | _, none => false
    | some a, some b => a ≼ b
  wle_refl a := by simp [wLe]; split <;> simp
  wle_trans := by
    intro a b c hab hbc
    simp_all [wLe]
    split at * <;> split at * <;> simp_all
    apply wle_trans hab hbc
  wle_antisymm := by
    intro a b hab hba
    simp_all [wLe]
    split at * <;> split at * <;> simp_all
    exact wle_antisymm hab hba

-- instance WeightedOmegaCompletePartialOrder.instOption {α : Type} [WeightedOmegaCompletePartialOrder α] :
--     WeightedOmegaCompletePartialOrder (Option α) where
--   wSup := sorry
--   wSup_le := sorry
--   le_wSup := sorry

-- def WeightedOmegaCompletePartialOrder.lex (α β : Type)
--   [WeightedOmegaCompletePartialOrder α] [WeightedOmegaCompletePartialOrder β] [DecidableRel (wLe (α:=α))] [DecidableRel (wLe (α:=β))] :
--     WeightedOmegaCompletePartialOrder (α × β) := {WeightedPartialOrder.lex α β with
--   wSup C :=
--     letI := WeightedPartialOrder.lex α β
--     let α_sup := wSup (C.map (·.fst) (by intro a b hab; simp; rcases hab <;> simp_all))
--     let Cβ : WeightedChain β := ⟨fun i ↦
--       let C' : List (Option β) := List.ofFn (fun (j : Fin i) ↦
--         let p := C.val j; if p.1 ≼ α_sup then some p.2 else none)
--       let C'' := C'.filterMap (·)
--       letI : Max β := ⟨fun a b ↦ if a ≼ b then a else b⟩
--       C''[i]?.getD (C''.max?.get (by simp_all [C', C'']; sorry))
--       ,
--       sorry⟩
--     ⟨α_sup, wSup Cβ⟩
--   le_wSup := sorry
--   wSup_le := sorry
-- }

variable {ι : Type}

/-- `⨁ x ∈ I, f x` is the finite sum over `f`. -/
def WeightedFinsum [WeightedPreSemiring α] (I : Finset ι) (f : ι → α) : α :=
  I.fold (· ⨁ ·) 𝟘 f

namespace BigOperators

syntax (name := bigweightedfinsum) "⨁ᶠ " bigOpBinders ("with " term)? ", " term:67 : term

macro_rules (kind := bigweightedfinsum)
  | `(⨁ᶠ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(WeightedFinsum $s (fun $x ↦ $v))

variable {ι : Type} [WeightedPreSemiring α]

open Lean Meta
open Elab Term Tactic TryThis

open PrettyPrinter.Delaborator SubExpr
open scoped Batteries.ExtendedBinder

/-- The possibilities we distinguish to delaborate the finset indexing a big operator:
* `finset s` corresponds to `∑ x ∈ s, f x`
* `univ` corresponds to `∑ x, f x`
* `filter s p` corresponds to `∑ x ∈ s with p x, f x`
* `filterUniv p` corresponds to `∑ x with p x, f x`
-/
private inductive FinsetResult where
  | finset (s : Term)
  | univ
  | filter (s : Term) (p : Term)
  | filterUniv (p : Term)

/-- Delaborates a finset indexing a big operator. In case it is a `Finset.filter`, `i` is used for
the binder name. -/
private def delabFinsetArg (i : Ident) : DelabM FinsetResult := do
  let s ← getExpr
  if s.isAppOfArity ``Finset.univ 2 then
    return .univ
  else if s.isAppOfArity ``Finset.filter 4 then
    let #[_, _, _, t] := s.getAppArgs | failure
    let p ←
      withNaryArg 1 do
        if (← getExpr).isLambda then
          withBindingBody i.getId delab
        else
          let p ← delab
          return (← `($p $i))
    if t.isAppOfArity ``Finset.univ 2 then
      return .filterUniv p
    else
      let ss ← withNaryArg 3 delab
      return .filter ss p
  else
    let ss ← delab
    return .finset ss

/-- Delaborator for `WeightedFinsum`. The `pp.funBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab WeightedFinsum] def delabWeightedFinsum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
  let res ← withNaryArg 3 <| delabFinsetArg i
  match res with
  | .finset ss => `(⨁ᶠ $i:ident ∈ $ss, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(⨁ᶠ $binder:bigOpBinder, $body)
  | .filter ss p =>
    `(⨁ᶠ $i:ident ∈ $ss with $p, $body)
  | .filterUniv p =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(⨁ᶠ $binder:bigOpBinder with $p, $body)

/-- info: fun I f ↦ ⨁ᶠ x ∈ I, f x : Finset ι → (ι → α) → α -/
#guard_msgs in
#check fun (I : Finset ι) (f : ι → α) ↦ ⨁ᶠ x ∈ I, f x

end BigOperators

section

variable {α : Type}
variable [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]

variable {I : Type} [e : Encodable I]

open WeightedOmegaContinuousPreSemiring WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedPreSemiring

@[simp]
theorem wle_wAdd (s s' : α) : s ≼ s ⨁ s' := by
  have := wAdd_mono s (wle_positive s')
  simpa [add_wZero]

@[simp]
theorem wAdd_eq_zero_iff {x y : α} : x ⨁ y = 𝟘 ↔ x = 𝟘 ∧ y = 𝟘 := by
  constructor
  · intro h
    constructor
    · apply wle_antisymm (by rw [← h]; apply wle_wAdd) (wle_positive x)
    · apply wle_antisymm (by rw [← h, wAdd_comm]; apply wle_wAdd) (wle_positive y)
  · rintro ⟨⟨_⟩, ⟨_⟩⟩
    exact wZero_add 𝟘
example {x y : α} : x ⨁ y ≠ 𝟘 ↔ x ≠ 𝟘 ∨ y ≠ 𝟘 := by
  simp [wAdd_eq_zero_iff, imp_iff_not_or]

omit [WeightedOmegaContinuousPreSemiring α] in
@[simp] theorem WeightedFinsup_empty {f : ι → α} : ⨁ᶠ i ∈ ∅, f i = 𝟘 := by rfl
omit [WeightedOmegaContinuousPreSemiring α] in
@[simp] theorem WeightedFinsup_singleton {f : ι → α} (a : ι) : ⨁ᶠ i ∈ {a}, f i = f a := by
  simp [WeightedFinsum]

theorem Finset.fold_range {X : Type} {n : ℕ} {f : X → X → X} [Std.Commutative f] [Std.Associative f]
    {g : ℕ → X} {init : X} :
    (Finset.range n).fold f init g = n.fold (fun a _ b ↦ f (g a) b) init := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.fold_succ]
    rw [← ih]; clear ih
    rw [range_succ]
    simp

theorem Finset.fold_range_succ {X : Type} {n : ℕ} {f : X → X → X} [Std.Commutative f] [Std.Associative f]
    {g : ℕ → X} {init : X} :
    (Finset.range (n + 1)).fold f init g = f (g n) (n.fold (fun a _ b ↦ f (g a) b) init) := by
  simp [Finset.fold_range]

omit [WeightedOmegaContinuousPreSemiring α] in
@[simp]
theorem WeightedFinsup_range_succ {a : ℕ} {f : ℕ → α} :
      ⨁ᶠ i ∈ Finset.range (a + 1), f i
    = (⨁ᶠ i ∈ Finset.range a, f i) ⨁ f a := by
  simp [WeightedFinsum]
  simp [Finset.fold_range, wAdd_comm]

omit [WeightedOmegaContinuousPreSemiring α] in
@[simp]
theorem WeightedFinsup_insert {a : ι} {S : Finset ι} [DecidableEq ι] (h : a ∉ S) {f : ι → α} :
      ⨁ᶠ i ∈ insert a S, f i
    = f a ⨁ ⨁ᶠ i ∈ S, f i := by
  simp_all [WeightedFinsum]

omit [WeightedOmegaContinuousPreSemiring α] in
@[simp]
theorem WeightedFinsup_range_add {a b : ℕ} {f : ℕ → α} :
      ⨁ᶠ i ∈ Finset.range (a + b), f i
    = (⨁ᶠ i ∈ Finset.range a, f i) ⨁ ⨁ᶠ i ∈ Finset.range b, f (a + i) := by
  induction b with
  | zero => simp only [add_zero, Finset.range_zero, WeightedFinsup_empty, add_wZero]
  | succ b ih =>
    rw [← add_assoc]
    rw [WeightedFinsup_range_succ, WeightedFinsup_range_succ]
    rw [ih]
    rw [wAdd_assoc]

theorem WeightedFinsup_range_mono {f : ℕ → α} :
    WeightedMonotone fun n ↦ ⨁ᶠ i ∈ Finset.range n, f i := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ c hac ih =>
    simp only [WeightedFinsup_range_succ]
    apply wle_trans (wle_wAdd _ _) (wAdd_mono_right (f c) ih)

section BigOperators

-- open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring in
-- noncomputable def WeightedSum_chain [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]
--     [e : Encodable ι] (f : ι → α) : WeightedChain α :=
--   let f' i := if let some x := e.decode i then f x else 𝟘
--   ⟨fun n ↦ n.fold (fun i _ x ↦ f' i ⨁ x) 𝟘, by
--     intro a b hab
--     obtain ⟨c, _, _⟩ := le_iff_exists_add.mp hab
--     induction c with
--     | zero => apply wle_refl
--     | succ c ih =>
--       apply wle_trans (ih (Nat.le_add_right a c)); clear ih hab
--       rw [← add_assoc]
--       simp only [Nat.fold_succ]
--       set q := (a + c).fold (fun i _ x ↦ f' i ⨁ x) 𝟘
--       have := wAdd_mono q (wle_positive (f' (a + c)))
--       simpa [WeightedPreSemiring.wAdd_comm]⟩
open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring in
noncomputable def WeightedSum_chain [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]
    [e : Encodable ι] (f : ι → α) : WeightedChain α :=
  let f' i := if let some x := e.decode₂ _ i then f x else 𝟘
  ⟨fun n ↦ ⨁ᶠ i ∈ Finset.range n, f' i, by
    intro a b hab
    simp [WeightedFinsum]
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ c hac ih =>
      apply wle_trans ih; clear ih
      rw [Finset.range_succ]
      simp
      have h : 𝟘 ≼ f' c := by simp
      letI : Std.Commutative fun (a b : α) ↦ a ⨁ b := instCommutativeWAdd
      set x := Finset.fold (· ⨁ ·) (𝟘 : α) f' (Finset.range c)
      have := @wAdd_mono_right α _ _ x _ _ h
      simp at this
      exact this⟩

open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring in
/-- `⨁' x : ι, f x` is the encodable/countable sum over `f`.

`letI : Encodable ι := Encodable.ofCountable ι`
-/
noncomputable def WeightedSum [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]
    [e : Encodable ι] (f : ι → α) : α := wSup (WeightedSum_chain f)

@[inherit_doc WeightedSum]
notation3 "⨁' "(...)", "r:67:(scoped f => WeightedSum f) => r

variable [Encodable ι] [Nonempty ι] [WeightedOmegaContinuousPreSemiring α]

/-- info: fun f ↦ ⨁' (x : ι), f x : (ι → α) → α -/
#guard_msgs in
#check fun (f : ι → α) ↦ ⨁' x : ι, f x

end BigOperators

theorem WeightedSum_eq_wSup_Nat (f : ℕ → α) :
    ⨁' n : ℕ, f n = wSup ⟨fun n ↦ ⨁ᶠ i ∈ Finset.range n, f i, WeightedFinsup_range_mono⟩ := by
  simp only [WeightedSum, WeightedSum_chain, WeightedFinsum, Encodable.decode₂,
    Encodable.decode_nat, Encodable.encode_nat, Option.bind_some, decide_true, Option.guard_pos,
    Finset.fold_range]

theorem WeightedSum_empty [IsEmpty I] (f : I → α) : ⨁' x : I, f x = 𝟘 := by
  simp only [WeightedSum, WeightedSum_chain, imp_false, IsEmpty.forall_iff, wZero_add, wSup_eq_zero_iff, DFunLike.coe]
  intro i; induction i with
    simp only [Finset.range_zero, WeightedFinsup_empty, WeightedFinsup_range_succ, add_wZero, *]
@[simp]
theorem WeightedSum_eq_zero_iff {f : I → α} : ⨁' x, f x = 𝟘 ↔ ∀ x, f x = 𝟘 := by
  constructor
  · intro h a
    simp [WeightedSum, WeightedSum_chain, DFunLike.coe] at h
    replace h := h (e.encode a + 1)
    simp_all
  · intro hf
    simp [WeightedSum, WeightedSum_chain, hf, DFunLike.coe]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      simp only [WeightedFinsup_range_succ, wAdd_eq_zero_iff]
      split <;> simp_all

@[simp]
theorem WeightedSum_zero {T : Type} [Encodable T] : ⨁' _ : T, (𝟘 : α) = 𝟘 := by
  simp

omit e in
theorem WeightedFinsum_mul_left {α : Type} [WeightedPreSemiring α] [DecidableEq I]
    {s : α} (S : Finset I) (f : I → α) :
    ⨁ᶠ x ∈ S, s ⨀ f x = s ⨀ ⨁ᶠ x ∈ S, f x := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all [WeightedPreSemiring.left_distrib]
omit e in
theorem WeightedFinsum_mul_right {α : Type} [WeightedPreSemiring α] [DecidableEq I]
    {s : α} (S : Finset I) (f : I → α) :
    ⨁ᶠ x ∈ S, f x ⨀ s = (⨁ᶠ x ∈ S, f x) ⨀ s:= by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all [WeightedPreSemiring.right_distrib]

theorem WeightedSum_mul_left {s : α} (f : I → α) : ⨁' x : I, s ⨀ f x = s ⨀ ⨁' x : I, f x := by
  simp [WeightedSum]
  have := wMul_wSup s (WeightedSum_chain (f ·))
  dsimp at this
  rw [this]
  congr
  ext i
  simp [WeightedSum_chain, WeightedChain.map, DFunLike.coe]
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [WeightedFinsup_range_succ]
    rw [ih]; clear ih
    split <;> simp [WeightedPreSemiring.left_distrib]
-- TODO: can we reuse some of the above proof?
theorem WeightedSum_mul_right {s : α} (f : I → α) : ⨁' x : I, f x ⨀ s = (⨁' x : I, f x) ⨀ s := by
  simp [WeightedSum]
  have := wSup_wMul s (WeightedSum_chain (f ·))
  dsimp at this
  rw [this]
  congr
  ext i
  simp [WeightedSum_chain, WeightedChain.map, DFunLike.coe]
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [WeightedFinsup_range_succ]
    rw [ih]; clear ih
    split <;> simp [WeightedPreSemiring.right_distrib]

@[gcongr]
theorem wAdd_gconr {a b c d : α} (h₁ : a ≼ c) (h₂ : b ≼ d) : a ⨁ b ≼ c ⨁ d :=
  wle_trans (wAdd_mono_left a h₂) (wAdd_mono_right d h₁)
@[gcongr]
theorem wMul_gconr {a b c d : α} (h₁ : a ≼ c) (h₂ : b ≼ d) : a ⨀ b ≼ c ⨀ d :=
  wle_trans (wMul_mono_left a h₂) (wMul_mono_right d h₁)

attribute [simp] WeightedChain.val_apply

instance WeightedChain.instWeightedAdd : WeightedAdd (WeightedChain α) where
  wAdd C₁ C₂ := ⟨fun i ↦ C₁ i ⨁ C₂ i, fun hab ↦ wAdd_gconr (C₁.prop hab) (C₂.prop hab)⟩

theorem WeightedChain.wAdd_apply (C₁ C₂ : WeightedChain α) (i : ℕ) :
    (C₁ ⨁ C₂) i = C₁ i ⨁ C₂ i := rfl

theorem WeightedSum_chain_wAdd_apply {f₁ f₂ : I → α} (n : ℕ) :
    (WeightedSum_chain fun x ↦ f₁ x ⨁ f₂ x) n = WeightedSum_chain f₁ n ⨁ WeightedSum_chain f₂ n := by
  induction n with
  | zero => simp [WeightedSum_chain, DFunLike.coe]
  | succ n ih =>
    simp [WeightedSum_chain, DFunLike.coe]
    simp [← wAdd_assoc]
    nth_rw 3 [wAdd_comm]
    nth_rw 1 [← wAdd_assoc]
    nth_rw 1 [wAdd_assoc]
    congr
    · simp [WeightedSum_chain, DFunLike.coe] at ih
      rw [ih, wAdd_comm]
    · split <;> simp

theorem WeightedSum_chain_wAdd {f₁ f₂ : I → α} :
    (WeightedSum_chain fun x ↦ f₁ x ⨁ f₂ x) = WeightedSum_chain f₁ ⨁ WeightedSum_chain f₂ := by
  ext n; simp [WeightedSum_chain_wAdd_apply]; rfl

theorem WeightedSum_add {f₁ f₂ : I → α} :
    ⨁' x : I, (f₁ x ⨁ f₂ x) = (⨁' x : I, f₁ x) ⨁ (⨁' x : I, f₂ x) := by
  simp only [WeightedSum, dite_eq_ite]
  have := wAdd_wSup (wSup (WeightedSum_chain f₁)) (WeightedSum_chain f₂)
  dsimp at this
  rw [this]; clear this
  apply wle_antisymm
  · apply wSup_le
    intro n
    simp [WeightedSum_chain_wAdd_apply]
    apply le_wSup_of_le n
    simp [WeightedChain.map]
    have := wSup_wAdd (WeightedSum_chain f₂ n) (WeightedSum_chain f₁)
    simp at this
    simp only [DFunLike.coe]
    simp [this]; clear this
    apply le_wSup_of_le n
    simp [WeightedChain.map]
    simp only [DFunLike.coe]
    simp
  · apply wSup_le _ _ fun n ↦ ?_
    simp [WeightedChain.map]
    simp only [DFunLike.coe]
    simp
    have := wSup_wAdd (WeightedSum_chain f₂ n) (WeightedSum_chain f₁)
    dsimp at this
    rw [this]; clear this
    apply wSup_le _ _ fun n' ↦ ?_
    apply le_wSup_of_le (n ⊔ n')
    simp [WeightedChain.map]
    simp only [DFunLike.coe]
    simp [WeightedSum_chain_wAdd_apply]
    gcongr
    · apply (WeightedSum_chain f₁).prop; simp
    · apply (WeightedSum_chain f₂).prop; simp

theorem Nat.succ_fold {α : Type} (n : ℕ) (f : ℕ → α → α) (init : α) :
    (1 + n).fold (fun i _ ↦ f i) init = n.fold (fun i _ ↦ f (i + 1)) (f 0 init) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_comm] at ih ⊢
    simp
    simp at ih
    rw [ih]

theorem Nat.fold_add' {α : Type} (a b n : ℕ) (f : ℕ → α → α) (init : α) :
      (a + b).fold (fun i _ ↦ f (i + n)) init
    = a.fold (fun i _ ↦ f (i + b + n)) (b.fold (fun i _ ↦ f (i + n)) init) := by
  induction a generalizing init b n with
  | zero => rw [add_comm]; simp
  | succ a ih =>
    suffices (a + 1 + b).fold (fun i _ ↦ f (i + n)) = (1 + (a + b)).fold (fun i _ ↦ f (i + n)) by
      rw [this]; clear this
      rw [Nat.succ_fold]
      simp only [zero_add]
      replace ih := ih b (1 + n) (f n init)
      simp [← add_assoc] at ih
      rw [ih]; clear ih
      rw [add_comm]
      rw [Nat.succ_fold]
      simp only [zero_add]
      congr
      · ext; congr! 1; omega
      · induction b <;> simp
        congr
    ext; apply fold_congr; omega

theorem Nat.fold_add {α : Type} (a b : ℕ) (f : ℕ → α → α) (init : α) :
      (a + b).fold (fun i _ ↦ f i) init
    = a.fold (fun i _ ↦ f (i + b)) (b.fold (fun i _ ↦ f i) init) :=
  Nat.fold_add' a b 0 f init

@[simp]
theorem Nat.fold_id {α : Type} (n : ℕ) (init : α) : n.fold (fun _ _ x ↦ x) init = init := by
  induction n with simp only [fold_zero, fold_succ, *]

omit e in
omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_pair [DecidableEq I] {i₀ i₁ : I} (h : i₀ ≠ i₁) (f : I → α) :
    ⨁ᶠ i ∈ ({i₀, i₁} : Finset I), f i = f i₀ ⨁ f i₁ := by
  simp [WeightedFinsum]
  rw [Finset.fold_insert (by simp [h])]
  simp [@Finset.insert_eq]

syntax "magic_simp" ("[" term,* "]")? : tactic

macro_rules
| `(tactic|magic_simp) => `(tactic|magic_simp [])
| `(tactic|magic_simp [$t:term,*]) => `(tactic|
  simp only [DFunLike.coe, wle_refl, $[$t:term],*];
  try simp only [WeightedChain.map, WeightedChain.val_apply]; simp only [DFunLike.coe, wle_refl];)
syntax "weightedSemiring" ident : tactic

macro_rules
| `(tactic|weightedSemiring $t) => `(tactic|
    try (
      letI inst : Semiring $t := WeightedSemiring.toSemiring $t;
      have myAdd : ∀ (x y : $t), x ⨁ y = x + y := fun _ _ ↦ rfl;
      simp only [myAdd] at *; clear myAdd
    )
  )

  -- induction S using Finset.induction with
  -- | empty => simp
  -- | insert x S hxS ih =>
  --   simp [WeightedSum]
  --   sorry

-- theorem WeightedSum_finite (S : Set I) (hS : S.Finite) (f : I → α) :
--     have : Encodable S := Encodable.ofCountable ↑S
--     have : Fintype S := hS.fintype
--     ⨁' x : S, f x = ⨁ᶠ x ∈ S, f x := by
--   letI := hS.fintype
--   have := WeightedSum_finset S.toFinset f
--   simp at this
--   simp
--   rw [← this]
--   simp [WeightedSum]
--   congr! 1
--   ext i
--   simp [WeightedSum_chain, DFunLike.coe]
--   congr! 2
--   sorry
--   -- split <;> split
--   -- · congr! 1
--   -- · simp_all
--   -- · simp_all
--   -- · simp_all

-- omit e in
-- theorem WeightedSum_pair [DecidableEq I] {i₀ i₁ : I} (h : i₀ ≠ i₁) (f : I → α) :
--     letI : Encodable ↑({i₀, i₁} : Set I) := {
--       encode := fun i ↦ if i.val = i₀ then 0 else 1
--       decode := fun i ↦
--         if i = 0 then some ⟨i₀, by simp⟩ else if i = 1 then some ⟨i₁, by simp⟩ else none
--       encodek := by
--         intro ⟨i, hi⟩; split_ifs <;> try grind
--         simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
--         grind
--     }
--     ⨁' i : ({i₀, i₁} : Set I), f i = f i₀ ⨁ f i₁ := by
--   apply wle_antisymm (wSup_le _ _ fun n ↦ ?_)
--     (wle_trans (by simp [WeightedSum_chain, DFunLike.coe, wAdd_comm]) (le_wSup _ 2))
--   simp only [WeightedSum_chain]
--   simp [DFunLike.coe]
--   match n with
--   | 0 | 1 => simp [DFunLike.coe]
--   | n + 2 =>
--     have : Finset.range (n + 2) = {0, 1} ∪ (Finset.range n).image (· + 2) := by ext; simp_all; sorry
--     rw [this]
--     sorry

-- example {J : Type} [Encodable J] (I : J → Set ι) [∀ i, Encodable (I i)] (f : (j : J) → I j → α) :
--     have : Encodable ↑(⋃ j, I j) := sorry
--     ⨁' j : J, ⨁' i : I j, f j i = ⨁' i : ↑(⋃ j, I j), f (by sorry) (by sorry) := by
--   sorry

end
