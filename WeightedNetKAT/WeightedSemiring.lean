module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import WeightedNetKAT.KStar

open OmegaCompletePartialOrder

/-!

# Weighted semirings

We introduces weighted versions of nessesaray semiring and order instances with custom notation that
mirror the Mathlib definitions almost one-to-one.

The reason for this is to simplify the instantiation of weighted version of already existing
structures. One such example is the Tropical semiring which works over `ENat`. `ENat` already has
instances for (almost) everything we need, however, the existing definitons are `(ENat, 0, 1, +, *,
≤)` while we need `(ENat, ⊤, 0, min, +, ≥)`. One could create new instances for these that shadow
the previous, but suddenly one has to proof goals that look like `0 + 1 ≤ 1` where `0` can be either
`0` or `⊤` and the ones can be `1` or `0` independently and `≤` can be either `≤` or `≥`.

To simplify these, the new notation makes it very clear for the reader to see which is which, and
equally as important, makes it easier to `simp` away the weighted notation and get to the meat of
the proof.

Previous versions tried the prior approach; for some instances it took hundreds of lines and much
turmoil, and some we deemed too complicated just because of the sheer confusion when mixing
semirings.

Instances with this new approach are significantly shorter and lends themselves much more to
automation.

-/

@[expose] public section

/-- Weighted variant of [`Add`] -/
class WAdd (α : Type*) where
  wadd : α → α → α
/-- Weighted variant of [`Mul`] -/
class WMul (α : Type*) where
  wmul : α → α → α
/-- Weighted variant of [`KStar`] -/
class WKStar (α : Type*) where
  /-- Weighted variant of [`KStar`] -/
  wkstar : α → α

/-- Weighted variant of [`Zero`] -/
class WZero (α : Type*) where
  wzero : α
/-- Weighted variant of [`One`] -/
class WOne (α : Type*) where
  wone : α

/-- Weighted variant of [`LE`] -/
class WLE (α : Type*) where
  wle : α → α → Prop
/-- Weighted variant of [`LT`] -/
class WLT (α : Type*) where
  wlt : α → α → Prop

export WAdd (wadd)
export WMul (wmul)
export WKStar (wkstar)
export WZero (wzero)
export WOne (wone)
export WLE (wle)
export WLT (wlt)

@[inherit_doc] scoped[WKStar] postfix:1024 "⍟" => WKStar.wkstar

notation "𝟘" => wzero
notation "𝟙" => wone
infixl:68 " ⨁ " => wadd
infixl:70 " ⨀ " => wmul
infixl:50 " ≼ " => wle
infixl:50 " ≺ " => wlt

abbrev WKStar.toKStar (α : Type*) [WKStar α] : KStar α := ⟨wkstar⟩

/-- Weighted variant of [`Semiring`] -/
class WSemiring (α : Type*) extends WAdd α, WMul α, WOne α, WZero α where
  wadd_wzero (a : α) : a ⨁ 𝟘 = a := by simp [wzero]
  wadd_assoc (a b c : α) : a ⨁ b ⨁ c = a ⨁ (b ⨁ c) := by simp [Std.Associative.assoc]
  wzero_wadd (a : α) : 𝟘 ⨁ a = a := by simp [wzero]
  wnsmul : ℕ → α → α
  wadd_comm (a b : α) : a ⨁ b = b ⨁ a := by simp [Std.Commutative.comm]
  left_distrib (a b c : α) : a ⨀ (b ⨁ c) = a ⨀ b ⨁ a ⨀ c := by simp [LeftDistribClass.left_distrib]
  right_distrib (a b c : α) : (a ⨁ b) ⨀ c = a ⨀ c ⨁ b ⨀ c := by simp [RightDistribClass.right_distrib]
  wzero_wmul (a : α) : 𝟘 ⨀ a = 𝟘 := by simp
  wmul_wzero (a : α) : a ⨀ 𝟘 = 𝟘 := by simp
  wmul_assoc (a b c : α) : a ⨀ b ⨀ c = a ⨀ (b ⨀ c) := by simp [Std.Associative.assoc]
  wone_wmul (a : α) : 𝟙 ⨀ a = a := by simp
  wmul_wone (a : α) : a ⨀ 𝟙 = a := by simp
  wnsmul_zero (x : α) : wnsmul 0 x = 𝟘 := by simp
  wnsmul_succ (n : ℕ) (x : α) : wnsmul (n + 1) x = wnsmul n x ⨁ x := by simp [AddMonoid.nsmul_succ, add_mul]

/-- Weighted variant of [`PartialOrder`] -/
class WPartialOrder (α : Type*) extends WLE α, WLT α where
  wle_refl (a : α) : a ≼ a := by intro; simp
  wle_trans {a b c : α} : a ≼ b → b ≼ c → a ≼ c
  wlt_iff_wle_not_wge (a b : α) : a ≺ b ↔ a ≼ b ∧ ¬b ≼ a := by intro _ _; rfl
  wle_antisymm (a b : α) (hab : a ≼ b) (hba : b ≼ a) : a = b

abbrev WSemiring.toSemiring (α : Type*) [WSemiring α] : Semiring α where
  add := wadd
  zero := wzero
  add_assoc := wadd_assoc
  zero_add := wzero_wadd
  add_zero := wadd_wzero
  nsmul := wnsmul
  add_comm := wadd_comm
  mul := wmul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := wzero_wmul
  mul_zero := wmul_wzero
  mul_assoc := wmul_assoc
  one := wone
  one_mul := wone_wmul
  mul_one := wmul_wone
  nsmul_zero := wnsmul_zero
  nsmul_succ := wnsmul_succ

abbrev WLE.toLE (α : Type*) [WLE α] : LE α := ⟨wle⟩
abbrev WLT.toLT (α : Type*) [WLT α] : LT α := ⟨wlt⟩

abbrev WPartialOrder.toPartialOrder (α : Type*) [WPartialOrder α] : PartialOrder α :=
  { WLE.toLE α, WLT.toLT α with
    le_refl := wle_refl
    le_trans _ _ _ := wle_trans
    lt_iff_le_not_ge a b := wlt_iff_wle_not_wge a b
    le_antisymm := wle_antisymm
  }

instance {α : Type*} [WLE α] : WLT α where
  wlt a b := a ≼ b ∧ ¬b ≼ a

class WOmegaCompletePartialOrder (α : Type*) extends WPartialOrder α where
  wωSup (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) : α
  wle_wωSup (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) (i : ℕ) : f i ≼ wωSup f h
  wωSup_wle (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) (x : α) : (∀ (i : ℕ), f i ≼ x) → wωSup f h ≼ x

theorem WOmegaCompletePartialOrder.wωSup_wle_of_wle {α : Type*} [WOmegaCompletePartialOrder α] {f : ℕ → α} {h : ∀ {a b}, a ≤ b → f a ≼ f b} {x : α} (i : ℕ) (hi : x ≼ f i) :
    x ≼ wωSup f h :=
  WPartialOrder.wle_trans hi (wle_wωSup f h i)

section

local instance {α : Type*} [WLE α] : LE α := WLE.toLE α
local instance {α : Type*} [WLT α] : LT α := WLT.toLT α
local instance {α : Type*} [WPartialOrder α] : PartialOrder α := WPartialOrder.toPartialOrder α

abbrev WOmegaCompletePartialOrder.toOmegaCompletePartialOrder (α : Type*) [WOmegaCompletePartialOrder α] : OmegaCompletePartialOrder α :=
  { WPartialOrder.toPartialOrder α with
    le_antisymm := WPartialOrder.wle_antisymm
    ωSup c := wωSup c (c.monotone ·)
    le_ωSup c := wle_wωSup c (c.monotone ·)
    ωSup_le c := wωSup_wle c (c.monotone ·)
  }

class WOmegaContinuousNonUnitalSemiring (α : Type*) extends WSemiring α, WOmegaCompletePartialOrder α where
  -- OrderBot
  wbot : α := 𝟘
  wbot_wle (a : α) : wbot ≼ a := by intro; simp
  -- IsPositiveOrderedAddMonoid
  wbot_eq_wzero : (wbot : α) = 𝟘 := by rfl
  -- AddLeftMono
  wadd_left_mono {b c : α} (h : b ≼ c) (a : α) : a ⨁ b ≼ a ⨁ c
  -- AddRightMono
  wadd_right_mono {b c : α} (h : b ≼ c) (a : α) : b ⨁ a ≼ c ⨁ a
  -- MulLeftMono
  wmul_left_mono {b c : α} (h : b ≼ c) (a : α) : a ⨀ b ≼ a ⨀ c
  -- MulRightMono
  wmul_right_mono {b c : α} (h : b ≼ c) (a : α) : b ⨀ a ≼ c ⨀ a
  -- OmegaContinuousNonUnitalSemiring
  wωScottContinuous_wadd_right (a : α) (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) :
    wωSup f h ⨁ a = wωSup (fun x ↦ f x ⨁ a) (fun h' ↦ wadd_right_mono (h h') _)
  wωScottContinuous_wadd_left (a : α) (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) :
    a ⨁ wωSup f h = wωSup (fun x ↦ a ⨁ f x) (fun h' ↦ wadd_left_mono (h h') a)
  wωScottContinuous_wmul_right (a : α) (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) :
    wωSup f h ⨀ a = wωSup (fun x ↦ f x ⨀ a) (fun h' ↦ wmul_right_mono (h h') a)
  wωScottContinuous_wmul_left (a : α) (f : ℕ → α) (h : ∀ {a b}, a ≤ b → f a ≼ f b) :
    a ⨀ wωSup f h = wωSup (fun x ↦ a ⨀ f x) (fun h' ↦ wmul_left_mono (h h') a)

local instance {α : Type*} [WSemiring α] : Semiring α := WSemiring.toSemiring α
local instance {α : Type*} [WOmegaCompletePartialOrder α] : OmegaCompletePartialOrder α := WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α

namespace WOmegaContinuousNonUnitalSemiring

variable (α : Type*) [WOmegaContinuousNonUnitalSemiring α]

abbrev toOrderBot : OrderBot α := {
  WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α with
  bot := wbot
  bot_le := wbot_wle
}

abbrev toMulLeftMono : MulLeftMono α := {
  WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α with
  elim _ _ _ h := wmul_left_mono h _
}

abbrev toMulRightMono : MulRightMono α := {
  WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α with
  elim _ _ _ h := wmul_right_mono h _
}

local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] : OrderBot α := WOmegaContinuousNonUnitalSemiring.toOrderBot α

abbrev toIsPositiveOrderedAddMonoid : IsPositiveOrderedAddMonoid α := {
  WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α with
  add_le_add_left _ _ h _ := wadd_right_mono h _
  bot_eq_zero := wbot_eq_wzero
}

end WOmegaContinuousNonUnitalSemiring

open scoped KStar

local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] : OrderBot α := WOmegaContinuousNonUnitalSemiring.toOrderBot α
local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] : MulLeftMono α := WOmegaContinuousNonUnitalSemiring.toMulLeftMono α
local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] : MulRightMono α := WOmegaContinuousNonUnitalSemiring.toMulRightMono α
local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] : IsPositiveOrderedAddMonoid α := WOmegaContinuousNonUnitalSemiring.toIsPositiveOrderedAddMonoid α

abbrev WOmegaContinuousNonUnitalSemiring.toOmegaContinuousNonUnitalSemiring (α : Type*) [WOmegaContinuousNonUnitalSemiring α] :
    OmegaContinuousNonUnitalSemiring α :=
  { WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α with
    ωScottContinuous_add_right a := by
      refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
      use (fun _ _ h ↦ wadd_right_mono h _), fun c ↦ wωScottContinuous_wadd_right a c (c.monotone ·)
    ωScottContinuous_add_left a := by
      refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
      use (fun _ _ h ↦ wadd_left_mono h _), fun c ↦ wωScottContinuous_wadd_left a c (c.monotone ·)
    ωScottContinuous_mul_right a := by
      refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
      use (fun _ _ h ↦ wmul_right_mono h _), fun c ↦ wωScottContinuous_wmul_right a c (c.monotone ·)
    ωScottContinuous_mul_left a := by
      refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
      use (fun _ _ h ↦ wmul_left_mono h _), fun c ↦ wωScottContinuous_wmul_left a c (c.monotone ·)
  }

def wstarn {α : Type*} [WSemiring α] (a : α) : ℕ → α
  | 0 => 𝟘
  | n + 1 => 𝟙 ⨁ a ⨀ wstarn a n

section

variable {α : Type*} [WOmegaContinuousNonUnitalSemiring α] {a b c d : α} {n m : ℕ}

open WSemiring
open WPartialOrder
open WOmegaContinuousNonUnitalSemiring

attribute [refl, simp] WPartialOrder.wle_refl
attribute [gcongr] wadd_left_mono
attribute [gcongr] wadd_right_mono
attribute [simp] wadd_wzero
attribute [simp] wzero_wadd
attribute [simp] wmul_wone
attribute [simp] wone_wmul
attribute [simp] wmul_wzero
attribute [simp] wzero_wmul


@[simp]
theorem wzero_le : 𝟘 ≼ a := by rw [← wbot_eq_wzero]; apply wbot_wle

@[gcongr]
theorem wadd_le_wadd (hac : a ≼ c) (hbd : b ≼ d) : a ⨁ b ≼ c ⨁ d := by
  apply wle_trans (wadd_left_mono hbd _)
  apply wle_trans (wadd_right_mono hac _)
  rfl

@[gcongr]
theorem wmul_le_wmul (hac : a ≼ c) (hbd : b ≼ d) : a ⨀ b ≼ c ⨀ d := by
  apply wle_trans (wmul_left_mono hbd _)
  apply wle_trans (wmul_right_mono hac _)
  rfl

@[simp] theorem wstarn_zero : wstarn a 0 = 𝟘 := rfl

@[gcongr]
theorem wstarn_mono_left (h : a ≼ b) : wstarn a n ≼ wstarn b n := by
  induction n with
  | zero => simp [WPartialOrder.wle_refl]
  | succ n ih =>
    simp [wstarn]
    gcongr

theorem wstarn_le_succ : wstarn a n ≼ wstarn a (n + 1) := by
  induction n with
  | zero =>
    simp [wstarn]
  | succ n ih =>
    simp only [wstarn, WSemiring.left_distrib, wmul_wone, ← wmul_assoc] at ih ⊢
    gcongr
    apply wle_trans (wmul_left_mono ih _)
    simp only [WSemiring.left_distrib, wmul_wone, ← wmul_assoc, wle_refl]

@[gcongr]
theorem wstarn_mono_right (h : n ≤ m) : wstarn a n ≼ wstarn a m := by
  fun_induction wstarn a m
  · simp_all
  · grind [wle_trans, WPartialOrder.wle_antisymm, wstarn.eq_def, wadd_le_wadd, wstarn_mono_left,
      wle_refl, wzero_le, wmul_left_mono, wstarn_le_succ]

theorem wstarn_mono : Monotone (wstarn a) := by apply wstarn_mono_right

open WOmegaCompletePartialOrder

@[simp]
theorem wstarn_wzero_left {i} : (wstarn 𝟘 i : α) = if i = 0 then 𝟘 else 𝟙 := by
  induction i with
  | zero => simp
  | succ i ih => simp [wstarn]

@[simp]
theorem wωSup_wstarn_wzero_left : (wωSup (wstarn 𝟘 ·) wstarn_mono_right : α) = 𝟙 := by
  apply le_antisymm
  · apply wωSup_wle
    intro i
    induction i with
    | zero => simp
    | succ i ih => simp [wstarn, wzero_wmul]
  · apply wωSup_wle_of_wle 1; simp [wstarn]

end

class LawfulWKStar (α : Type*) [WKStar α] [WOmegaContinuousNonUnitalSemiring α] where
  wkstar_eq_sum (m : α) :
    wkstar m = WOmegaCompletePartialOrder.wωSup (fun n ↦ wstarn m n) (by intro i j h; simp; apply wstarn_mono_right h)

section

local instance {α : Type*} [WSemiring α] : Semiring α := WSemiring.toSemiring α
local instance {α : Type*} [WKStar α] : KStar α := WKStar.toKStar α

abbrev LawfulWKStar.toLawfulKStar (α : Type*) [WOmegaContinuousNonUnitalSemiring α] [WKStar α] [LawfulWKStar α] : LawfulKStar α where
  kstar_eq_sum m := by
    have {a : α} {n : ℕ} : wstarn a n = ∑ i ∈ Finset.range n, a^i := by
      induction n with
      | zero => simp [wstarn]; rfl
      | succ n ih =>
        simp [wstarn, Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
        rw [add_comm]
        congr
    simp [this, KStar.kstar, wkstar_eq_sum, ωSum_nat_eq_ωSup]
    rfl

open WOmegaContinuousNonUnitalSemiring

local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] [WKStar α] [LawfulWKStar α] :
    LawfulKStar α := LawfulWKStar.toLawfulKStar α
local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] [WKStar α] [LawfulWKStar α] :
    OmegaCompletePartialOrder α := WOmegaCompletePartialOrder.toOmegaCompletePartialOrder α
local instance {α : Type*} [WOmegaContinuousNonUnitalSemiring α] [WKStar α] [LawfulWKStar α] :
    OmegaContinuousNonUnitalSemiring α := toOmegaContinuousNonUnitalSemiring α

abbrev LawfulWKStar.toKStarIter (α : Type*)
    [WOmegaContinuousNonUnitalSemiring α] [WKStar α] [LawfulWKStar α] : KStarIter α where
  kstar_iter m := by
    simp [LawfulKStar.kstar_eq_sum]
    nth_rw 2 [ωSum_nat_eq_succ]
    simp [pow_succ', ωSum_mul_left]

end

end

end

attribute [simp] wzero
attribute [simp] wadd
attribute [simp] wmul
attribute [simp] wle
