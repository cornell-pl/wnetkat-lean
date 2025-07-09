import Mathlib.Computability.RegularExpressions
import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Lattice
import WeightedNetKAT.WNKA

open OmegaCompletePartialOrder

variable {α : Type}

instance : AddCommMonoid (RegularExpression α) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  add_comm := sorry
  nsmul_succ := sorry
  nsmul_zero := sorry

instance : PartialOrder (RegularExpression α) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : OrderBot (RegularExpression α) where
  bot := 0
  bot_le := sorry

instance : IsPositiveOrderedAddMonoid (RegularExpression α) where
  bot_eq_zero := rfl
  add_le_add_left := sorry

instance : Semiring (RegularExpression α) where
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : OmegaCompletePartialOrder (RegularExpression α) where
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le := sorry

instance : MulLeftMono (RegularExpression α) where
  elim := sorry
instance : MulRightMono (RegularExpression α) where
  elim := sorry

instance : OmegaContinuousNonUnitalSemiring (RegularExpression α) where
  ωSup_add_left := by
    sorry
    -- intro x
    -- refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, ?_⟩
    -- intro c
    -- exact ENat.add_iSup ⇑c
  ωSup_add_right := by
    sorry
    -- intro x
    -- refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, ?_⟩
    -- intro c
    -- exact ENat.iSup_add ⇑c
  ωSup_mul_left := by
    sorry
    -- intro x
    -- refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, ?_⟩
    -- intro c
    -- exact ENat.mul_iSup x ⇑c
  ωSup_mul_right := by
    sorry
    -- intro x
    -- refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, ?_⟩
    -- intro c
    -- exact ENat.iSup_mul (⇑c) x

instance : WeightedNetKAT.Star (RegularExpression α) where
  star m := m.star

instance : WeightedNetKAT.LawfulStar (RegularExpression α) where
  star_eq_sum n := by
    simp [WeightedNetKAT.Star.star]
    sorry

open RegularExpression

def RegularExpression.isEq {α : Type} [DecidableEq α] (r r' : RegularExpression α) : Bool :=
  match r, r' with
  | zero, zero => true
  | epsilon, epsilon => true
  | char a, char a' => a = a'
  | plus a b, plus a' b' => a.isEq a' ∧ b.isEq b'
  | comp a b, comp a' b' => a.isEq a' ∧ b.isEq b'
  | star a, star a' => a.isEq a'
  | _, _ => false

instance {α : Type} [DecidableEq α] : DecidableEq (RegularExpression α) := fun a b ↦
  if h : a.isEq b then
    .isTrue (by fun_induction RegularExpression.isEq <;> grind)
  else
    .isFalse (by fun_induction RegularExpression.isEq <;> simp_all <;> sorry)

partial def RegularExpression.simp {α : Type} [DecidableEq α] [Repr α] (r : RegularExpression α) : RegularExpression α :=
  match r with
  | zero => zero
  | epsilon => epsilon
  | char a => char a
  | plus a b =>
    match a.simp, b.simp with
    | zero, b => b
    | a, zero => a
    | a, b => if a = b then a else plus a b
  | comp a b =>
    match a.simp, b.simp with
    | epsilon, b => b
    | a, epsilon => a
    | zero, _ => zero
    | _, zero => zero
    | a, b => comp a b
  | star a =>
    match a.simp with
    | zero | epsilon => epsilon
    | a => star a.simp

def RegularExpression.repr {α : Type} [Repr α] (r : RegularExpression α) : String :=
  match r with
  | zero => "0"
  | epsilon => "ε"
  | char a => reprStr a
  | plus a b => s!"({a.repr}+{b.repr})"
  | comp a b => s!"({a.repr};{b.repr})"
  | star a => s!"({a.repr})*"

instance {α : Type} [DecidableEq α] [Repr α] : Repr (RegularExpression α) where
  reprPrec n _ := n.simp.repr
