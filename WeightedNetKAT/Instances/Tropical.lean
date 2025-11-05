import WeightedNetKAT.Star
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Tropical.Lattice
import Mathlib.Algebra.Tropical.BigOperators

open Tropical

@[simp]
instance : WeightedNetKAT.Star (Tropical (OrderDual ℕ∞)) where
  star x := if x ≥ trop 0 then trop 0 else trop ⊤


-- instance : LinearOrderedAddCommMonoidWithTop ℕ∞ᵒᵈ where
--   -- add_le_add_left := by
--   --   simp
--   --   intro a b hab c x y
--   top_add' x := by
--     refine OrderDual.ofDual_inj.mp ?_
--     simp
--     -- rw [Tropical.add_eq_iff (R:=ℕ∞ᵒᵈ) (x:=⊤) (y:=x)]
--     sorry
--     -- refine OrderDual.ofDual_inj.mp ?_
--     -- simp
--     -- refine ENat.lt_one_iff_eq_zero.mp ?_
--     -- apply?

instance : Semiring (Tropical (OrderDual ℕ∞)) where
  zero_mul a := by
    rw [trop_mul_def]
    refine trop_eq_iff_eq_untrop.mpr ?_
    simp
    refine OrderDual.ofDual_inj.mp ?_
    simp
    refine ENat.lt_one_iff_eq_zero.mp ?_
    simp
  mul_zero a := by simp

instance : WeightedNetKAT.LawfulStar (Tropical (OrderDual ℕ∞)) where
  star_eq_sum x := by
    simp; split_ifs with h
    · subst_eqs
      rw [ωSum_nat_eq_succ]
      simp
      apply le_top
    · apply le_antisymm
      · simp_all
        simp [ωSum_nat_eq_ωSup]
        sorry
      · apply le_top

instance : Repr Arctic where
  reprPrec a _ :=
    match a with
    | none => "-∞"
    | some n => reprStr (OrderDual.toDual.symm n)
