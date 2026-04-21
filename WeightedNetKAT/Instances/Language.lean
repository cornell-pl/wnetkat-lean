module

public import Mathlib.Computability.Language
public import Mathlib.Data.ENat.Lattice
public import WeightedNetKAT.Computation
public import WeightedNetKAT.KStar

@[expose] public section

open OmegaCompletePartialOrder

variable {α : Type}

instance : IsPositiveOrderedAddMonoid (Language α) where
  bot_eq_zero := rfl

instance : OmegaContinuousNonUnitalSemiring (Language α) where
  ωScottContinuous_add_left x :=
    ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, (Language.add_iSup · x)⟩
  ωScottContinuous_add_right x :=
    ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, (Language.iSup_add · x)⟩
  ωScottContinuous_mul_left x :=
    ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, (Language.mul_iSup · x)⟩
  ωScottContinuous_mul_right x :=
    ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, (Language.iSup_mul · x)⟩

open scoped Classical in
instance : LawfulKStar (Language α) where
  kstar_eq_sum m := by
    apply le_antisymm
    · refine kstar_le_of_mul_le_left ?_ ?_
      · rw [ωSum_nat_eq_succ]; simp only [pow_zero, self_le_add_right]
      · nth_rw 2 [ωSum_nat_eq_succ]; simp [pow_succ, ωSum_mul_right]
    · refine ωSum_le_of_finset fun S ↦ ?_
      induction S using Finset.induction with
      | empty => simp
      | insert x S hx ih => simp_all [add_le]
