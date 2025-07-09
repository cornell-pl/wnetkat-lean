import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Lattice
import WeightedNetKAT.WNKA
import Mathlib.Computability.Language

open OmegaCompletePartialOrder

variable {α : Type}

instance : IsPositiveOrderedAddMonoid (Language α) where
  bot_eq_zero := rfl

instance : OmegaContinuousNonUnitalSemiring (Language α) where
  ωSup_add_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, ?_⟩
    intro c
    exact Language.add_iSup (⇑c) x
  ωSup_add_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, ?_⟩
    intro c
    exact Language.iSup_add (⇑c) x
  ωSup_mul_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, ?_⟩
    intro c
    exact Language.mul_iSup (⇑c) x
  ωSup_mul_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, ?_⟩
    intro c
    exact Language.iSup_mul (⇑c) x

instance : WeightedNetKAT.Star (Language α) where
  star m := KStar.kstar m

open scoped Classical in
instance : WeightedNetKAT.LawfulStar (Language α) where
  star_eq_sum := by sorry
