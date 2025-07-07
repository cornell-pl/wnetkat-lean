import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Lattice
import WeightedNetKAT.WNKA

open OmegaCompletePartialOrder

instance : IsPositiveOrderedAddMonoid ℕ∞ where
  bot_eq_zero := rfl

instance : OmegaContinuousNonUnitalSemiring ℕ∞ where
  ωSup_add_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, ?_⟩
    intro c
    exact ENat.add_iSup ⇑c
  ωSup_add_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, ?_⟩
    intro c
    exact ENat.iSup_add ⇑c
  ωSup_mul_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, ?_⟩
    intro c
    exact ENat.mul_iSup x ⇑c
  ωSup_mul_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, ?_⟩
    intro c
    exact ENat.iSup_mul (⇑c) x

instance : WeightedNetKAT.FinsuppStar ℕ∞ where
  wStar {X _ _} m := m

instance : WeightedNetKAT.LawfulFinsuppStar ℕ∞ where
  wStar_eq_sum := sorry
