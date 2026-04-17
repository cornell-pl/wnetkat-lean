module

public import Mathlib.Data.ENat.Lattice
public import WeightedNetKAT.Computation
public import WeightedNetKAT.Star

@[expose] public section

open OmegaCompletePartialOrder

instance : IsPositiveOrderedAddMonoid ℕ∞ where
  bot_eq_zero := rfl

instance : OmegaContinuousNonUnitalSemiring ℕ∞ where
  ωScottContinuous_add_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, ?_⟩
    intro c
    exact ENat.add_iSup ⇑c
  ωScottContinuous_add_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, ?_⟩
    intro c
    exact ENat.iSup_add ⇑c
  ωScottContinuous_mul_left := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, ?_⟩
    intro c
    exact ENat.mul_iSup x ⇑c
  ωScottContinuous_mul_right := by
    intro x
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, ?_⟩
    intro c
    exact ENat.iSup_mul (⇑c) x

instance : WeightedNetKAT.Star ℕ∞ where
  star | some 0 => 1 | _ => ⊤

instance : WeightedNetKAT.LawfulStar ℕ∞ where
  star_eq_sum n := by
    simp [WeightedNetKAT.Star.star]
    have h₀ : (some 0 : Option ℕ) = (0 : ℕ∞) := by rfl
    split
    · rw [ωSum_nat_eq_succ, h₀]
      simp
    · rename_i h
      simp [ωSum_nat_eq_ωSup, ωSup]
      refine (ENat.eq_top_iff_forall_ge.mpr fun m ↦ le_iSup_of_le m ?_).symm
      induction m with
      | zero => simp
      | succ m ih =>
        simp [Finset.sum_range_succ', pow_succ, ← Finset.sum_mul]
        apply le_trans (ENat.self_le_mul_right m h)
        gcongr
