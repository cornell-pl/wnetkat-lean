-- import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
-- import WeightedNetKAT.Star
-- import WeightedNetKAT.MatrixExt

-- open OmegaCompletePartialOrder

-- class ComputableSemiring (α : Type*) [Semiring α] [WeightedNetKAT.Star α] where
--   unique_star : ∀ X A B : α, A * X + B = X → X = A^* * B

-- open WeightedNetKAT

-- def ComputableSemiring.of_thing {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [WeightedNetKAT.StarIter α] [OmegaCompletePartialOrder α]
--     [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α] [LawfulStar α]
--     (h : ∀ a b c : α, a * b^* * c = ωSup ⟨fun n ↦ a * b^n * c, sorry⟩) : ComputableSemiring α where
--   unique_star X A B h' := by
--     have h'' := h (a:=X) (b:=A) (c:=B)
--     simp [LawfulStar.star_eq_sum, ← ωSum_mul_left, ← ωSum_mul_right] at h''
--     simp [ωSum_nat_eq_ωSup] at h''

--     have := h 1 A B
--     simp at this
--     rw [this]; clear this
--     -- rw [← StarIter.star_iter]
--     -- simp [right_distrib]
--     -- rw [h]
--     -- simp [add_ωSup]
--     apply le_antisymm
--     ·
--       sorry
--     · simp
--       intro i
--       induction i with
--       | zero => simp; rw [← h']; refine le_add_of_nonneg_left ?_; simp
--       | succ i ih =>
--         simp [pow_succ']
--         rw [← h']
--         grw [← ih]
--         simp [mul_assoc]
--         refine le_add_of_nonneg_right ?_
--         simp
