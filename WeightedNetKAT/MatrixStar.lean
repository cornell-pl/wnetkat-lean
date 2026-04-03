import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import WeightedNetKAT.Star
import WeightedNetKAT.MatrixExt

namespace Matrix.Star

open WeightedNetKAT

section

variable {α : Type*} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

scoped notation "𝟙" => Unit

instance : WeightedNetKAT.Star (Matrix 𝟙 𝟙 α) where
  star m := (m () ())^*
instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [LawfulStar α] :
    LawfulStar (Matrix 𝟙 𝟙 α) where
  star_eq_sum m := by
    have := LawfulStar.star_eq_sum (m () ())
    ext ⟨⟩ ⟨⟩
    simp_all
    convert this; clear this
    rename_i n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Matrix.mul_apply, ih]

def nice {n : ℕ} (m : Matrix (Fin (n + 1)) (Fin (n + 1)) α) : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α
  | .inl l,  .inl r  => m ⟨l, by omega⟩ ⟨r, by omega⟩
  | .inl l,  .inr () => m ⟨l, by omega⟩ ⟨n, by omega⟩
  | .inr (), .inl r  => m ⟨n, by omega⟩ ⟨r, by omega⟩
  | .inr (), .inr () => m ⟨n, by omega⟩ ⟨n, by omega⟩

end

section

variable {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance instStar :
    WeightedNetKAT.Star (Matrix n n α) where
  star m := ω∑ i : ℕ, m^i

noncomputable instance instLawfulStar :
    WeightedNetKAT.LawfulStar (Matrix n n α) where
  star_eq_sum _ := rfl

end
