module

public import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
public import WeightedNetKAT.KStar
public import WeightedNetKAT.MatrixExt

@[expose] public section

namespace Matrix.KStar

open KStar
open scoped Computability

open scoped MatrixNotation

section

variable {α : Type*} [AddCommMonoid α] [Mul α] [KStar α]

scoped notation "𝟙" => Unit

instance : KStar 𝕄[𝟙,𝟙,α] where
  kstar m := (m () ())∗
instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [KStar α] [LawfulKStar α] :
    LawfulKStar 𝕄[𝟙,𝟙,α] where
  kstar_eq_sum m := by
    have := LawfulKStar.kstar_eq_sum (m () ())
    ext ⟨⟩ ⟨⟩
    simp_all
    convert this; clear this
    rename_i n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Matrix.mul_apply, ih]

end

section

variable {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance instKStar :
    KStar 𝕄[n,n,α] where
  kstar m := ω∑ i : ℕ, m^i

noncomputable instance instLawfulKStar :
    LawfulKStar 𝕄[n,n,α] where
  kstar_eq_sum _ := rfl

end
