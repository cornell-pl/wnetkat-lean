import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import WeightedNetKAT.Listed
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.OmegaContinuousNonUnitalSemiring

namespace WeightedNetKAT

/-- `Star` introduces notation `m^*` which is supposed to satisfy `m^* = ω∑ n : ℕ, m^n`. Note that
  this is not imposed by the `Star` type class but rather `LawfulStar` since it requires
  `OmegaCompletePartialOrder` which is in general non-computable.
-/
class Star (α : Type) where
  star : α → α
postfix:max "^*" => WeightedNetKAT.Star.star
class LawfulStar (α : Type)
    [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] where
  star_eq_sum : ∀ m : α, m^* = ω∑ n : ℕ, m^n

instance instUnitStar {α : Type} [Star α] : Star (Matrix Unit Unit α) where
  star m := fun α β ↦ (m α β)^*
-- instance : LawfulStar (Matrix Unit Unit 𝒮) where
--   star_eq_sum := sorry

variable {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [LawfulStar α]
variable [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]

open OmegaCompletePartialOrder

theorem ωSup_pow {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α]
    (f : ℕ → α) (hf : Monotone f) (i : ℕ) :
      ωSup ⟨fun n ↦ (f n)^i, fun a b hab ↦ by simp; gcongr; exact hf hab⟩
    = ωSup ⟨fun n ↦ f n, hf⟩ ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [pow_succ]
    rw [← ih]
    simp [ωSup_mul_ωSup]

theorem star_iter {a : α} :
    1 + a * a^* = a^* := by
  simp [LawfulStar.star_eq_sum]
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [pow_succ', ωSum_mul_left]
theorem star_iter' {a : α} :
    1 + a^* * a = a^* := by
  simp [LawfulStar.star_eq_sum]
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [pow_succ, ωSum_mul_right]
theorem add_star {a b : α} :
    (a + b)^* = (a^* * b)^* * a^* := by
  simp [LawfulStar.star_eq_sum]
  simp [← ωSum_mul_left, ← ωSum_mul_right]
  simp [ωSum_nat_eq_ωSup, sum_ωSup', ← ωSup_pow, ωSup_mul, sum_ωSup', sum_ωSup']
  rw [ωSup_ωSup_eq_ωSup', ωSup_ωSup_eq_ωSup']
  · apply le_antisymm
    · simp
      intro n
      apply le_ωSup_of_le n
      · simp
        gcongr with j hj
        induction n generalizing j with
        | zero => simp_all
        | succ n ih =>
          rcases j with _ | j
          · simp_all [Finset.sum_range_succ']
            sorry
          · simp_all
            simp [pow_succ, ← mul_assoc]
            specialize ih j hj
            apply le_trans (mul_right_mono (a:=a + b) ih)
            simp only
            simp [Finset.sum_range_succ', Finset.sum_mul]
            have : ∀ x y z : α, x ≤ y → x ≤ y + z := sorry
            apply this
            apply Finset.sum_le_sum
            intro i hi
            simp [Finset.sum_range_succ', Finset.sum_add_distrib, pow_succ]
            simp [mul_add, add_mul]
            sorry
      · sorry
    · simp
      intro n
      apply le_ωSup_of_le n
      simp
      sorry
  · intro i j hij n
    simp
    obtain ⟨m, _, _⟩ : ∃ m, i + m = j := by exact Nat.le.dest hij
    simp [Finset.sum_range_add, Finset.sum_add_distrib, add_assoc]
    have : ∀ x y z : α, x ≤ y → x ≤ y + z := by intro x y z h; rw [← add_zero x]; gcongr; simp
    sorry
    -- apply this
    -- rfl
  -- · intro a b hab j
  --   simp
  --   intro n
  --   apply le_ωSup_of_le n
  --   simp [DFunLike.coe]
  --   gcongr
  --   simp


  -- apply le_antisymm
  -- · simp [DFunLike.coe]
  --   intro i
  --   apply le_ωSup_of_le i
  --   apply le_ωSup_of_le i
  --   apply le_ωSup_of_le i
  --   simp [DFunLike.coe]
  --   induction i with
  --   | zero => simp
  --   | succ i ih =>
  --     simp [Finset.sum_range_succ]

  -- · simp [DFunLike.coe]
  --   intro i₀ i₁ i₂
  --   apply le_ωSup_of_le (i₀ + i₁ + i₂)
  --   simp [DFunLike.coe]
  --   -- simp [Finset.sum_mul]
  --   rw [add_assoc, Finset.sum_range_add]
  --   sorry

  -- -- · intro a b hab j
  -- --   simp
  -- --   apply Finset.sum_mono_set_of_nonneg
  -- --   · simp
  -- --   · simp [hab]
theorem mul_star {a b : α} :
    (a * b)^* = 1 + a * (b * a)^* * b := by
  simp only [LawfulStar.star_eq_sum, ← ωSum_mul_left, ← ωSum_mul_right]
  nth_rw 1 [ωSum_nat_eq_succ]
  simp only [pow_zero]
  congr with n
  induction n with
  | zero => grind [mul_one]
  | succ n ih => rw [pow_succ]; grind [mul_assoc]

end WeightedNetKAT

def Matrix.listedEquivNat {α A : Type} [DecidableEq A] [i : Listed A] :
    Matrix A A α ≃ Matrix (Fin i.size) (Fin i.size) α :=
  ⟨fun m ↦ m.submatrix Listed.decodeFin Listed.decodeFin,
   fun m ↦ m.submatrix Listed.encodeFin Listed.encodeFin,
   by intro m; ext i j; simp,
   by intro m; ext i j; simp⟩

namespace Matrix.Star

open WeightedNetKAT

variable {α : Type} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

scoped notation "𝟙" => Unit

instance : WeightedNetKAT.Star (Matrix 𝟙 𝟙 α) where
  star m := (m () ())^*
instance {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [LawfulStar α] :
    WeightedNetKAT.LawfulStar (Matrix 𝟙 𝟙 α) where
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

def conice {n : ℕ} (m : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α) : Matrix (Fin (n + 1)) (Fin (n + 1)) α
  | l,  r  =>
    let l' := if hl : l = n then .inr () else .inl ⟨l, by omega⟩
    let r' := if hr : r = n then .inr () else .inl ⟨r, by omega⟩
    m l' r'

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  match n with
  | 0 => fun a b ↦ m a b
  | n+1 =>
    let m' := nice m
    let a : Matrix (Fin n) (Fin n) α := m'.toBlocks₁₁
    let b := m'.toBlocks₁₂
    let c := m'.toBlocks₂₁
    let d := m'.toBlocks₂₂

    let η₁ := star_fin a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ := (d + η₃)^*
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    let m'' := Matrix.fromBlocks α β γ δ

    conice m''

theorem star_fin_lawful
    {α : Type} [Semiring α] [WeightedNetKAT.Star α]
    [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [WeightedNetKAT.LawfulStar α]
    [MulLeftMono α]
    [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
    -- [∀ n', MulLeftMono (Matrix (Fin n') (Fin n') α)]
    -- [∀ n', MulRightMono (Matrix (Fin n') (Fin n') α)]
    {n : ℕ}
    (m : Matrix (Fin n) (Fin n) α) :
    star_fin m = ω∑ i : ℕ, m^i := by
  induction n with
  | zero => ext ⟨_, hi⟩; omega
  | succ n ih =>
    simp [star_fin]
    simp [ih]
    simp [add_star]
    simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
    simp [← ωSum_mul_right, ← ωSum_mul_left, ← Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
    set QQQ := (nice m).toBlocks₂₂
    simp [LawfulStar.star_eq_sum]
    simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
    simp [← ωSum_mul_right, ← ωSum_mul_left, ← Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [conice]
    sorry
    -- split_ifs <;> subst_eqs
    -- · simp [QQQ]
    -- · simp
    -- · simp
    -- · simp
    -- split_ifs
    -- · subst_eqs
    --   simp
    --   -- rw [LawfulStar.star_eq_sum]
    --   simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
    -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
    -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
    -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  -- fun_induction star_fin with
  -- | case1 => ext ⟨_, h⟩; omega
  -- | case2 n' m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ ih =>
  --   simp [m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, m₁₀, m₁₁, m₁₂, m₁₃, m₁₄] at ih ⊢
  --   simp [ih]
  --   simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --   ext ⟨i, hi⟩ ⟨j, hj⟩
  --   simp [Matrix.add_apply, conice, fromBlocks]
  --   split_ifs
  --   · subst_eqs
  --     simp_all [Matrix.add_apply]
  --   · simp
  --   · simp
  --   · simp

  -- sorry
  -- -- fun_induction star_fin
  -- -- next => sorry
  -- -- next => sorry

instance instListed {A : Type} [DecidableEq A] [Listed A] : WeightedNetKAT.Star (Matrix A A α) where
  star m :=
    let m' := Matrix.listedEquivNat m
    let m'' := star_fin m'
    Matrix.listedEquivNat.symm m''

variable {𝒮 : Type} [Semiring 𝒮] [WeightedNetKAT.Star 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]
variable [LawfulStar 𝒮]
variable {X : Type} [Fintype X] [DecidableEq X] [Listed X]

instance : WeightedNetKAT.LawfulStar (Matrix X X 𝒮) where
  star_eq_sum m := by
    let m' := Matrix.listedEquivNat m
    convert congrArg Matrix.listedEquivNat.symm (star_fin_lawful m')
    refine (Equiv.apply_eq_iff_eq_symm_apply listedEquivNat).mp ?_
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [m', listedEquivNat, submatrix, Listed.decodeFin]
    congr with n
    induction n generalizing i j with
    | zero =>
      simp [Matrix.one_apply]
      split_ifs with h₁ h₂ h₃
      · rfl
      · have := congrArg Listed.encode h₁
        simp at this; contradiction
      · have := congrArg (Listed.decode (α:=X)) h₃
        simp_all
      · rfl
    | succ n ih =>
      simp [pow_succ, Matrix.mul_apply]
      symm
      apply Finset.sum_equiv Listed.equivFin.symm
      · simp
      · simp
        intro x
        simp [Listed.equivFin, Listed.decodeFin]
        rw [ih]

end Matrix.Star
