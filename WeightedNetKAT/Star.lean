import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import WeightedNetKAT.Listed
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.EMatrix
import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import Mathlib.Tactic.Ring.RingNF

namespace Matrix

variable {l m n m' n' α : Type*}
variable [Listed l] [DecidableEq l] [Listed m] [DecidableEq m] [Listed n] [DecidableEq n]
variable [Listed m'] [DecidableEq m'] [Listed n'] [DecidableEq n']

def concrete (M : Matrix m n α) : Matrix m n α := EMatrix.ofMatrix M |>.asMatrix

def concrete_concrete (M : Matrix m n (Matrix m' n' α)) : Matrix m n (Matrix m' n' α) :=
  (M.concrete.map .concrete).concrete

@[simp] theorem concrete_id : Matrix.concrete (m:=m) (n:=n) (α:=α) = id := by ext; simp [concrete]
@[simp] theorem concrete_concrete_id :
    Matrix.concrete_concrete (m:=m) (n:=n) (m':=m') (n':=n') (α:=α) = id := by ext; simp [concrete_concrete]

end Matrix

namespace WeightedNetKAT

/-- `Star` introduces notation `m^*` which is supposed to satisfy `m^* = ω∑ n : ℕ, m^n`. Note that
  this is not imposed by the `Star` type class but rather `LawfulStar` since it requires
  `OmegaCompletePartialOrder` which is in general non-computable.
-/
class Star (α : Type*) where
  star : α → α
@[inherit_doc Star]
postfix:max "^*" => WeightedNetKAT.Star.star
class LawfulStar (α : Type*)
    [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] where
  star_eq_sum : ∀ m : α, m^* = ω∑ n : ℕ, m^n
class StarIter (α : Type*) [One α] [Mul α] [Add α] [Star α] where
  star_iter : ∀ m : α, 1 + m * m^* = m^*

open OmegaCompletePartialOrder

def lawfulStarOf {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [MulLeftMono α]
    (h : ∀ m : α, m^* = 1 + m * m^*)
    (h' : ∀ (a c : α), 1 + c * a ≤ c → a^* ≤ c) :
    ∀ m : α, m^* = ω∑ n : ℕ, m^n := by
  intro m
  simp [ωSum_nat_eq_ωSup]
  apply le_antisymm
  · clear h'
    sorry
  · simp
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
      rw [h, add_comm]
      gcongr

def lawfulStarOf' {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [MulLeftMono α]
    (h : ∀ m : α, m^* = 1 + m * m^*)
    (h' : ∀ (a c : α), 1 + c * a ≤ c → a^* ≤ c) :
    LawfulStar α := ⟨lawfulStarOf h h'⟩

instance instUnitStar {α : Type*} [Star α] : Star (Matrix Unit Unit α) where
  star m := fun α β ↦ (m α β)^*
-- instance : LawfulStar (Matrix Unit Unit 𝒮) where
--   star_eq_sum := sorry

variable {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [LawfulStar α]
variable [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]

theorem ωSup_pow {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α]
    (f : ℕ → α) (hf : Monotone f) (i : ℕ) :
      ωSup ⟨fun n ↦ (f n)^i, fun a b hab ↦ by simp; gcongr; exact hf hab⟩
    = ωSup ⟨fun n ↦ f n, hf⟩ ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [pow_succ]
    rw [← ih]
    simp [ωSup_mul_ωSup]

-- omit [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α] in
-- theorem asdasd {e x f : α} (h : f + e * x ≤ x) : e^* * f ≤ x := by
--   simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
--   simp [← ωSum_mul_left]
--   simp [ωSum_nat_eq_ωSup]
--   apply le_trans _ (le_ωSum_of_finset {1})
--   simp

/-- **(A.10)**  -/
theorem star_iter {a : α} :
    1 + a * a^* = a^* := by
  simp [LawfulStar.star_eq_sum]
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [pow_succ', ωSum_mul_left]

theorem help_me {a b c : α} :
    a * b^* * c = ωSup ⟨fun i ↦ a * b^i * c, sorry⟩ := by
  simp [LawfulStar.star_eq_sum]
  simp [← ωSum_mul_left, ← ωSum_mul_right]
  rw [ωSum_nat_eq_succ]
  simp [ωSum_nat_eq_ωSup]
  simp [add_ωSup]
  congr! 3 with n
  induction n with
  | zero => simp
  | succ n ih =>
    simp_all [Finset.sum_range_succ]
    simp [← Finset.sum_mul] at ih ⊢
    rw [← add_assoc]
    rw [ih]
    sorry
  -- nth_rw 2 [ωSum_nat_eq_succ]
  -- simp [pow_succ', ωSum_mul_left]

instance : StarIter α where star_iter _ := star_iter

/-- **(A.11)**  -/
theorem star_iter' {a : α} :
    1 + a^* * a = a^* := by
  simp [LawfulStar.star_eq_sum]
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [pow_succ, ωSum_mul_right]

omit [MulRightMono α] [OmegaContinuousNonUnitalSemiring α] in
theorem idk_left {a c : α} (h : 1 + a * c ≤ c) : a^* ≤ c := by
  simp [LawfulStar.star_eq_sum, ωSum_nat_eq_ωSup]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    simp [Finset.sum_range_succ']
    apply le_trans _ h
    rw [add_comm]
    simp [pow_succ', ← Finset.mul_sum]
    gcongr
omit [MulLeftMono α] [OmegaContinuousNonUnitalSemiring α] in
theorem idk_right {a c : α} (h : 1 + c * a ≤ c) : a^* ≤ c := by
  simp [LawfulStar.star_eq_sum, ωSum_nat_eq_ωSup]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    simp [Finset.sum_range_succ']
    apply le_trans _ h
    rw [add_comm]
    simp [pow_succ, ← Finset.sum_mul]
    gcongr

/-- **(A.12)**  -/
theorem A12 {a b c : α} (h : b + a * c ≤ c) : a^* * b ≤ c := by
  simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
  simp [ωSum_nat_eq_ωSup]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    simp [Finset.sum_range_succ']
    simp [pow_succ', mul_assoc, ← Finset.mul_sum]
    apply le_trans _ h
    rw [add_comm]
    gcongr
/-- **(A.13)**  -/
theorem A13 {a b c : α} (h : b + c * a ≤ c) : b * a^* ≤ c := by
  simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
  simp [ωSum_nat_eq_ωSup]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    simp [Finset.sum_range_succ']
    simp [pow_succ, ← Finset.sum_mul, ← mul_assoc]
    apply le_trans _ h
    rw [add_comm]
    gcongr

/-- **(A.14)**  -/
theorem A14 {a c : α} (h : a * c ≤ c) : a^* * c ≤ c := by
  simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
  simp [ωSum_nat_eq_ωSup]
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    simp_all [Finset.sum_range_succ']
    simp [pow_succ', ← Finset.mul_sum, mul_assoc]
    apply le_trans _ h
    sorry

theorem mul_star_le_star {a : α} :
    a * a^* ≤ a^* := by
  simp [LawfulStar.star_eq_sum, ← ωSum_mul_left, ← pow_succ']
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [le_add_of_nonneg_left]

-- theorem idk {a c : α} (h : a * c ≤ c) : a^* * c ≤ c := by
--   simp [LawfulStar.star_eq_sum]
--   simp [← ωSum_mul_right]
--   rw [ωSum_nat_eq_ωSup]
--   simp
--   intro i
--   induction i with
--   | zero => simp
--   | succ i ih =>
--     simp_all [Finset.sum_range_succ]
--     sorry

--  Lemma star_distr (a b: X A A): (a + b)# == a# * (b*a#)#.
--   Proof.
--     apply leq_antisym.
--     star_left_induction.
--     semiring_normalize.
--     ac_rewrite (star_make_right (b*a#)).
--     rewrite <- (star_make_right a) at 4.
--     semiring_reflexivity.
--     rewrite <- (star_trans (a+b)).
--     apply dot_incr.
--      apply star_incr. auto with algebra.
--      rewrite <- (star_idem (a+b)). apply star_incr.
--     rewrite <- (a_star_a_leq_star_a (a+b)).
--     apply dot_incr. auto with algebra.
--     apply star_incr. auto with algebra.
--   Qed.

omit [OmegaContinuousNonUnitalSemiring α] in
@[gcongr]
theorem star_le_star {a b : α} (h : a ≤ b) : a^* ≤ b^* := by
  simp [LawfulStar.star_eq_sum]
  apply ωSum_mono fun i ↦ ?_
  induction i with
  | zero => simp
  | succ i ih => simp [pow_succ]; gcongr

theorem add_star {a b : α} :
    (a + b)^* = a^* * (b * a^*)^* := by
  apply le_antisymm
  · apply idk_left
    simp [right_distrib, ← add_assoc, ← mul_assoc]
    rw [add_assoc]
    nth_rw 2 [add_comm]
    rw [← add_assoc]
    simp [star_iter]
    nth_rw 6 [← star_iter]
    simp [right_distrib]
  · sorry
    -- NOTE: not sound
    -- rw [← star_mul_star (a:=a + b)]
    -- gcongr ?_^* * ?_
    -- · refine le_add_of_le_of_nonneg (by rfl) (by simp)
    -- · apply idk_right
    --   nth_rw 3 [← star_iter']
    --   apply add_le_add (by rfl)
    --   simp [left_distrib, ← mul_assoc]
    --   nth_rw 2 [← star_iter']
    --   simp [left_distrib, ← mul_assoc]
    --   rw [add_comm]
    --   gcongr
    --   nth_rw 2 [← star_mul_star (a:=a + b)]
    --   simp [mul_assoc]
    --   gcongr
    --   nth_rw 2 [← star_iter]
    --   simp [right_distrib, ← add_assoc]
    --   refine le_add_of_nonneg_of_le (by simp) ?_
    --   gcongr
    --   refine le_add_of_le_of_nonneg (by rfl) (by simp)

theorem add_star' {a b : α} :
    (a + b)^* = (a^* * b)^* * a^* := by
  apply le_antisymm
  · apply idk_right
    simp [left_distrib, ← add_assoc, mul_assoc]
    rw [add_assoc]
    nth_rw 2 [add_comm]
    rw [← add_assoc]
    simp [star_iter']
    nth_rw 8 [← star_iter']
    simp [left_distrib]
  · sorry
    -- NOTE: not sound
    -- rw [← star_mul_star (a:=a + b)]
    -- gcongr ?_ * ?_^*
    -- · apply idk_left
    --   nth_rw 3 [← star_iter]
    --   apply add_le_add (by rfl)
    --   simp [right_distrib, mul_assoc]
    --   nth_rw 1 [← star_iter]
    --   simp [right_distrib, mul_assoc]
    --   rw [add_comm]
    --   gcongr a * ?_ + ?_
    --   nth_rw 2 [← star_mul_star (a:=a + b)]
    --   gcongr
    --   · refine le_add_of_le_of_nonneg (by rfl) (by simp)
    --   · nth_rw 2 [← star_iter]
    --     simp [right_distrib, ← add_assoc]
    --     refine le_add_of_nonneg_of_le (by simp) ?_
    --     gcongr
    -- · refine le_add_of_le_of_nonneg (by rfl) (by simp)

theorem mul_star {a b : α} :
    (a * b)^* = 1 + a * (b * a)^* * b := by
  simp only [LawfulStar.star_eq_sum, ← ωSum_mul_left, ← ωSum_mul_right]
  nth_rw 1 [ωSum_nat_eq_succ]
  simp only [pow_zero]
  congr with n
  induction n with
  | zero => grind [mul_one]
  | succ n ih => rw [pow_succ]; grind [mul_assoc]

theorem least_q {a b : α} : IsLeast {x | b + a * x = x} (a^* * b) := by
  constructor
  · simp
    nth_rw 2 [← star_iter]
    simp [← mul_assoc, right_distrib]
  · intro c h
    simp only [Set.mem_setOf_eq] at h
    apply A12 (le_of_eq h)

end WeightedNetKAT

def Matrix.listedEquivNat {α A : Type*} [DecidableEq A] [i : Listed A] :
    Matrix A A α ≃ Matrix (Fin i.size) (Fin i.size) α :=
  ⟨fun m ↦ m.submatrix Listed.decodeFin Listed.decodeFin,
   fun m ↦ m.submatrix Listed.encodeFin Listed.encodeFin,
   by intro m; ext i j; simp,
   by intro m; ext i j; simp⟩
