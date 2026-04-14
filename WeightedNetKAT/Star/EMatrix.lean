import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring.RingNF
import WeightedNetKAT.EMatrix
import WeightedNetKAT.Listed
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import WeightedNetKAT.MatrixStar

namespace Matrix.Star

open WeightedNetKAT

section

variable {α : Type*} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

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

instance {m n : ℕ} : HMul α (NMatrix m n α) (NMatrix m n α) where
    hMul s M := M.map (fun x ↦ s * x)
instance {m n : ℕ} : HMul (NMatrix m n α) α (NMatrix m n α) where
    hMul M s := M.map (fun x ↦ x * s)

instance : WeightedNetKAT.Star (NMatrix 1 1 α) where
  star a := .fill (a 0 0)^*

instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] : StarIter (NMatrix 1 1 α) where
  star_iter m := by
    simp [WeightedNetKAT.Star.star]
    nth_rw 2 [← StarIter.star_iter]
    ext ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ <;> try omega
    simp [NMatrix.fill, Matrix.mul_apply]

def star_fin' {n : ℕ} (m : NMatrix n n α) : NMatrix n n α :=
  match n with
  | 0 => .ofFn fun a b ↦ False.elim (by have := a.isLt; omega)
  | n'+1 =>
    let m' := m
    let a : NMatrix n' n' α := m'.toBlocks₁₁
    let b := m'.toBlocks₁₂
    let c := m'.toBlocks₂₁
    let d := m'.toBlocks₂₂

    let η₁ := star_fin' a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ : NMatrix 1 1 α := (d + η₃)^*
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    NMatrix.fromBlocks α β γ δ

/-- A more efficient version of `star_fin'` that splits the matrix up into four approximately equal
blocks. -/
def star_fin'' {n : ℕ} (M : NMatrix n n α) : NMatrix n n α :=
  let m := n / 2
  if h : m = 0 then
    if h : n = 0 then
      .ofFn fun a b ↦ False.elim (by have := a.isLt; omega)
    else
      .ofFn fun _ _ ↦ (M ⟨0, by grind⟩ ⟨0, by grind⟩)^*
  else
    let m' := n - m
    let M' : NMatrix (m + m') (m + m') α := ⟨M.data.cast (by simp [m, m']; grind)⟩
    -- let m' := m
    let a := M'.toBlocks₁₁
    let b := M'.toBlocks₁₂
    let c := M'.toBlocks₂₁
    let d := M'.toBlocks₂₂

    let η₁ := star_fin' a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ := star_fin' (d + η₃)
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    ⟨(NMatrix.fromBlocks α β γ δ).data.cast (by grind)⟩

-- NOTE: this should be `@[csimp]` once we've proven it correct
-- @[csimp]
theorem star_fin'_eq_star_fin'' : @star_fin' = @star_fin'' := by
  sorry

instance {n : ℕ} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star (NMatrix n n α) := ⟨star_fin'⟩
instance {n : Type*} [Listed n] [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star (EMatrix n n α) := inferInstanceAs (WeightedNetKAT.Star (NMatrix _ _ α))

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  star_fin' (.ofMatrix m) |>.asMatrix

end

theorem star_fin'_iter {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : NMatrix n n α) :
    1 + M * M^* = M^* := by
  induction n with
  | zero => ext ⟨_, _⟩; omega
  | succ n ih =>
    let a : NMatrix n n α := M.toBlocks₁₁
    let b := M.toBlocks₁₂
    let c := M.toBlocks₂₁
    let d := M.toBlocks₂₂

    set a' := star_fin' a
    have ha' : star_fin' a = a' := rfl
    replace ih : 1 + a * a' = a' := ih _

    wlog h : M = NMatrix.fromBlocks a b c d generalizing a b c d
    · absurd h; simp [a, b, c, d]
    · simp [h] at *
      simp [WeightedNetKAT.Star.star]
      rw [star_fin']
      simp only [NMatrix.fromBlocks_toBlocks₁₁, NMatrix.fromBlocks_toBlocks₁₂,
        NMatrix.fromBlocks_toBlocks₂₂, NMatrix.fromBlocks_toBlocks₂₁]
      simp only [ha']
      set δ' := (d + c * a' * b)^*
      simp [← NMatrix.mul_assoc]
      set γ' := δ' * c * a'
      have : a' * b * δ' * c * a' = a' * b * γ' := by simp [γ', NMatrix.mul_assoc]
      simp [this]; clear this
      set β' := a' * b * δ'
      set α' := a' + a' * b * γ'

      simp [NMatrix.fromBlocks_mul]
      rw [← NMatrix.fromBlocks_eq_one (α:=α) (n:=n) (m:=1)]
      simp [NMatrix.fromBlocks_add]
      have hδ : 1 + (d + c * a' * b) * δ' = δ' := by simp [δ']; exact StarIter.star_iter (d + c * a' * b)

      congr! 1
      · grind only [NMatrix.add_mul, add_assoc, NMatrix.one_mul, add_comm, NMatrix.mul_assoc,
        left_distrib]
      · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc]
      · simp [γ']
        nth_rw 2 [← ih]
        simp [α', γ', NMatrix.mul_add, ← NMatrix.mul_assoc]
        nth_rw 3 [← hδ]
        simp [NMatrix.add_mul]
        nth_rw 1 [← ih]
        simp [NMatrix.mul_add, ← NMatrix.mul_assoc, NMatrix.add_assoc]
        congr! 1
        nth_rw 4 [← ih]
        simp [NMatrix.mul_add, ← NMatrix.mul_assoc]
        nth_rw 3 [← ih]
        simp only [NMatrix.mul_add, NMatrix.mul_one]
        grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc,
          NMatrix.add_assoc]
      · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.mul_assoc, ← NMatrix.add_assoc]

instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] {n : ℕ} :
    StarIter (NMatrix n n α) := ⟨star_fin'_iter⟩

open OmegaCompletePartialOrder

instance {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α] [Mul α] [AddCommMonoid α] [IsPositiveOrderedAddMonoid α] [MulLeftMono α] {n : ℕ} :
    MulLeftMono (NMatrix n n α) := by
  constructor
  intro a b c h i j
  simp [Matrix.mul_apply]
  gcongr
  apply h
instance {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α] [Mul α] [AddCommMonoid α] [IsPositiveOrderedAddMonoid α] [MulRightMono α] {n : ℕ} :
    MulRightMono (NMatrix n n α) := by
  constructor
  intro a b c h i j
  simp [Matrix.mul_apply]
  gcongr
  apply h

open OmegaContinuousNonUnitalSemiring

attribute [simp] instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9

theorem ωSup_apply {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ}
    (x j : Fin n) (c : Chain (NMatrix n n α)) :
    ωSup c x j = ωSup (c.map ⟨fun n ↦ n x j, fun ⦃_ _⦄ a ↦ a x j⟩) := by
  simp [ωSup, Chain.map, OrderHom.comp]; unfold Function.comp; simp only [DFunLike.coe]; simp

instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ} :
    OmegaContinuousNonUnitalSemiring (NMatrix n n α) where
  ωScottContinuous_add_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, fun c ↦ ?_⟩
    ext i j
    convert ωScottContinuous_add_left (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
    · simp [ωSup_apply]
    · simp [ωSup_apply]; congr! 1; ext; simp
  ωScottContinuous_add_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, fun c ↦ ?_⟩
    ext i j
    convert ωScottContinuous_add_right (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
    · simp [ωSup_apply]
    · simp [ωSup_apply]; congr! 1; ext; simp
  ωScottContinuous_mul_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, fun c ↦ ?_⟩
    ext i j
    simp [mul_apply, ωSup_apply, mul_ωSup, sum_ωSup']
    congr! 1
    ext
    simp [mul_apply]
  ωScottContinuous_mul_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, fun c ↦ ?_⟩
    ext i j
    simp [mul_apply, ωSup_apply, ωSup_mul, sum_ωSup']
    congr! 1
    ext
    simp [mul_apply]

-- TODO: we need this
instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ} :
    LawfulStar (NMatrix n n α) where
  star_eq_sum m := by
    apply le_antisymm
    · rw [← star_fin'_iter, ← star_fin'_iter, ← star_fin'_iter, ← star_fin'_iter, ← star_fin'_iter, ← star_fin'_iter]
      simp [mul_add, ← add_assoc, ← pow_succ, ← mul_assoc]
      rw [ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ]
      simp [pow_succ', _root_.ωSum_mul_left, ← add_assoc, ← mul_assoc]
      gcongr
      sorry
    · simp [ωSum_nat_eq_ωSup]
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
        rw [← star_fin'_iter]
        rw [add_comm]
        gcongr

section

variable {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]

instance {n : Type*} [Listed n] : LawfulStar (EMatrix n n α) :=
  inferInstanceAs (LawfulStar (NMatrix (Listed.size n) (Listed.size n) α))
