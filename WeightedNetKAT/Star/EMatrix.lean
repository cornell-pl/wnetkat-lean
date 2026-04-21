module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring.RingNF
public import WeightedNetKAT.EMatrix
public import WeightedNetKAT.Listed
public import WeightedNetKAT.MatrixExt
public import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
public import WeightedNetKAT.Star.Matrix
import all Init.Data.Nat.Power2.Basic

@[expose] public section

namespace Matrix.Star

open WeightedNetKAT

open scoped MatrixNotation

section

variable {α : Type*} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

instance : WeightedNetKAT.Star 𝕄[𝟙,𝟙,α] where
  star m := (m () ())^*
instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [LawfulStar α] :
    LawfulStar 𝕄[𝟙,𝟙,α] where
  star_eq_sum m := by
    have := LawfulStar.star_eq_sum (m () ())
    ext ⟨⟩ ⟨⟩
    simp_all
    convert this; clear this
    rename_i n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Matrix.mul_apply, ih]

instance {m n : ℕ} : HMul α N𝕄[m,n,α] N𝕄[m,n,α] where
    hMul s M := M.map (fun x ↦ s * x)
instance {m n : ℕ} : HMul N𝕄[m,n,α] α N𝕄[m,n,α] where
    hMul M s := M.map (fun x ↦ x * s)

instance : WeightedNetKAT.Star N𝕄[1,1,α] where
  star a := .fill (a 0 0)^*

instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] : StarIter N𝕄[1,1,α] where
  star_iter m := by
    simp [WeightedNetKAT.Star.star]
    nth_rw 2 [← StarIter.star_iter]
    ext ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ <;> try omega
    simp [NMatrix.fill, Matrix.mul_apply]

def star_fin' {n : ℕ} (m : N𝕄[n,n,α]) : N𝕄[n,n,α] :=
  match n with
  | 0 => .ofFn fun a b ↦ False.elim (by have := a.isLt; omega)
  | n'+1 =>
    let m' := m
    let a : N𝕄[n',n',α] := m'.toBlocks₁₁
    let b := m'.toBlocks₁₂
    let c := m'.toBlocks₂₁
    let d := m'.toBlocks₂₂

    let η₁ := star_fin' a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ : N𝕄[1,1,α] := (d + η₃)^*
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    NMatrix.fromBlocks α β γ δ

def _root_.Nat.isPowerOfTwo_iff {n : ℕ} : n.isPowerOfTwo ↔ ∃ m, n = 2 ^ m := by rfl
def _root_.Nat.powTwoRec {motive : ℕ → Sort*} (base : motive 1) (induct : ∀ i, motive (2 ^ i) → motive (2 ^ i + 2 ^ i)) (n : ℕ) :
    motive (2 ^ n) := by
  induction n with
  | zero => exact base
  | succ n ih =>
    specialize induct n ih
    have : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by grind
    rw [← this]
    assumption
def _root_.Nat.powTwoRec' {motive : ℕ → Sort*} (base : motive 1) (induct : ∀ i, motive (2 ^ i) → motive (2 ^ i + 2 ^ i)) (n : ℕ) (hn : n.isPowerOfTwo) :
    motive n := by
  let r := Nat.powTwoRec base induct n.log2
  have : (2 ^ n.log2) = n := by rw [Nat.isPowerOfTwo_iff] at hn; obtain ⟨m, ⟨_⟩⟩ := hn; simp
  rw [this] at r
  exact r

def starFin₂ {n : ℕ} (h : n.isPowerOfTwo) : N𝕄[n,n,α] → N𝕄[n,n,α] :=
  let f₁ := fun M ↦ .ofFn fun _ _ ↦ (M ⟨0, by grind⟩ ⟨0, by grind⟩)^*
  let f₂ := fun n (f : N𝕄[2 ^ n,2 ^ n,α] → N𝕄[2 ^ n,2 ^ n,α]) (M : N𝕄[2 ^ n + 2 ^ n,2 ^ n + 2 ^ n,α]) ↦
    let a := M.toBlocks₁₁
    let b := M.toBlocks₁₂
    let c := M.toBlocks₂₁
    let d := M.toBlocks₂₂

    let η₁ := f a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ := f (d + η₃)
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    ⟨(NMatrix.fromBlocks α β γ δ).data.cast (by grind)⟩
  Nat.powTwoRec' (motive := fun n ↦ N𝕄[n,n,α] → N𝕄[n,n,α]) f₁ f₂ n h

/-- A more efficient version of `star_fin'` that splits the matrix up into four approximately equal
blocks. -/
def starFin {n : ℕ} (M : N𝕄[n,n,α]) : N𝕄[n,n,α] :=
  if hn : n.isPowerOfTwo then
    starFin₂ hn M
  else
    sorry

-- NOTE: this should be `@[csimp]` once we've proven it correct
-- @[csimp]
theorem star_fin'_eq_starFin : @star_fin' = @starFin := by
  sorry

instance {n : ℕ} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star N𝕄[n,n,α] := ⟨star_fin'⟩
instance {n : Type*} [Listed n] [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star (E𝕄[n,n,α]) := inferInstanceAs (WeightedNetKAT.Star (NMatrix _ _ α))

def star_fin {n : ℕ} (m : 𝕄[Fin n,Fin n,α]) : 𝕄[Fin n,Fin n,α] :=
  star_fin' (.ofMatrix m) |>.asMatrix

end

theorem star_fin'_iter {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : N𝕄[n,n,α]) :
    1 + M * M^* = M^* := by
  induction n with
  | zero => ext ⟨_, _⟩; omega
  | succ n ih =>
    let a : N𝕄[n,n,α] := M.toBlocks₁₁
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

-- TODO
theorem starFin_iter_pow_two {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : N𝕄[2 ^ n,2 ^ n,α]) :
    1 + M * starFin M = starFin M := by
  revert M
  apply Nat.powTwoRec (motive := fun n ↦ ∀ (M : N𝕄[n,n,α]), 1 + M * starFin M = starFin M) ?_ ?_ n
  · intro M
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp at hi hj
    subst_eqs
    simp [starFin, Matrix.mul_apply]
    sorry
  · clear n;
    intro n ih M
    let a : N𝕄[2 ^ n,2 ^ n,α] := M.toBlocks₁₁
    let b := M.toBlocks₁₂
    let c := M.toBlocks₂₁
    let d := M.toBlocks₂₂

    set a' := starFin a
    have ha' : starFin a = a' := rfl
    replace ih : 1 + a * a' = a' := ih _

    wlog h : M = NMatrix.fromBlocks a b c d generalizing a b c d
    · absurd h; simp [a, b, c, d]
    · simp [h] at *
      rw [starFin]
      sorry

theorem starFin_iter {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : N𝕄[n,n,α]) :
    1 + M * starFin M = starFin M := by
  if hm : n.isPowerOfTwo then
    obtain ⟨n, ⟨_⟩⟩ := hm
    exact starFin_iter_pow_two M
  else
    -- TODO: prove for non powers of two
    sorry

instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] {n : ℕ} :
    StarIter N𝕄[n,n,α] := ⟨star_fin'_iter⟩

open OmegaCompletePartialOrder

instance {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α] [Mul α] [AddCommMonoid α] [IsPositiveOrderedAddMonoid α] [MulLeftMono α] {n : ℕ} :
    MulLeftMono N𝕄[n,n,α] := by
  constructor
  intro a b c h i j
  simp [Matrix.mul_apply]
  gcongr
  apply h
instance {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α] [Mul α] [AddCommMonoid α] [IsPositiveOrderedAddMonoid α] [MulRightMono α] {n : ℕ} :
    MulRightMono N𝕄[n,n,α] := by
  constructor
  intro a b c h i j
  simp [Matrix.mul_apply]
  gcongr
  apply h

open OmegaContinuousNonUnitalSemiring

attribute [simp] instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9

theorem ωSup_apply {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ}
    (x j : Fin n) (c : Chain N𝕄[n,n,α]) :
    ωSup c x j = ωSup (c.map ⟨fun n ↦ n x j, fun ⦃_ _⦄ a ↦ a x j⟩) := by
  simp [ωSup, Chain.map, OrderHom.comp]; unfold Function.comp; simp only [DFunLike.coe]; simp

instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [MulLeftMono α] [MulRightMono α] [IsPositiveOrderedAddMonoid α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ} :
    OmegaContinuousNonUnitalSemiring N𝕄[n,n,α] where
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

axiom axiomNMatrixStarLeωSum {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ} (m : N𝕄[n,n,α]) :
    m^* ≤ ω∑ n, m ^ n

-- TODO: we need this to show that our algorithms are computable; `axiomNMatrixStarLeωSum` for now
instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α] {n : ℕ} :
    LawfulStar N𝕄[n,n,α] where
  star_eq_sum m := by
    apply le_antisymm
    · exact axiomNMatrixStarLeωSum m
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

instance {n : Type*} [Listed n] : LawfulStar (E𝕄[n,n,α]) :=
  inferInstanceAs (LawfulStar (NMatrix (Listed.size n) (Listed.size n) α))
