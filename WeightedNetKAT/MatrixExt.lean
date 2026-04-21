module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import WeightedNetKAT.OmegaContinuousNonUnitalSemiring

@[expose] public section

open OmegaCompletePartialOrder
open scoped RightActions

namespace MatrixNotation

scoped notation "𝕄[" x ", " y ", " s "]" => Matrix x y s

/-- A column vector -/
scoped notation "C[" a "," b"]" => Matrix.fromCols a b
/-- A row vector -/
scoped notation "R[" a "," b"]" => Matrix.fromRows a b
/-- A block matrix -/
scoped notation "B[" "[" a ", " b "]" ", " "[" c ", " d "]" "]" => Matrix.fromBlocks a b c d

end MatrixNotation

open MatrixNotation

section

variable {𝒮 : Type*} [OmegaCompletePartialOrder 𝒮]

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

instance : OmegaCompletePartialOrder (𝕄[X,Y,𝒮]) :=
  inferInstanceAs (OmegaCompletePartialOrder (X → Y → 𝒮))

variable [OrderBot 𝒮]

instance : OrderBot (𝕄[X,Y,𝒮]) := inferInstanceAs (OrderBot (X → Y → 𝒮))

variable [AddCommMonoid 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

instance : IsPositiveOrderedAddMonoid (𝕄[X,Y,𝒮]) :=
  inferInstanceAs (IsPositiveOrderedAddMonoid (X → Y → 𝒮))

end

namespace Matrix

alias C_mul_R := Matrix.fromCols_mul_fromRows
alias C_mul_B := Matrix.fromCols_mul_fromBlocks
alias B_mul_B := Matrix.fromBlocks_multiply
alias B_mul_R := Matrix.fromBlocks_mul_fromRows

def unfold {A B C D α : Type*}
    (m : 𝕄[A,B,𝕄[C,D,α]]) : 𝕄[C,D,𝕄[A,B,α]] :=
  fun c d a b ↦ m a b c d

@[simp]
theorem unfold_apply {A B C D α : Type*} (m : 𝕄[A,B,𝕄[C,D,α]]) (c : C) (d : D) :
    m.unfold c d = fun a b ↦ m a b c d := rfl

def down {A B α : Type*} [Unique A] [Unique B] (m : 𝕄[A,B,α]) : α := m default default
-- TOOD: this should probably lift to a diagonal matrix
@[coe] def up {A B α : Type*} (a : α) : 𝕄[A,B,α] := fun _ _ ↦ a

instance {A B α : Type*} : Coe α 𝕄[A,B,α] := ⟨up⟩

@[simp]
theorem up_apply {A B α : Type*} (a : α) (x : A) (y : B) : Matrix.up (A:=A) (B:=B) a x y = a := rfl

@[simp]
def down_up {A B α : Type*} [AddCommMonoid α] [Unique A] [Unique B] (a : α) :
    (Matrix.up a : 𝕄[A,B,α]).down = a := by simp [down, up]
@[simp]
def up_down {A B α : Type*} [AddCommMonoid α] [Unique A] [Unique B] (m : 𝕄[A,B,α]) :
    (Matrix.up m.down : 𝕄[A,B,α]) = m := by simp [down]; ext; simp; congr <;> apply Unique.default_eq

@[simp]
def down_sum {ι A B α : Type*} [AddCommMonoid α] [Unique A] [Unique B] (f : ι → 𝕄[A,B,α]) (S : Finset ι) :
    (∑ x ∈ S, f x).down = ∑ x ∈ S, (f x).down := by
  simp [down, Matrix.sum_apply]
@[simp]
def down_add {A B α : Type*} [AddCommMonoid α] [Unique A] [Unique B] (m m' : 𝕄[A,B,α]) :
    (m + m').down = m.down + m'.down := by
  simp [down]
@[simp]
def down_mul {A B C α : Type*} [NonUnitalSemiring α] [Unique A] [Unique B] [Unique C] (m : 𝕄[A,B,α]) (m' : 𝕄[B,C,α]) :
    (m * m').down = m.down * m'.down := by
  simp [down, Matrix.mul_apply]
@[simp]
def down_mul_right {A B α : Type*} [NonUnitalSemiring α] [Unique A] [Unique B] (m : 𝕄[A,B,α]) (s : α) :
    (m <• s).down = m.down * s := by
  simp [down]
@[simp]
def down_zero {A B α : Type*} [AddCommMonoid α] [Unique A] [Unique B] :
    (0 : 𝕄[A,B,α]).down = 0 := by
  simp [down]
@[simp]
def down_smul_left {A B α : Type*} [NonUnitalSemiring α] [Unique A] [Unique B] (m : 𝕄[A,B,α]) (r : α) :
    (r •> m).down = r •> m.down := by
  simp [down]
@[simp]
def down_smul_right {A B α : Type*} [NonUnitalSemiring α] [Unique A] [Unique B] (m : 𝕄[A,B,α]) (r : α) :
    (m <• r).down = m.down <• r := by
  simp [down]

@[simp]
theorem up_add {A B α : Type*} [AddCommMonoid α] (a b : α) : Matrix.up (A:=A) (B:=B) (a + b) = ↑a + ↑b := rfl

def coe_unique_left {A A' B α : Type*} [Unique A] [Unique A'] (m : 𝕄[A,B,α]) : 𝕄[A',B,α] :=
  fun _ b ↦ m default b

theorem coe_unique_left_fun {A A' B α : Type*} [Unique A] [Unique A'] (f : A → B → α) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) (fun a b ↦ f a b) = fun _ b ↦ f default b := rfl
@[simp]
theorem coe_unique_left_apply {A A' B α : Type*} [Unique A] [Unique A'] (f : A → B → α) (a : A') (b : B) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) f a b = f default b := by
  simp [coe_unique_left]
@[simp]
theorem coe_unique_left_coe_unique_left {A A' A'' B α : Type*} [Unique A] [Unique A'] [Unique A''] (f : A → B → α) :
    coe_unique_left (A:=A') (A':=A'') (B:=B) (α:=α) (coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) f) = coe_unique_left (A:=A) (A':=A'') (B:=B) (α:=α) f := by
  ext; simp
@[simp]
theorem coe_unique_left_idem {A B α : Type*} [Unique A] (f : A → B → α) :
    coe_unique_left (A:=A) (A':=A) (B:=B) (α:=α) f = f := by
  ext; simp; congr; apply Unique.default_eq
@[simp]
theorem coe_unique_left_mul {A A' B C α : Type*} [Unique A] [Unique A'] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    [AddCommMonoid α] [Mul α]
    (f : 𝕄[A,B,α]) (g : 𝕄[B,C,α]) :
    coe_unique_left (A:=A) (A':=A') (B:=C) (α:=α) (f * g) = coe_unique_left f * g  := by
  ext a c
  simp [Matrix.mul_apply]
@[simp]
theorem coe_unique_left_Add {A A' B α : Type*} [Unique A] [Unique A'] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    [Add α]
    (f : 𝕄[A,B,α]) (g : 𝕄[A,B,α]) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) (f + g) = coe_unique_left f + coe_unique_left g  := by
  ext a c
  simp
@[simp]
theorem coe_unique_left_sum {A A' B ι α : Type*} [Unique A] [Unique A'] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [Fintype ι] [DecidableEq ι]
    [AddCommMonoid α] [Mul α]
    {S : Finset ι}
    (f : ι → 𝕄[A,B,α]) :
    (∑ i ∈ S, f i).coe_unique_left (A':=A') = ∑ i ∈ S, (f i).coe_unique_left := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S hx ih => simp_all



section

variable {𝒮 : Type*} [NonUnitalSemiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

@[simp]
theorem ωSum_apply {ι A B : Type*} [Countable ι] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] {f : ι → 𝕄[A,B,𝒮]} (a : A) :
    (ω∑ x, f x) a = ω∑ x, f x a := by
  convert _root_.ωSum_apply

@[simp]
theorem up_ωSum {ι A N : Type*} [Countable ι] [DecidableEq A] [Fintype A] [DecidableEq N] [Fintype N] {f : ι → 𝕄[A,A,𝒮]} :
    up (A:=N) (B:=N) (ω∑ x, f x) = ω∑ x, up (f x) := by
  ext n m a b
  simp

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem of_ωSum {ι A B : Type*} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    {f : ι → 𝕄[A,B,𝒮]} :
    Matrix.of (fun a b ↦ ω∑ x, f x a b) = ω∑ x, Matrix.of (fun a b ↦ f x a b) := by
  ext; simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem of_ωSum' {ι A B : Type*} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    {f : ι → 𝕄[A,B,𝒮]} :
    (fun a b ↦ ω∑ x, f x a b) = ω∑ x, (fun a b ↦ f x a b) := by
  ext; simp

theorem ωSum_mul_right {ι A B C : Type*} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    {f : ι → 𝕄[A,B,𝒮]} (a : 𝕄[B,C,𝒮]) :
    ω∑ x, f x * a = (ω∑ x, f x) * a := by
  ext a c; simp [mul_apply, ← _root_.ωSum_mul_right, ωSum_sum_comm]
theorem ωSum_mul_left {ι A B C : Type*} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    {f : ι → 𝕄[B,C,𝒮]} (a : 𝕄[A,B,𝒮]) :
    ω∑ x, a * f x = a * (ω∑ x, f x) := by
  ext a c; simp [mul_apply, ← _root_.ωSum_mul_left, ωSum_sum_comm]

instance {N : Type*} [DecidableEq N] [Fintype N] : MulLeftMono 𝕄[N,N,𝒮] where
  elim := by
    intro a b c hbc n n'
    simp [Matrix.mul_apply]
    gcongr with m
    exact hbc m n'
instance {N : Type*} [DecidableEq N] [Fintype N] : MulRightMono 𝕄[N,N,𝒮] where
  elim := by
    intro a b c hbc n n'
    simp [Function.swap, Matrix.mul_apply]
    gcongr with m
    exact hbc n m
open OmegaContinuousNonUnitalSemiring in
instance {N : Type*} [DecidableEq N] [Fintype N] : OmegaContinuousNonUnitalSemiring 𝕄[N,N,𝒮] where
  ωScottContinuous_add_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, fun c ↦ ?_⟩
    ext i j
    convert ωScottContinuous_add_left (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
  ωScottContinuous_add_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, fun c ↦ ?_⟩
    ext i j
    convert ωScottContinuous_add_right (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
  ωScottContinuous_mul_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, fun c ↦ ?_⟩
    ext i j
    have : ∀ x, ωSup c x j = ωSup (c.map ⟨fun n ↦ n x j, fun ⦃_ _⦄ a ↦ a x j⟩) := fun _ ↦ rfl
    simp [mul_apply, this, mul_ωSup, sum_ωSup']
    rfl
  ωScottContinuous_mul_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, fun c ↦ ?_⟩
    ext i j
    have : ∀ x, ωSup c i x = ωSup (c.map ⟨fun n ↦ n i x, fun ⦃_ _⦄ a ↦ a i x⟩) := fun _ ↦ rfl
    simp [mul_apply, this, ωSup_mul, sum_ωSup']
    rfl

end

open scoped RightActions
open OmegaCompletePartialOrder

@[simp]
theorem fun_one_mul {𝒮 m n : Type*} [Semiring 𝒮] [Fintype m] [Unique m] (x : 𝕄[m,n,𝒮]) :
    (@HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid (fun _ ↦ 1) x : 𝕄[m,n,𝒮]) = x := by
  ext; simp [mul_apply, ← Unique.default_eq]
@[simp]
theorem mul_fun_one {𝒮 m n : Type*} [Semiring 𝒮] [Fintype n] [Unique n] (x : 𝕄[m,n,𝒮]) :
    (@HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid x (fun _ ↦ 1) : 𝕄[m,n,𝒮]) = x := by
  ext; simp [mul_apply, ← Unique.default_eq]

theorem unit_mul_apply {α X Y : Type*} [AddCommMonoid α] [Mul α] (A : 𝕄[X,Unit,α]) (B : 𝕄[Unit,Y,α]) (x) (y) :
    (A * B) x y = A x () * B () y := by simp [mul_apply]

@[simp]
theorem smul_apply' {α X : Type*} [AddCommMonoid α] [Mul α] (r : α) (A : 𝕄[X,X,α]) (i j : X) :
    (A <• r) i j = (A i j) •> r := rfl

end Matrix
