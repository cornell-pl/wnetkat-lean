import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import WeightedNetKAT.Listed
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import Mathlib.Tactic.Ring.RingNF

structure NMatrix (m n : ℕ) (α : Type*) where
  data : Vector α (m * n)

namespace NMatrix

variable {l m m' n n' : ℕ} {α : Type*}
variable {X X' : NMatrix m n α}
variable {Y Y' : NMatrix n l α}

@[inline]
def ofFn (f : Fin m → Fin n → α) : NMatrix m n α :=
  ⟨.ofFn fun i ↦ f i.divNat i.modNat⟩

@[inline]
def get (M : NMatrix m n α) (i : Fin m) (j : Fin n) : α :=
  M.data[i.val * n + j.val]'(by
    rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
    clear X X' Y Y' M
    rcases n with _ | n <;> rcases m with _ | m <;> try omega
    simp_all
    simp_all [Nat.lt_succ_iff]
    ring_nf
    simp [add_assoc]
    nth_rw 3 [add_comm]
    simp [Nat.lt_add_one_iff]
    ring_nf
    calc
      i + i * n + j ≤ m + m * n + n := by gcongr
      _ ≤ n + n * m + m := by ring_nf; rfl)

@[ext]
theorem ext (h : ∀ i j, X.get i j = X'.get i j) : X = X' := by
  cases X; cases X'
  congr
  simp_all [get]
  ext i hi
  specialize h (⟨i, hi⟩ : Fin _).divNat (⟨i, hi⟩ : Fin _).modNat
  simp_all [Nat.div_add_mod']

@[simp, grind]
theorem ofFn_get {f : Fin m → Fin n → α} : (ofFn f).get = f := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp [ofFn, get]
  rcases n with _ | n <;> rcases m with _ | m <;> try omega
  congr
  · simp [Fin.divNat]
    rw [Nat.add_div]
    · have : ¬n + 1 ≤ j := by omega
      simp [Nat.mod_eq_of_lt, hj, this]
    · simp
  · simp [Fin.modNat]
    omega

@[simp, grind]
theorem get_ofFn : ofFn X.get = X := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases n with _ | n <;> rcases m with _ | m <;> try omega
  simp [ofFn, get]
  have : ¬n + 1 ≤ j := by omega
  simp [Nat.mod_eq_of_lt, hj]
  congr
  rw [Nat.add_div]
  · simp [Nat.mod_eq_of_lt, hj, this]
  · omega

def toBlocks₁₁ (M : NMatrix (m + m') (n + n') α) : NMatrix m n α :=
  .ofFn fun i j ↦ M.get ⟨i, by omega⟩ ⟨j, by omega⟩
def toBlocks₁₂ (M : NMatrix (m + m') (n + n') α) : NMatrix m n' α :=
  .ofFn fun i j ↦ M.get ⟨i, by omega⟩ ⟨n + j, by omega⟩
def toBlocks₂₁ (M : NMatrix (m + m') (n + n') α) : NMatrix m' n α :=
  .ofFn fun i j ↦ M.get ⟨m + i, by omega⟩ ⟨j, by omega⟩
def toBlocks₂₂ (M : NMatrix (m + m') (n + n') α) : NMatrix m' n' α :=
  .ofFn fun i j ↦ M.get ⟨m + i, by omega⟩ ⟨n + j, by omega⟩

def fromBlocks
    (m₁₁ : NMatrix m n α) (m₁₂ : NMatrix m n' α) (m₂₁ : NMatrix m' n α) (m₂₂ : NMatrix m' n' α) :
    NMatrix (m + m') (n + n') α :=
  .ofFn fun i j ↦
    if _ : i < m then
      if _ : j < n then
        m₁₁.get ⟨i, by omega⟩ ⟨j, by omega⟩
      else
        m₁₂.get ⟨i, by omega⟩ ⟨j - n, by omega⟩
    else
      if _ : j < n then
        m₂₁.get ⟨i - m, by have := i.isLt; omega⟩ ⟨j, by omega⟩
      else
        m₂₂.get ⟨i - m, by omega⟩ ⟨j - n, by omega⟩

def asMatrix (M : NMatrix m n α) : Matrix (Fin m) (Fin n) α := M.get
def ofMatrix (M : Matrix (Fin m) (Fin n) α) : NMatrix m n α := .ofFn M

@[simp, grind] theorem asMatrix_ofMatrix : NMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind] theorem ofMatrix_asMatrix {M : Matrix (Fin m) (Fin n) α} :
    (NMatrix.ofMatrix M).asMatrix = M := by
  simp [ofMatrix, asMatrix]

@[simp, grind]
theorem ofFn_asMatrix {f : Fin m → Fin n → α} : (ofFn f).asMatrix = f := ofFn_get
@[simp, grind]
theorem ofMatrix_get {f : Fin m → Fin n → α} : (NMatrix.ofMatrix f).get = f := ofFn_get

def map {β : Type} (M : NMatrix m n α) (f : α → β) : NMatrix m n β :=
  ⟨M.data.map f⟩

instance [Zero α] [One α] : One (NMatrix n n α) := ⟨NMatrix.ofMatrix 1⟩
instance [Zero α] : Zero (NMatrix n n α) := ⟨NMatrix.ofMatrix 0⟩

instance [Add α] : Add (NMatrix m n α) where
  add a b := .ofMatrix (a.asMatrix + b.asMatrix)
instance [Mul α] [AddCommMonoid α] : HMul (NMatrix l m α) (NMatrix m n α) (NMatrix l n α) where
  hMul a b := .ofMatrix (a.asMatrix * b.asMatrix)

@[simp]
theorem add_get [Add α] : (X + X').get = X.get + X'.get := by
  unfold instAdd
  rw [HAdd.hAdd, instHAdd]
  simp
  rfl

theorem asMatrix_add [Add α] : (X + X').asMatrix = X.asMatrix + X'.asMatrix := by simp [asMatrix]

@[simp]
theorem mul_get [Mul α] [AddCommMonoid α] : (X * Y).get = X.asMatrix * Y.asMatrix := by
  simp [HMul.hMul]

theorem asMatrix_mul [Mul α] [AddCommMonoid α] : (X * Y).asMatrix = X.asMatrix * Y.asMatrix := by simp [asMatrix]

#eval! (NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)) + NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)

end NMatrix

def EMatrix (m n α : Type) [Listed m] [Listed n] := NMatrix (Listed.size m) (Listed.size n) α

-- structure EMatrix (m n α : Type) [instm : Listed m] [instn : Listed n] where
--   data : Vector α (instm.size * instn.size)
-- deriving DecidableEq

namespace EMatrix

variable {l m n α : Type} [lListed : Listed l] [mListed : Listed m] [nListed : Listed n]
variable {m' n' : Type} [Listed m'] [Listed n']
variable {X X' : EMatrix m n α}
variable {Y Y' : EMatrix n l α}

def get (M : EMatrix m n α) (i : m) (j : n) : α :=
  let i' := Listed.encodeFin i
  let j' := Listed.encodeFin j
  NMatrix.get M i' j'

def ofFn (f : Fin (Listed.size m) → (Fin (Listed.size n)) → α) : EMatrix m n α :=
  NMatrix.ofFn fun i j ↦ f i j
def ofFnSlow (f : m → n → α) : EMatrix m n α :=
  NMatrix.ofFn fun i j ↦ f (Listed.decodeFin i) (Listed.decodeFin j)

@[simp, grind]
theorem ofFnSlow_get {f : m → n → α} : (ofFnSlow f).get = f := by
  ext i j
  simp [ofFnSlow, get]

@[simp, grind]
theorem get_ofFnSlow : ofFnSlow X.get = X := by
  simp [ofFnSlow]
  sorry

@[simp, grind]
theorem ofFn_get {f : Fin (Listed.size m) → Fin (Listed.size n) → α} : (ofFn f).get = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext i j
  simp [ofFn, get]

@[simp, grind]
theorem get_ofFn : ofFn (NMatrix.get X) = X := by simp [ofFn]

def asMatrix (M : EMatrix m n α) : Matrix m n α := M.get
def ofMatrix (M : Matrix m n α) : EMatrix m n α := .ofFnSlow M

@[simp, grind]
theorem ofFnSlow_asMatrix {f : m → n → α} : (ofFnSlow f).asMatrix = f := ofFnSlow_get
@[simp, grind]
theorem ofMatrix_get {f : m → n → α} : (EMatrix.ofMatrix f).get = f := ofFnSlow_get

@[simp, grind] theorem asMatrix_ofMatrix : EMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind] theorem ofMatrix_asMatrix {M : Matrix m n α} :
    (EMatrix.ofMatrix M).asMatrix = M := by
  simp [ofMatrix, asMatrix]

def map {β: Type} (f : α → β) (M : EMatrix m n α) : EMatrix m n β :=
  .ofFn fun i j ↦ f (NMatrix.get M i j)

def asNMatrix (X : EMatrix m n α) : NMatrix (Listed.size m) (Listed.size n) α := X
def asNMatrix₂ (X : EMatrix m n (EMatrix m' n' α)) : NMatrix (Listed.size m) (Listed.size n) (NMatrix (Listed.size m') (Listed.size n') α) := X

theorem eq_of_asNMatrix (h : X.asNMatrix = X'.asNMatrix) : X = X' := h

@[ext]
theorem ext (h : ∀ i j, X.get i j = X'.get i j) : X = X' := by
  apply eq_of_asNMatrix
  ext i j
  specialize h (Listed.decodeFin i) (Listed.decodeFin j)
  simp [get] at h
  exact h

def asNatMatrix (X : EMatrix m n α) : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) α :=
  NMatrix.get X
def ofNatMatrix (X : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) α) : EMatrix m n α :=
  NMatrix.ofFn X

def asMatrix₂ (M : EMatrix m n (EMatrix m' n' α)) : Matrix m n (Matrix m' n' α) := fun i j i' j' ↦ (M.get i j).get i' j'
def ofMatrix₂ (M : Matrix m n (Matrix m' n' α)) : EMatrix m n (EMatrix m' n' α) := (EMatrix.ofFnSlow M).map .ofMatrix

def asNatMatrix₂ (M : EMatrix m n (EMatrix m' n' α)) :
    Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) (Matrix (Fin (Listed.size m')) (Fin (Listed.size n')) α) :=
  fun i j i' j' ↦ NMatrix.get (NMatrix.get M i j) i' j'
def ofNatMatrix₂ (M : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) (Matrix (Fin (Listed.size m')) (Fin (Listed.size n')) α)) :
    EMatrix m n (EMatrix m' n' α) := (NMatrix.ofFn M).map .ofNatMatrix

-- @[simp, grind]
-- theorem ofFn_asMatrix₂ {f : m → n → α} : (ofFn f).asMatrix₂ = f := ofFn_get
-- @[simp, grind]
-- theorem ofMatrix₂_get {f : m → n → EMatrix m' n' α} : (EMatrix.ofMatrix₂ f).get = f := ofFn_get

@[simp, grind] theorem asMatrix₂_ofMatrix₂ {X : EMatrix m n (EMatrix m' n' α)} : EMatrix.ofMatrix₂ X.asMatrix₂ = X := by
  simp [ofMatrix₂]
  ext i j i' j'
  simp [map, asMatrix₂, ofFnSlow]
omit [Listed m'] [Listed n'] in
@[simp, grind] theorem ofMatrix₂_asMatrix₂ {M : Matrix m n (Matrix m' n' α)} :
    (EMatrix.ofMatrix M).asMatrix = M := by
  simp [ofMatrix, asMatrix]


theorem eq_ofMatrix (h : X.asMatrix = X'.asMatrix) : X = X' := by
  ext i j; exact congrFun₂ h i j

instance [Add α] : Add (EMatrix m n α) where
  add a b := .ofNatMatrix (a.asNatMatrix + b.asNatMatrix)

instance [Zero α] : Zero (EMatrix m n α) := ⟨EMatrix.ofNatMatrix 0⟩

@[simp]
theorem zero_get [Zero α] : (0 : EMatrix m n α).get = 0 := by
  ext i j
  simp
  suffices (EMatrix.ofMatrix (0 : Matrix _ _ α)).get i j = 0 by convert this
  simp

@[simp]
theorem zero_asMatrix [Zero α] : EMatrix.asMatrix (0 : EMatrix m n α) = 0 := by
  ext; simp [asMatrix]

instance [Mul α] {X Y : Type} [Listed X] [Listed Y] : HSMul α (EMatrix X Y α) (EMatrix X Y α) where
  hSMul s m := m.map (s * ·)

open scoped RightActions

instance [Mul α] {X Y : Type} [Listed X] [Listed Y] : HSMul αᵐᵒᵖ (EMatrix X Y α) (EMatrix X Y α) where
  hSMul s m := m.map (· * s.unop)

@[simp]
theorem add_get [Add α] : (X + X').get = X.get + X'.get := by
  unfold instAdd
  rw [HAdd.hAdd, instHAdd]
  simp
  sorry
  -- rfl

@[simp] theorem asMatrix_add [Add α] : (X + X').asMatrix = X.asMatrix + X'.asMatrix := by simp [asMatrix]

instance [AddCommMonoid α] : AddCommMonoid (EMatrix m n α) where
  add_assoc X Y Z := by apply eq_ofMatrix; simp [add_assoc]
  add_comm X Y := by apply eq_ofMatrix; simp [add_comm]
  zero_add X := by apply eq_ofMatrix; simp
  add_zero X := by apply eq_ofMatrix; simp
  nsmul n X := .ofMatrix (n * X.asMatrix)
  nsmul_zero X := by apply eq_ofMatrix; simp; apply AddMonoid.nsmul_zero
  nsmul_succ X Y := by apply eq_ofMatrix; simp; apply AddMonoid.nsmul_succ


instance [Fintype m] [Mul α] [AddCommMonoid α] : HMul (EMatrix l m α) (EMatrix m n α) (EMatrix l n α) where
  hMul a b := .ofNatMatrix (a.asNatMatrix * b.asNatMatrix)

@[simp]
theorem mul_get [Fintype n] [Mul α] [AddCommMonoid α] : (X * Y).get = X.asMatrix * Y.asMatrix := by
  simp [HMul.hMul]
  sorry

theorem asMatrix_mul [Fintype n] [Mul α] [AddCommMonoid α] : (X * Y).asMatrix = X.asMatrix * Y.asMatrix := by simp [asMatrix]

#eval! (EMatrix.ofFnSlow (m:=Fin 2) (n:=Fin 2) (α:=ℕ × ℕ) fun i j ↦ (i, j)) + EMatrix.ofFnSlow (m:=Fin 2) (n:=Fin 2) (α:=ℕ × ℕ) fun i j ↦ (i, j)

instance [Zero α] [One α] [DecidableEq n] : One (EMatrix n n α) := ⟨EMatrix.ofMatrix 1⟩

-- instance [Semiring α] : Semiring (EMatrix n n α) where
--   add_assoc := by sorry


end EMatrix

namespace Matrix

variable {l m n m' n' α : Type}
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


-- NOTE: not sound
-- theorem star_mul_star {a : α} :
--     a^* * a^* = a^* := by
--   -- apply le_antisymm
--   -- · have : a * a^* ≤ a^* := by nth_rw 2 [← star_iter]; refine le_add_of_nonneg_left (by simp)
--   --   apply le_trans _ this
--   --   nth_rw 3 [← star_iter]
--   --   sorry
--   -- simp [LawfulStar.star_eq_sum, ← ωSum_mul_right, ← ωSum_mul_left]
--   -- simp [← pow_add]
--   -- sorry
--   apply le_antisymm
--   · simp [LawfulStar.star_eq_sum, ← ωSum_mul_right, ← ωSum_mul_left]
--     simp [ωSum_nat_eq_ωSup, sum_ωSup']
--     intro i j
--     rw [sum_ωSup']
--     simp
--     sorry

--   -- symm
--   -- apply ωSum_eq_ωSum_of_ne_one_bij fun ⟨(i, j), b⟩ ↦ Nat.pair i j
--   -- · intro ⟨l, hl⟩ ⟨r, hr⟩ h
--   --   simp_all
--   --   grind
--   -- · intro i h
--   --   simp_all
--   --   let x := Nat.unpair i
--   --   use x.1, x.2
--   --   simp [x]
--   --   simp [pow_add]
--   --   contrapose! h
--   --   sorry
--   -- · simp
--   --   intro i j h
--     -- have := pow_eq_zero (n:=i) (a:=a)
--     -- rcases

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


theorem uniqueness {a b x : α} (h : b + a * x = x) : x = a^* * b := by
  apply le_antisymm
  · simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
    simp [ωSum_nat_eq_ωSup]
    have : ∀ {a : α} (C : Chain α), (a ≤ ωSup C ↔ ∀ (b : α), (∀ i, C i ≤ b) → a ≤ b) := by
      intro a C
      constructor
      · intro h b h'
        apply le_trans h
        simp [h']
      · intro h

        sorry
    simp [this]; clear this
    intro c hc
    rw [← h]
    apply le_trans _ (hc 3)
    simp [Finset.sum_range_succ]
    sorry

    -- have : b + a * a^* * b ≤ a^* * b := by
    --   nth_rw 2 [← star_iter]
    --   simp [right_distrib]
    -- apply le_trans _ this
    -- rw [← h, mul_assoc]
    -- gcongr

    -- sorry
  · apply A12 (le_of_eq h)
  -- have ⟨h₁, h₂⟩ := least_q (a:=a) (b:=b)
  -- simp [IsLeast, lowerBounds] at h₁ h₂
  -- rw [← h₁]

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

def conice {n : ℕ} (m : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α) : Matrix (Fin (n + 1)) (Fin (n + 1)) α :=
  Matrix.concrete fun l r =>
    let l' := if hl : l = n then .inr () else .inl ⟨l, by omega⟩
    let r' := if hr : r = n then .inr () else .inl ⟨r, by omega⟩
    m l' r'

def star_fin' {n : ℕ} (m : NMatrix n n α) : NMatrix n n α :=
  let res : NMatrix n n α :=
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

      let δ : NMatrix 1 1 α := .ofFn fun _ _ ↦ ((d + η₃).get 0 0)^*
      let γ := δ * η₂
      let β := η₂' * δ
      let α := η₁ + β * η₂

      let m'' := NMatrix.fromBlocks α β γ δ

      m''

  -- printprint f!"star_fin({n})" res
  res

def star_fin_old {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  let res : Matrix (Fin n) (Fin n) α :=
    match n with
    | 0 => fun a b ↦ False.elim (by have := a.isLt; omega)
    | 1 =>
      let x := (m 0 0)^*
      fun _ _ ↦ x
    | 2 =>
      let m' := nice m

      let i₁ := .inl 0
      let i₂ := .inr ()

      let a := m' i₁ i₁
      let b := m' i₁ i₂
      let c := m' i₂ i₁
      let d := m' i₂ i₂

      let η₁ := a^*
      let η₂ := c * η₁
      let η₂' := η₁ * b
      let η₃ := η₂ * b

      let δ := (d + η₃)^*
      let γ := δ * η₂
      let β := η₂' * δ
      let α := η₁ + β * η₂

      let m'' := Matrix.fromBlocks α β γ δ

      conice m'' |>.concrete
    | n'+1 =>
      let m' := nice m
      let a : Matrix (Fin n') (Fin n') α := m'.toBlocks₁₁
      let b := m'.toBlocks₁₂
      let c := m'.toBlocks₂₁
      let d := m'.toBlocks₂₂

      let η₁ := star_fin_old a
      let η₂ := c * η₁ |>.concrete
      let η₂' := η₁ * b |>.concrete
      let η₃ := η₂ * b |>.concrete

      let δ := (d + η₃)^* |>.concrete
      let γ := δ * η₂ |>.concrete
      let β := η₂' * δ |>.concrete
      let α := η₁ + β * η₂ |>.concrete

      let m'' := Matrix.fromBlocks α β γ δ

      -- conice m''
      conice m'' |>.concrete

  -- printprint f!"star_fin({n})" res
  res

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  letI : Inhabited α := ⟨0⟩
  -- timeitit f!"old[{n}]" (do return star_fin_old m)
  timeitit f!"new[{n}]" (do return star_fin' (.ofMatrix m) |>.asMatrix)

instance instStar
    {α : Type} [Semiring α] [WeightedNetKAT.Star α]
    [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [WeightedNetKAT.LawfulStar α]
    [MulLeftMono α]
    [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
    -- [∀ n', MulLeftMono (Matrix (Fin n') (Fin n') α)]
    -- [∀ n', MulRightMono (Matrix (Fin n') (Fin n') α)]
    {n : ℕ} :
    WeightedNetKAT.Star (Matrix (Fin n) (Fin n) α) where
  star := star_fin

def star_fin_lawful'
    {α : Type} [Semiring α] [WeightedNetKAT.Star α]
    [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [WeightedNetKAT.LawfulStar α]
    [MulLeftMono α]
    [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
    -- [∀ n', MulLeftMono (Matrix (Fin n') (Fin n') α)]
    -- [∀ n', MulRightMono (Matrix (Fin n') (Fin n') α)]
    {n : ℕ} :
    LawfulStar (Matrix (Fin n) (Fin n) α) := by
  sorry
  -- induction n with
  -- | zero => constructor; intro m; ext ⟨_, hi⟩; omega
  -- | succ n ih =>
  --   constructor; intro m
  --   have : ∀ m' : Matrix (Fin n) (Fin n) α, star_fin m' = m'^* := by intro m'; rfl
  --   rcases n with _ | _ | n
  --   · sorry
  --   · sorry
  --   · simp [instStar, star_fin]
  --     simp [this]
  --     set a := (nice m).toBlocks₁₁
  --     set b := (nice m).toBlocks₁₂
  --     set c := (nice m).toBlocks₂₁
  --     set d := (nice m).toBlocks₂₂
  --     -- simp [add_star]
  --     ext ⟨i, hi⟩ ⟨j, hj⟩
  --     simp [conice]
  --     split_ifs <;> subst_eqs
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry

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
  sorry
  -- induction n with
  -- | zero => ext ⟨_, hi⟩; omega
  -- | succ n ih =>
  --   rcases n with _ | _ | n
  --   · simp [star_fin]
  --     sorry
  --   · sorry
  --   · simp [star_fin]
  --     set M₁₁ := (nice m).toBlocks₁₁
  --     set M₁₂ := (nice m).toBlocks₁₂
  --     set M₂₂ := (nice m).toBlocks₂₂
  --     set M₂₁ := (nice m).toBlocks₂₁
  --     simp [add_star]
  --     simp [ih]
  --     simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
  --     simp [← ωSum_mul_right, ← ωSum_mul_left, ← Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
  --     simp [LawfulStar.star_eq_sum]
  --     simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
  --     simp [← ωSum_mul_right, ← ωSum_mul_left, ← Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib, add_mul, mul_add, Matrix.mul_add, Matrix.add_mul]
  --     ext ⟨i, hi⟩ ⟨j, hj⟩
  --     simp [conice]
  --     split_ifs <;> subst_eqs
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     · simp_all
  --       sorry
  --     -- sorry
  --     -- split_ifs <;> subst_eqs
  --     -- · simp [QQQ]
  --     -- · simp
  --     -- · simp
  --     -- · simp
  --     -- split_ifs
  --     -- · subst_eqs
  --     --   simp
  --     --   -- rw [LawfulStar.star_eq_sum]
  --     --   simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --     -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --     -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --     -- · simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --   -- fun_induction star_fin with
  --   -- | case1 => ext ⟨_, h⟩; omega
  --   -- | case2 n' m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂ m₁₃ m₁₄ ih =>
  --   --   simp [m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, m₁₀, m₁₁, m₁₂, m₁₃, m₁₄] at ih ⊢
  --   --   simp [ih]
  --   --   simp [← ωSum_mul_right, ← ωSum_mul_left, Matrix.mul_assoc, ← ωSum_add, left_distrib, right_distrib]
  --   --   ext ⟨i, hi⟩ ⟨j, hj⟩
  --   --   simp [Matrix.add_apply, conice, fromBlocks]
  --   --   split_ifs
  --   --   · subst_eqs
  --   --     simp_all [Matrix.add_apply]
  --   --   · simp
  --   --   · simp
  --   --   · simp

  --   -- sorry
  --   -- -- fun_induction star_fin
  --   -- -- next => sorry
  --   -- -- next => sorry

instance instListed {A : Type} [DecidableEq A] [Listed A] : WeightedNetKAT.Star (Matrix A A α) where
  star m :=
    let m' := Matrix.listedEquivNat m
    let m'' := star_fin m'
    Matrix.listedEquivNat.symm m'' |>.concrete

instance instListed' {n : ℕ} : WeightedNetKAT.Star (NMatrix n n α) where
  star m :=
    -- let m' := Matrix.listedEquivNat m
    star_fin' m
    -- Matrix.listedEquivNat.symm m'' |>.concrete

variable {𝒮 : Type} [Semiring 𝒮] [WeightedNetKAT.Star 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]
variable [LawfulStar 𝒮]
variable {X : Type} [Fintype X] [DecidableEq X] [Listed X]

instance : WeightedNetKAT.LawfulStar (Matrix X X 𝒮) where
  star_eq_sum m := by
    let m' := Matrix.listedEquivNat m
    convert congrArg Matrix.listedEquivNat.symm (star_fin_lawful m')
    · sorry
    · refine (Equiv.apply_eq_iff_eq_symm_apply listedEquivNat).mp ?_
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
