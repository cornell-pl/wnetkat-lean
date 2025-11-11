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

variable {l k m m' n n' : ℕ} {α : Type*}
variable {X X' : NMatrix m n α}
variable {Y Y' : NMatrix n l α}
variable {Z Z' : NMatrix l k α}

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

def asMatrix (M : NMatrix m n α) : Matrix (Fin m) (Fin n) α := M.get
def ofMatrix (M : Matrix (Fin m) (Fin n) α) : NMatrix m n α := .ofFn M

theorem asMatrix_eq_get : X.asMatrix = X.get := rfl

theorem eq_of_asMatrix (h : X.asMatrix = X'.asMatrix) : X = X' := by
  ext i j; exact congrFun₂ h i j

section

variable (m₁₁ : NMatrix m n α) (m₁₂ : NMatrix m n' α) (m₂₁ : NMatrix m' n α) (m₂₂ : NMatrix m' n' α)

def fromBlocks : NMatrix (m + m') (n + n') α :=
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

notation "fromBlocks[" a ", " b ", " c ", " d "]" => fromBlocks a b c d

variable (M : NMatrix (m + m') (n + n') α)

def toBlocks₁₁ : NMatrix m n α :=
  .ofFn fun i j ↦ M.get ⟨i, by omega⟩ ⟨j, by omega⟩
def toBlocks₁₂ : NMatrix m n' α :=
  .ofFn fun i j ↦ M.get ⟨i, by omega⟩ ⟨n + j, by omega⟩
def toBlocks₂₁ : NMatrix m' n α :=
  .ofFn fun i j ↦ M.get ⟨m + i, by omega⟩ ⟨j, by omega⟩
def toBlocks₂₂ : NMatrix m' n' α :=
  .ofFn fun i j ↦ M.get ⟨m + i, by omega⟩ ⟨n + j, by omega⟩

@[simp]
theorem toBlocks₁₁_get {i j} : M.toBlocks₁₁.get i j = M.get ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  simp [toBlocks₁₁]
@[simp]
theorem toBlocks₁₂_get {i j} : M.toBlocks₁₂.get i j = M.get ⟨i, by omega⟩ ⟨n + j, by omega⟩ := by
  simp [toBlocks₁₂]
@[simp]
theorem toBlocks₂₁_get {i j} : M.toBlocks₂₁.get i j = M.get ⟨m + i, by omega⟩ ⟨j, by omega⟩ := by
  simp [toBlocks₂₁]
@[simp]
theorem toBlocks₂₂_get {i j} : M.toBlocks₂₂.get i j = M.get ⟨m + i, by omega⟩ ⟨n + j, by omega⟩ := by
  simp [toBlocks₂₂]

@[simp]
theorem fromBlocks_toBlocks₁₁ : fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂].toBlocks₁₁ = m₁₁ := by
  simp [fromBlocks, toBlocks₁₁]
@[simp]
theorem fromBlocks_toBlocks₁₂ : fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂].toBlocks₁₂ = m₁₂ := by
  simp [fromBlocks, toBlocks₁₂]
@[simp]
theorem fromBlocks_toBlocks₂₁ : fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂].toBlocks₂₁ = m₂₁ := by
  simp [fromBlocks, toBlocks₂₁]
@[simp]
theorem fromBlocks_toBlocks₂₂ : fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂].toBlocks₂₂ = m₂₂ := by
  simp [fromBlocks, toBlocks₂₂]

@[simp]
theorem fromBlocks_get {i j} :
      fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂].get i j
    = if hi : i < m then
        if hj : j < n then m₁₁.get ⟨i, by omega⟩ ⟨j, by omega⟩ else m₁₂.get ⟨i, by omega⟩ ⟨j - n, by omega⟩
      else
        if hj : j < n then m₂₁.get ⟨i - m, by omega⟩ ⟨j, by omega⟩ else m₂₂.get ⟨i - m, by omega⟩ ⟨j -n, by omega⟩ := by
  grind [fromBlocks]

@[simp]
theorem toBlocks_fromBlocks : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext; simp; split_ifs <;> congr <;> omega

end

def fill (a : α) : NMatrix m n α := .ofFn fun _ _ ↦ a

@[simp] def fill_get {a : α} {i : Fin m} {j : Fin n} : (fill a).get i j = a := by simp [fill]

@[simp, grind] theorem asMatrix_ofMatrix : NMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind] theorem ofMatrix_asMatrix {M : Matrix (Fin m) (Fin n) α} :
    (NMatrix.ofMatrix M).asMatrix = M := by
  simp [ofMatrix, asMatrix]

@[simp, grind]
theorem ofFn_asMatrix {f : Fin m → Fin n → α} : (ofFn f).asMatrix = f := ofFn_get
@[simp, grind]
theorem ofMatrix_get {f : Fin m → Fin n → α} : (NMatrix.ofMatrix f).get = f := ofFn_get

def map {β : Type*} (M : NMatrix m n α) (f : α → β) : NMatrix m n β :=
  ⟨M.data.map f⟩

@[simp, grind]
theorem map_get {β : Type*} (M : NMatrix m n α) (f : α → β) {i j} :
    (M.map f).get i j = f (M.get i j) := by
  simp [map, get]

instance [Zero α] [One α] : One (NMatrix n n α) := ⟨NMatrix.ofMatrix 1⟩
instance [Zero α] : Zero (NMatrix m n α) := ⟨NMatrix.ofMatrix 0⟩

@[simp, grind]
theorem zero_get [Zero α] {i j} : (0 : NMatrix m n α).get i j = 0 := by
  simp [OfNat.ofNat, Zero.zero]
@[simp, grind]
theorem one_get [Zero α] [One α] {i j} : (1 : NMatrix n n α).get i j = if i = j then 1 else 0 := by
  simp [OfNat.ofNat, One.one, Matrix.diagonal_apply]

instance [Add α] : Add (NMatrix m n α) where
  add a b := .ofMatrix (a.asMatrix + b.asMatrix)
instance [Mul α] [AddCommMonoid α] : HMul (NMatrix l m α) (NMatrix m n α) (NMatrix l n α) where
  hMul a b := .ofMatrix (a.asMatrix * b.asMatrix)
@[simp] instance [Mul α] [AddCommMonoid α] : Mul (NMatrix n n α) := ⟨HMul.hMul⟩

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

theorem mul_assoc [NonUnitalSemiring α] : X * Y * Z = X * (Y * Z) := by
  ext; simp [asMatrix_mul, Matrix.mul_assoc]

theorem add_assoc [AddSemigroup α] {X'' : NMatrix m n α} : X + X' + X'' = X + (X' + X'') := by
  ext; simp [_root_.add_assoc]

theorem add_comm [AddCommMonoid α] : X + X' = X' + X := by
  ext; simp [_root_.add_comm]

theorem add_mul [Semiring α] : (X + X') * Y = X * Y + X' * Y := by
  ext; simp only [mul_get, asMatrix_eq_get, add_get, Matrix.mul_apply, Pi.add_apply, right_distrib,
    Finset.sum_add_distrib]
theorem mul_add [Semiring α] : X * (Y + Y') = X * Y + X * Y' := by
  ext; simp only [mul_get, asMatrix_eq_get, add_get, Matrix.mul_apply, Pi.add_apply, left_distrib,
    Finset.sum_add_distrib]

@[simp]
theorem one_mul [Semiring α] : (1 : NMatrix m m α) * X = X := by
  ext; simp only [mul_get, asMatrix_eq_get, Matrix.mul_apply, one_get, ite_mul, _root_.one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
@[simp]
theorem mul_one [Semiring α] : X * (1 : NMatrix n n α) = X := by
  ext; simp only [mul_get, asMatrix_eq_get, Matrix.mul_apply, one_get, mul_ite, _root_.mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
@[simp]
theorem zero_mul [NonUnitalSemiring α] : (0 : NMatrix l m α) * X = 0 := by
  ext; simp only [mul_get, asMatrix_eq_get, Matrix.mul_apply, zero_get, MulZeroClass.zero_mul,
    Finset.sum_const_zero]
@[simp]
theorem mul_zero [NonUnitalSemiring α] : X * (0 : NMatrix n l α) = 0 := by
  ext; simp only [mul_get, asMatrix_eq_get, Matrix.mul_apply, zero_get, MulZeroClass.mul_zero,
    Finset.sum_const_zero]

@[simp]
theorem zero_add [NonUnitalSemiring α] : 0 + X = X := by
  ext; simp only [add_get, Pi.add_apply, zero_get, _root_.zero_add]
@[simp]
theorem add_zero [NonUnitalSemiring α] : X + 0 = X := by
  ext; simp only [add_get, Pi.add_apply, zero_get, _root_.add_zero]


#eval! (NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)) + NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)

instance {α : Type*} [Semiring α] : Semiring (NMatrix n n α) where
  add_assoc A B C := by ext; simp [add_assoc]
  zero_add A := by ext; simp
  add_zero A := by ext; simp
  nsmul n A := A.map (n * ·)
  nsmul_succ n A := by ext; simp [right_distrib]
  nsmul_zero A := by ext; simp
  add_comm A B := by ext; simp [add_comm]
  left_distrib A B C := by ext; simp [left_distrib, mul_get, asMatrix_eq_get]
  right_distrib A B C := by ext; simp [right_distrib, mul_get, asMatrix_eq_get]
  zero_mul A := by ext; simp only [instMulOfAddCommMonoid, zero_mul, zero_get]
  mul_zero A := by ext; simp only [instMulOfAddCommMonoid, mul_zero, zero_get]
  mul_assoc A B C := by ext; simp [mul_assoc]
  one_mul A := by ext; simp only [instMulOfAddCommMonoid, one_mul]
  mul_one A := by ext; simp only [instMulOfAddCommMonoid, mul_one]

section

variable {α : Type*}

variable [OmegaCompletePartialOrder α]

open OmegaCompletePartialOrder

instance : PartialOrder (NMatrix m n α) where
  le a b := a.asMatrix ≤ b.asMatrix
  le_refl a := le_refl a.asMatrix
  le_trans a b c hab hbc := le_trans hab hbc
  le_antisymm a b hab hba := NMatrix.ext_iff.mpr fun i ↦ congrFun (congrFun (le_antisymm hab hba) i)
instance : OmegaCompletePartialOrder (NMatrix m n α) where
  ωSup c := ωSup (c.map ⟨(·.asMatrix), fun _ _ a ↦ a⟩) |> .ofMatrix
  le_ωSup c i := by
    have := le_ωSup (c.map ⟨(·.asMatrix), fun _ _ a ↦ a⟩) i
    apply le_trans this
    simp only [ofMatrix_asMatrix, le_refl]
  ωSup_le c m i := by
    have := ωSup_le (c.map ⟨(·.asMatrix), fun _ _ a ↦ a⟩) m.asMatrix i
    apply le_trans _ this
    simp only [ofMatrix_asMatrix, le_refl]

variable [OrderBot α]

instance : OrderBot (NMatrix m n α) where
  bot := .ofMatrix ⊥
  bot_le x := by
    have := OrderBot.bot_le x.asMatrix
    apply le_trans _ this
    simp only [ofMatrix_asMatrix, le_refl]

variable [Semiring α] [IsPositiveOrderedAddMonoid α]

instance : IsPositiveOrderedAddMonoid (NMatrix n n α) where
  bot_eq_zero := by
    have := IsPositiveOrderedAddMonoid.bot_eq_zero (𝒮:=Matrix (Fin n) (Fin n) α)
    exact congrArg NMatrix.ofMatrix this
  add_le_add_left := by
    intro a b h c
    have := IsOrderedAddMonoid.add_le_add_left a.asMatrix b.asMatrix h c.asMatrix
    have : NMatrix.ofMatrix (c.asMatrix + a.asMatrix) ≤ NMatrix.ofMatrix (c.asMatrix + b.asMatrix) := by intro i j; simp; exact this i j
    exact this
  add_le_add_right := by
    intro a b h c
    have := IsOrderedAddMonoid.add_le_add_right a.asMatrix b.asMatrix h c.asMatrix
    have : NMatrix.ofMatrix (a.asMatrix + c.asMatrix) ≤ NMatrix.ofMatrix (b.asMatrix + c.asMatrix) := by intro i j; simp; exact this i j
    exact this

variable [MulLeftMono α]
instance : MulLeftMono (NMatrix n n α) where
  elim a b c h := by
    simp_all
    have h' : b.asMatrix ≤ c.asMatrix := h
    have h'' : a.asMatrix * b.asMatrix ≤ a.asMatrix * c.asMatrix := by apply mul_le_mul_left' h'
    have h'' : NMatrix.ofMatrix (a.asMatrix * b.asMatrix) ≤ NMatrix.ofMatrix (a.asMatrix * c.asMatrix) := by intro i j; simp [h'' i j]
    exact h''

end
section

variable {l m n o p q : ℕ}

variable (A : NMatrix n l α) (B : NMatrix n m α) (C : NMatrix o l α) (D : NMatrix o m α)
variable (A' : NMatrix l p α) (B' : NMatrix l q α) (C' : NMatrix m p α) (D' : NMatrix m q α)

theorem fromBlocks_mul [NonUnitalSemiring α] :
      fromBlocks A B C D * fromBlocks A' B' C' D'
    = fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  apply eq_of_asMatrix
  simp [asMatrix_mul]
  have := Matrix.fromBlocks_multiply A.asMatrix B.asMatrix C.asMatrix D.asMatrix A'.asMatrix B'.asMatrix C'.asMatrix D'.asMatrix
  ext ⟨i, hi₀⟩ ⟨j, hj₀⟩
  by_cases hi : i < n <;> by_cases hj : j < p
  · let i' : Fin n ⊕ Fin o := .inl ⟨i, by omega⟩
    let j' : Fin p ⊕ Fin q := .inl ⟨j, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inl ⟨i, by omega⟩
    let j' : Fin p ⊕ Fin q := .inr ⟨j - p, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inr ⟨i - n, by omega⟩
    let j' : Fin p ⊕ Fin q := .inl ⟨j, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inr ⟨i - n, by omega⟩
    let j' : Fin p ⊕ Fin q := .inr ⟨j - p, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, asMatrix_eq_get, hi, hj]

end

section

variable {l m n o p q : ℕ}

variable (A : NMatrix n l α) (B : NMatrix n m α) (C : NMatrix o l α) (D : NMatrix o m α)
variable (A' : NMatrix n l α) (B' : NMatrix n m α) (C' : NMatrix o l α) (D' : NMatrix o m α)

theorem fromBlocks_add [Add α] :
      fromBlocks[A, B, C, D] + fromBlocks[A', B', C', D']
    = fromBlocks[A + A', B + B', C + C', D + D'] := by
  ext; simp; grind

theorem fromBlocks_eq_one [Semiring α] :
      fromBlocks[(1 : NMatrix n n α), (0 : NMatrix n m α), (0 : NMatrix m n α), (1 : NMatrix m m α)]
    = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  grind [fromBlocks_get, one_get, zero_get]

@[simp]
theorem fromBlocks_le_iff [OmegaCompletePartialOrder α] :
    fromBlocks[A, B, C, D] ≤ fromBlocks[A', B', C', D'] ↔ (A ≤ A' ∧ B ≤ B' ∧ C ≤ C' ∧ D ≤ D') := by
  constructor
  · intro h
    split_ands
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i, by omega⟩ ⟨j, by omega⟩
      simp [asMatrix_eq_get, hi, hj] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i, by omega⟩ ⟨j + l, by omega⟩
      simp [asMatrix_eq_get, hi] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i + n, by omega⟩ ⟨j, by omega⟩
      simp [asMatrix_eq_get, hj] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i + n, by omega⟩ ⟨j + l, by omega⟩
      simp [asMatrix_eq_get] at h
      exact h
  · intro ⟨_, _, _, _⟩
    intro ⟨i, hi⟩ ⟨j, hj⟩
    simp [asMatrix_eq_get]
    split_ifs <;> apply_assumption

theorem fromBlocks_le [OmegaCompletePartialOrder α]
    (hA : A ≤ A')
    (hB : B ≤ B')
    (hC : C ≤ C')
    (hD : D ≤ D') :
    fromBlocks[A, B, C, D] ≤ fromBlocks[A', B', C', D'] := by
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp [asMatrix_eq_get]
  split_ifs <;> apply_assumption

end

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
class StarIter (α : Type) [One α] [Mul α] [Add α] [Star α] where
  star_iter : ∀ m : α, 1 + m * m^* = m^*

open OmegaCompletePartialOrder

def lawfulStarOf {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [MulLeftMono α]
    (h : ∀ m : α, m^* = 1 + m * m^*)
    (h' : ∀ (a c : α), 1 + c * a ≤ c → a^* ≤ c) :
    ∀ m : α, m^* = ω∑ n : ℕ, m^n := by
  intro m
  simp [ωSum_nat_eq_ωSup]
  apply le_antisymm
  · -- apply h'
    clear h'
    -- apply le_ωSup



    sorry
  · simp
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
      rw [h, add_comm]
      gcongr

def lawfulStarOf' {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [MulLeftMono α]
    (h : ∀ m : α, m^* = 1 + m * m^*)
    (h' : ∀ (a c : α), 1 + c * a ≤ c → a^* ≤ c) :
    LawfulStar α := ⟨lawfulStarOf h h'⟩

instance instUnitStar {α : Type} [Star α] : Star (Matrix Unit Unit α) where
  star m := fun α β ↦ (m α β)^*
-- instance : LawfulStar (Matrix Unit Unit 𝒮) where
--   star_eq_sum := sorry

variable {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] [LawfulStar α]
variable [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]

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

instance {m n : ℕ} : HMul α (NMatrix m n α) (NMatrix m n α) where
    hMul s M := M.map (fun x ↦ s * x)
instance {m n : ℕ} : HMul (NMatrix m n α) α (NMatrix m n α) where
    hMul M s := M.map (fun x ↦ x * s)

instance : WeightedNetKAT.Star (NMatrix 1 1 α) where
  star a := .fill (a.get 0 0)^*

instance {α : Type} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] : StarIter (NMatrix 1 1 α) where
  star_iter m := by
    simp [instStarNMatrixOfNatNat]
    nth_rw 2 [← StarIter.star_iter]
    ext ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ <;> try omega
    simp [NMatrix.fill, Matrix.mul_apply, NMatrix.asMatrix_eq_get]

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

theorem star_fin'_iter {α : Type} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : NMatrix n n α) :
    1 + M * star_fin' M = star_fin' M := by
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

open OmegaCompletePartialOrder

-- theorem star_fin'_eq_sum {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
--     [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [StarIter α] [MulLeftMono α]
--     {n : ℕ} (a : NMatrix n n α) :
--     star_fin' a = ω∑ i, a^i := by
--   apply le_antisymm
--   · simp [ωSum_nat_eq_ωSup]

--     sorry
--   · simp [ωSum_nat_eq_ωSup]
--     intro i
--     sorry

theorem star_fin'_least {α : Type} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [StarIter α] [MulLeftMono α]
    {n : ℕ} (M N : NMatrix n n α) (h : 1 + N * M ≤ N) :
    star_fin' M ≤ N := by
  induction n with
  | zero => sorry
  | succ n ih =>
    let a : NMatrix n n α := M.toBlocks₁₁
    let b := M.toBlocks₁₂
    let c := M.toBlocks₂₁
    let d := M.toBlocks₂₂

    let x : NMatrix n n α := N.toBlocks₁₁
    let y := N.toBlocks₁₂
    let z := N.toBlocks₂₁
    let w := N.toBlocks₂₂

    set a' := star_fin' a
    have ha'₀ : star_fin' a = a' := rfl
    have ha' : 1 + a * a' = a' := star_fin'_iter a
    have ha'' : 1 + a' * a = a' := sorry

    replace ih := ih a
    simp [ha'₀] at ih

    -- replace ih : 1 + a * a' = a' := ih _

    wlog hM : M = NMatrix.fromBlocks a b c d generalizing a b c d
    · absurd hM; simp [a, b, c, d]
    · wlog hN : N = NMatrix.fromBlocks x y z w generalizing x y z w
      · absurd hN; simp [x, y, z, w]
      · simp [hN, hM] at *
        rw [star_fin']
        simp [ha'₀]
        rw [← NMatrix.fromBlocks_eq_one] at h
        simp [NMatrix.fromBlocks_mul, NMatrix.fromBlocks_add, ← NMatrix.add_assoc] at h
        obtain ⟨h₁, h₂, h₃, h₄⟩ := h
        split_ands
        · apply le_trans _ h₁
          nth_rw 1 [← ha'']
          simp [NMatrix.add_assoc]

          sorry
        · sorry
        · sorry
        · sorry
  -- rw [← star_fin'_iter]
  -- apply le_trans _ h
  -- gcongr
  -- simp
  -- sorry

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  star_fin' (.ofMatrix m) |>.asMatrix

instance instStar
    {α : Type} [Semiring α] [WeightedNetKAT.Star α]
    [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [WeightedNetKAT.LawfulStar α]
    [MulLeftMono α]
    [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
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
  induction n with
  | zero => constructor; intro m; ext ⟨_, hi⟩; omega
  | succ n ih =>
    apply lawfulStarOf'
    · intro m
      simp [instStar]
      simp [star_fin, star_fin']
      sorry
    · sorry
  -- sorry
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
