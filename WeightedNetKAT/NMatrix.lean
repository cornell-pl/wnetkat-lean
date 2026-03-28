import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Ring.RingNF
import WeightedNetKAT.MatrixExt

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

@[inline, deprecated]
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

theorem ext_get (h : ∀ i j, X.get i j = X'.get i j) : X = X' := by
  cases X; cases X'
  congr
  simp_all [get]
  ext i hi
  specialize h (⟨i, hi⟩ : Fin _).divNat (⟨i, hi⟩ : Fin _).modNat
  simp_all [Nat.div_add_mod']

theorem get_inj : Function.Injective (get (m:=m) (n:=n) (α:=α)) := by
  rintro a b h; apply ext_get; intro i j; exact congrFun₂ h i j

instance : FunLike (NMatrix m n α) (Fin m) (Fin n → α) where
  coe := get
  coe_injective' := get_inj

theorem get_eq_apply {i} : X.get i = X i := by rfl

@[ext] theorem ext (h : ∀ i j, X i j = X' i j) : X = X' := ext_get h

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
  apply ext_get
  intro ⟨i, hi⟩ ⟨j, hj⟩
  rcases n with _ | n <;> rcases m with _ | m <;> try omega
  simp [ofFn, get]
  have : ¬n + 1 ≤ j := by omega
  simp [Nat.mod_eq_of_lt, hj]
  congr
  rw [Nat.add_div]
  · simp [Nat.mod_eq_of_lt, hj, this]
  · omega

@[simp, grind]
theorem ofFn_apply {f : Fin m → Fin n → α} {i} : ofFn f i = f i := by
  simp [DFunLike.coe]

@[simp, grind]
theorem apply_ofFn : ofFn X = X := by
  simp [DFunLike.coe]

def asMatrix (M : NMatrix m n α) : Matrix (Fin m) (Fin n) α := DFunLike.coe M
def ofMatrix (M : Matrix (Fin m) (Fin n) α) : NMatrix m n α := .ofFn M

theorem asMatrix_eq_apply : X.asMatrix = DFunLike.coe X := rfl
@[simp] theorem asMatrix_apply {i} : X.asMatrix i = X i := rfl
@[simp] theorem ofMatrix_apply {M : Matrix (Fin m) (Fin n) α} {i} : ofMatrix M i = M i := by
  simp [ofMatrix]

theorem eq_of_asMatrix (h : X.asMatrix = X'.asMatrix) : X = X' := by
  ext i j; exact congrFun₂ h i j

section

variable (m₁₁ : NMatrix m n α) (m₁₂ : NMatrix m n' α) (m₂₁ : NMatrix m' n α) (m₂₂ : NMatrix m' n' α)

def fromBlocks : NMatrix (m + m') (n + n') α :=
  .ofFn fun i j ↦
    if _ : i < m then
      if _ : j < n then
        m₁₁ ⟨i, by omega⟩ ⟨j, by omega⟩
      else
        m₁₂ ⟨i, by omega⟩ ⟨j - n, by omega⟩
    else
      if _ : j < n then
        m₂₁ ⟨i - m, by have := i.isLt; omega⟩ ⟨j, by omega⟩
      else
        m₂₂ ⟨i - m, by omega⟩ ⟨j - n, by omega⟩

notation "fromBlocks[" a ", " b ", " c ", " d "]" => fromBlocks a b c d

variable (M : NMatrix (m + m') (n + n') α)

def toBlocks₁₁ : NMatrix m n α :=
  .ofFn fun i j ↦ M ⟨i, by omega⟩ ⟨j, by omega⟩
def toBlocks₁₂ : NMatrix m n' α :=
  .ofFn fun i j ↦ M ⟨i, by omega⟩ ⟨n + j, by omega⟩
def toBlocks₂₁ : NMatrix m' n α :=
  .ofFn fun i j ↦ M ⟨m + i, by omega⟩ ⟨j, by omega⟩
def toBlocks₂₂ : NMatrix m' n' α :=
  .ofFn fun i j ↦ M ⟨m + i, by omega⟩ ⟨n + j, by omega⟩

@[simp]
theorem toBlocks₁₁_apply {i j} : M.toBlocks₁₁ i j = M ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  simp [toBlocks₁₁]
@[simp]
theorem toBlocks₁₂_apply {i j} : M.toBlocks₁₂ i j = M ⟨i, by omega⟩ ⟨n + j, by omega⟩ := by
  simp [toBlocks₁₂]
@[simp]
theorem toBlocks₂₁_apply {i j} : M.toBlocks₂₁ i j = M ⟨m + i, by omega⟩ ⟨j, by omega⟩ := by
  simp [toBlocks₂₁]
@[simp]
theorem toBlocks₂₂_apply {i j} : M.toBlocks₂₂ i j = M ⟨m + i, by omega⟩ ⟨n + j, by omega⟩ := by
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
      fromBlocks[m₁₁, m₁₂, m₂₁, m₂₂] i j
    = if hi : i < m then
        if hj : j < n then m₁₁ ⟨i, by omega⟩ ⟨j, by omega⟩ else m₁₂ ⟨i, by omega⟩ ⟨j - n, by omega⟩
      else
        if hj : j < n then m₂₁ ⟨i - m, by omega⟩ ⟨j, by omega⟩ else m₂₂ ⟨i - m, by omega⟩ ⟨j -n, by omega⟩ := by
  grind [fromBlocks]

@[simp]
theorem toBlocks_fromBlocks : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext; simp; split_ifs <;> congr! <;> omega

end

def fill (a : α) : NMatrix m n α := .ofFn fun _ _ ↦ a

@[simp] def fill_apply {a : α} {i : Fin m} {j : Fin n} : fill a i j = a := by simp [fill]

@[simp, grind] theorem asMatrix_ofMatrix : NMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind] theorem ofMatrix_asMatrix {M : Matrix (Fin m) (Fin n) α} :
    (NMatrix.ofMatrix M).asMatrix = M := by
  ext; simp

@[simp, grind]
theorem ofFn_asMatrix {f : Fin m → Fin n → α} : (ofFn f).asMatrix = f := ofFn_get

def map {β : Type*} (M : NMatrix m n α) (f : α → β) : NMatrix m n β :=
  ⟨M.data.map f⟩

@[simp, grind]
theorem map_apply {β : Type*} (M : NMatrix m n α) (f : α → β) {i j} :
    M.map f i j = f (M i j) := by
  simp [map, DFunLike.coe, get]

instance [Zero α] [One α] : One (NMatrix n n α) := ⟨NMatrix.ofMatrix 1⟩
instance [Zero α] : Zero (NMatrix m n α) := ⟨NMatrix.ofMatrix 0⟩

@[simp, grind]
theorem zero_apply [Zero α] {i j} : (0 : NMatrix m n α) i j = 0 := by
  simp [OfNat.ofNat, Zero.zero]
@[simp, grind]
theorem one_apply [Zero α] [One α] {i j} : (1 : NMatrix n n α) i j = if i = j then 1 else 0 := by
  simp [OfNat.ofNat, One.one, Matrix.diagonal_apply]

instance [Add α] : Add (NMatrix m n α) where
  add a b := .ofMatrix (a.asMatrix + b.asMatrix)
instance [Mul α] [AddCommMonoid α] : HMul (NMatrix l m α) (NMatrix m n α) (NMatrix l n α) where
  hMul a b := .ofMatrix (a.asMatrix * b.asMatrix)
@[simp] instance [Mul α] [AddCommMonoid α] : Mul (NMatrix n n α) := ⟨HMul.hMul⟩

@[simp]
theorem add_apply [Add α] {i} : (X + X') i = X i + X' i := by
  unfold instAdd
  rw [HAdd.hAdd, instHAdd]
  simp
  rfl

instance [AddCommMonoid α] : AddCommMonoid (NMatrix m n α) where
  add_assoc X Y Z := by ext; simp [add_assoc]
  add_comm X Y := by ext; simp [add_comm]
  zero_add X := by ext; simp
  add_zero X := by ext; simp
  nsmul a X := .ofMatrix (AddMonoid.nsmul a X.asMatrix : Matrix (Fin m) (Fin n) α)
  nsmul_zero X := by ext; simp
  nsmul_succ X Y := by ext; simp; apply AddMonoid.nsmul_succ

@[simp] theorem asMatrix_add [Add α] : (X + X').asMatrix = X.asMatrix + X'.asMatrix := by ext; simp

@[simp]
theorem mul_coe [Mul α] [AddCommMonoid α] : DFunLike.coe (X * Y) = X.asMatrix * Y.asMatrix := by
  ext; simp [HMul.hMul]

theorem asMatrix_mul [Mul α] [AddCommMonoid α] : (X * Y).asMatrix = X.asMatrix * Y.asMatrix := by simp [asMatrix]

theorem mul_assoc [NonUnitalSemiring α] : X * Y * Z = X * (Y * Z) := by
  ext; simp [asMatrix_mul, Matrix.mul_assoc]

theorem add_assoc [AddSemigroup α] {X'' : NMatrix m n α} : X + X' + X'' = X + (X' + X'') := by
  ext; simp [_root_.add_assoc]

theorem add_comm [AddCommMonoid α] : X + X' = X' + X := by
  ext; simp [_root_.add_comm]

theorem add_mul [Semiring α] : (X + X') * Y = X * Y + X' * Y := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, add_apply, Pi.add_apply, right_distrib,
    Finset.sum_add_distrib]
theorem mul_add [Semiring α] : X * (Y + Y') = X * Y + X * Y' := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, add_apply, Pi.add_apply, left_distrib,
    Finset.sum_add_distrib]

@[simp]
theorem one_mul [Semiring α] : (1 : NMatrix m m α) * X = X := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, one_apply, ite_mul, _root_.one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
@[simp]
theorem mul_one [Semiring α] : X * (1 : NMatrix n n α) = X := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, one_apply, mul_ite, _root_.mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
@[simp]
theorem zero_mul [NonUnitalSemiring α] : (0 : NMatrix l m α) * X = 0 := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, zero_apply, MulZeroClass.zero_mul,
    Finset.sum_const_zero]
@[simp]
theorem mul_zero [NonUnitalSemiring α] : X * (0 : NMatrix n l α) = 0 := by
  ext; simp only [mul_coe, Matrix.mul_apply, asMatrix_apply, zero_apply, MulZeroClass.mul_zero,
    Finset.sum_const_zero]

@[simp]
theorem zero_add [NonUnitalSemiring α] : 0 + X = X := by
  ext; simp only [_root_.zero_add]
@[simp]
theorem add_zero [NonUnitalSemiring α] : X + 0 = X := by
  ext; simp only [_root_.add_zero]


#eval! (NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)) + NMatrix.ofFn (m:=2) (n:=2) (α:=ℕ × ℕ) fun i j ↦ (i, j)

instance {α : Type*} [Semiring α] : Semiring (NMatrix n n α) where
  left_distrib A B C := by ext; simp [left_distrib, mul_coe]
  right_distrib A B C := by ext; simp [right_distrib, mul_coe]
  zero_mul A := by ext; simp only [instMulOfAddCommMonoid, zero_mul]
  mul_zero A := by ext; simp only [instMulOfAddCommMonoid, mul_zero]
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


instance [AddCommMonoid α] [IsPositiveOrderedAddMonoid α] : IsPositiveOrderedAddMonoid (NMatrix m n α) where
  bot_eq_zero := by
    have := IsPositiveOrderedAddMonoid.bot_eq_zero (𝒮:=Matrix (Fin m) (Fin n) α)
    exact congrArg NMatrix.ofMatrix this
  add_le_add_left := by
    intro a b h c
    have := IsOrderedAddMonoid.add_le_add_left a.asMatrix b.asMatrix h c.asMatrix
    have : NMatrix.ofMatrix (a.asMatrix + c.asMatrix) ≤ NMatrix.ofMatrix (b.asMatrix + c.asMatrix) := by intro i j; simp; exact this i j
    exact this
  add_le_add_right := by
    intro a b h c
    have := IsOrderedAddMonoid.add_le_add_right a.asMatrix b.asMatrix h c.asMatrix
    have : NMatrix.ofMatrix (c.asMatrix + a.asMatrix) ≤ NMatrix.ofMatrix (c.asMatrix + b.asMatrix) := by intro i j; simp; exact this i j
    exact this

variable [Semiring α] [IsPositiveOrderedAddMonoid α] [MulLeftMono α]
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
    · simp [Matrix.mul_apply, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inl ⟨i, by omega⟩
    let j' : Fin p ⊕ Fin q := .inr ⟨j - p, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inr ⟨i - n, by omega⟩
    let j' : Fin p ⊕ Fin q := .inl ⟨j, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, hi, hj]
  · let i' : Fin n ⊕ Fin o := .inr ⟨i - n, by omega⟩
    let j' : Fin p ⊕ Fin q := .inr ⟨j - p, by omega⟩
    replace this := congrFun₂ this i' j'
    simp [i', j'] at this
    convert this <;> clear this
    · simp [Matrix.mul_apply, hi, hj]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_add]
      congr! 2
      grind [Finset.mem_range]
    · simp [Matrix.mul_apply, hi, hj]

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
  grind [fromBlocks_get]

@[simp]
theorem fromBlocks_le_iff [OmegaCompletePartialOrder α] :
    fromBlocks[A, B, C, D] ≤ fromBlocks[A', B', C', D'] ↔ (A ≤ A' ∧ B ≤ B' ∧ C ≤ C' ∧ D ≤ D') := by
  constructor
  · intro h
    split_ands
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i, by omega⟩ ⟨j, by omega⟩
      simp [hi, hj] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i, by omega⟩ ⟨j + l, by omega⟩
      simp [hi] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i + n, by omega⟩ ⟨j, by omega⟩
      simp [hj] at h
      exact h
    · intro ⟨i, hi⟩ ⟨j, hj⟩
      replace h := h ⟨i + n, by omega⟩ ⟨j + l, by omega⟩
      simp at h
      exact h
  · intro ⟨_, _, _, _⟩
    intro ⟨i, hi⟩ ⟨j, hj⟩
    simp
    split_ifs <;> apply_assumption

theorem fromBlocks_le [OmegaCompletePartialOrder α]
    (hA : A ≤ A')
    (hB : B ≤ B')
    (hC : C ≤ C')
    (hD : D ≤ D') :
    fromBlocks[A, B, C, D] ≤ fromBlocks[A', B', C', D'] := by
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp
  split_ifs <;> apply_assumption

end

attribute [simp, grind] get_eq_apply

open OmegaCompletePartialOrder

@[simp]
theorem ωSum_apply {m n : ℕ} {𝒮 : Type*} [AddCommMonoid 𝒮] {ι : Type*} [Countable ι] [DecidableEq ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → NMatrix m n 𝒮) {x y} :
    (ω∑ i, f i) x y = ω∑ i, f i x y := by
  simp [ωSum, OmegaCompletePartialOrder.ωSup, NMatrix.ofMatrix]
  congr! 1
  ext k
  simp [Chain.map, OrderHom.comp]
  simp only [DFunLike.coe]
  induction k with
  | zero => simp
  | succ k ih =>
    simp_all [Finset.sum_range_succ]
    congr
    split <;> simp_all

end NMatrix
