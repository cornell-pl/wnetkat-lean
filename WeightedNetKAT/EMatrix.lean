module

public import WeightedNetKAT.Listed
public import WeightedNetKAT.NMatrix

@[expose] public section

def EMatrix (m n α : Type*) [Listed m] [Listed n] := NMatrix (Listed.size m) (Listed.size n) α

namespace WeightingNotation

scoped notation "E𝒲[" x ", " y ", " s "]" => EMatrix x y s
scoped notation "N𝒲[" x ", " y ", " s "]" => NMatrix x y s

end WeightingNotation

open WeightingNotation

namespace EMatrix

variable {l m n w α : Type*} [Listed l] [Listed m] [Listed n] [Listed w]
variable {m' n' : Type*} [Listed m'] [Listed n']
variable {X X' : EMatrix m n α}
variable {Y Y' : EMatrix n l α}
variable {Z Z' : EMatrix l w α}

def getN (M : EMatrix m n α) (i : Fin (Listed.size m)) (j : Fin (Listed.size n)) : α := NMatrix.get M i j

def get (M : EMatrix m n α) (i : m) (j : n) : α :=
  let i' := Listed.encodeFin i
  let j' := Listed.encodeFin j
  M.getN i' j'

def asNMatrix (X : EMatrix m n α) : NMatrix (Listed.size m) (Listed.size n) α := X
def asNMatrix₂ (X : EMatrix m n (EMatrix m' n' α)) : NMatrix (Listed.size m) (Listed.size n) (NMatrix (Listed.size m') (Listed.size n') α) := X

theorem eq_of_asNMatrix (h : X.asNMatrix = X'.asNMatrix) : X = X' := h
theorem ext_get (h : ∀ i j, X.get i j = X'.get i j) : X = X' := by
  apply eq_of_asNMatrix
  ext i j
  specialize h (Listed.decodeFin i) (Listed.decodeFin j)
  simp [get] at h
  exact h

theorem get_inj : Function.Injective (get (m:=m) (n:=n) (α:=α)) := by
  intro M M' h
  apply ext_get (congrFun₂ h)

instance : FunLike (EMatrix m n α) m (n → α) where
  coe := get
  coe_injective' := get_inj

@[simp]
theorem get_eq_apply {i} : X.get i = X i := by rfl

@[grind =, simp]
theorem asNMatrix_apply {i j} : X.asNMatrix i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp [asNMatrix]
  simp only [DFunLike.coe, NMatrix.get, get, getN]
  simp only [NMatrix.data_getElem, Listed.decodeFin_encodeFin]

@[simp]
theorem getN_eq {i j} : X.getN i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  rw [← asNMatrix_apply]
  rfl

@[ext]
theorem ext (h : ∀ i j, X i j = X' i j) : X = X' := by
  apply eq_of_asNMatrix
  ext i j
  grind

def ofFn : (Fin (Listed.size m) → (Fin (Listed.size n)) → α) → EMatrix m n α := NMatrix.ofFn
def ofFnSlow (f : m → n → α) : EMatrix m n α :=
  NMatrix.ofFn fun i j ↦ f (Listed.decodeFin i) (Listed.decodeFin j)

def ofNMatrix (N : NMatrix (Listed.size m) (Listed.size n) α) : EMatrix m n α := N

@[simp, grind =]
theorem NMatrix_coe_apply {M : EMatrix m n α} (i : m) (j : n) :
      @DFunLike.coe (NMatrix (Listed.size m) (Listed.size n) α) (Fin (Listed.size m)) (fun _ ↦ Fin (Listed.size n) → α) inferInstance M (Listed.encodeFin i) (Listed.encodeFin j)
    = M i j := rfl
@[simp]
theorem NMatrix_ofFn_apply (i : m) (j : n) {f} :
      @DFunLike.coe E𝒲[m, n, α] m (fun _ ↦ n → α) instFunLikeForall (NMatrix.ofFn f) i j
    = f (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp only [DFunLike.coe, get, getN, NMatrix.get]
  simp only [NMatrix.data_getElem, NMatrix.ofFn_apply]

@[simp, grind =]
theorem apply_ofFnSlow : ofFnSlow X = X := by
  ext; simp [ofFnSlow]
@[simp, grind =]
theorem ofFnSlow_apply {f : m → n → α} {i} : ofFnSlow f i = f i := by
  ext; simp [ofFnSlow]
@[simp, grind =]
theorem ofFn_apply {f : Fin (Listed.size m) → Fin (Listed.size n) → α} {i j} :
    ofFn f i j = f (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp [ofFn]

def asMatrix (M : EMatrix m n α) : Matrix m n α := DFunLike.coe M
def ofMatrix (M : Matrix m n α) : EMatrix m n α := .ofFnSlow M

@[simp, grind =]
theorem ofMatrix_apply {f : m → n → α} {i} : EMatrix.ofMatrix f i = f i := by simp [ofMatrix]

@[simp, grind =]
theorem asMatrix_apply {f : EMatrix m n α} {i} : EMatrix.asMatrix f i = f i := by simp [asMatrix]
@[simp, grind =]
theorem asMatrix_apply₂ {f : EMatrix m n α} {i j} : EMatrix.asMatrix f i j = f i j := by simp [asMatrix]

@[simp, grind =] theorem asMatrix_ofMatrix : EMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind =] theorem ofMatrix_asMatrix {M : Matrix m n α} :
    (EMatrix.ofMatrix M).asMatrix = M := by ext; simp

def map {β: Type*} (f : α → β) (M : EMatrix m n α) : EMatrix m n β :=
  .ofFn fun i j ↦ f (M.getN i j)

def asMatrix₂ (M : EMatrix m n (EMatrix m' n' α)) : Matrix m n (Matrix m' n' α) := fun i j i' j' ↦ M i j i' j'
def ofMatrix₂ (M : Matrix m n (Matrix m' n' α)) : EMatrix m n (EMatrix m' n' α) := (EMatrix.ofFnSlow M).map .ofMatrix

@[simp, grind =] theorem asMatrix₂_ofMatrix₂ {X : EMatrix m n (EMatrix m' n' α)} : EMatrix.ofMatrix₂ X.asMatrix₂ = X := by
  simp [ofMatrix₂]
  ext i j i' j'
  simp [map, asMatrix₂, ofFnSlow]
@[simp, grind =] theorem ofMatrix₂_asMatrix₂ {M : Matrix m n (Matrix m' n' α)} :
    (EMatrix.ofMatrix₂ M).asMatrix₂ = M := by
  simp [ofMatrix₂]
  ext
  simp [map, asMatrix₂, ofFnSlow]

theorem eq_ofMatrix (h : X.asMatrix = X'.asMatrix) : X = X' := by
  ext i j; exact congrFun₂ h i j

instance [Zero α] [One α] : One (EMatrix n n α) := inferInstanceAs (One (NMatrix _ _ α))
instance [Zero α] : Zero (EMatrix m n α) := inferInstanceAs (Zero (NMatrix _ _ α))
instance [Add α] : Add (EMatrix m n α) := inferInstanceAs (Add (NMatrix _ _ α))
theorem add_def [Add α] : X + X' = X.asNMatrix + X'.asNMatrix := rfl
theorem one_def [Zero α] [One α] : (1 : EMatrix n n α) = (1 : EMatrix n n α).asNMatrix := rfl
theorem zero_def [Zero α] : (0 : EMatrix m n α) = (0 : EMatrix m n α).asNMatrix := rfl

theorem one_apply [DecidableEq n] [Zero α] [One α] {i j} : (1 : EMatrix n n α) i j = if i = j then 1 else 0 := by
  rw [one_def]
  simp [asNMatrix]
  convert NMatrix.one_apply
  simp

@[simp]
theorem zero_apply [Zero α] {i j} : (0 : EMatrix m n α) i j = 0 := by
  suffices (EMatrix.ofMatrix (0 : Matrix _ _ α)) i j = 0 by convert this
  simp

@[simp]
theorem zero_apply' [Zero α] {i j} : @OfNat.ofNat E𝒲[m, n, α] 0 Zero.toOfNat0 i j = 0 := by
  simp

@[simp]
theorem zero_asMatrix [Zero α] : EMatrix.asMatrix (0 : EMatrix m n α) = 0 := by
  ext; simp [asMatrix]

instance [Mul α] {X Y : Type*} [Listed X] [Listed Y] : HSMul α (EMatrix X Y α) (EMatrix X Y α) where
  hSMul s m := m.map (s * ·)

open scoped RightActions

instance [Mul α] {X Y : Type*} [Listed X] [Listed Y] : HSMul αᵐᵒᵖ (EMatrix X Y α) (EMatrix X Y α) where
  hSMul s m := m.map (· * s.unop)

@[simp]
theorem NMatrix_apply {M : 𝒲[Fin (Listed.size m), Fin (Listed.size n), α]} {i : m} {j : n} :
      @DFunLike.coe E𝒲[m, n, α] m (fun _ ↦ n → α) instFunLikeForall (NMatrix.ofMatrix M) i j
    = NMatrix.ofMatrix M (Listed.encodeFin i) (Listed.encodeFin j) := by
  rfl

@[simp]
theorem add_apply [Add α] {i j} : (X + X') i j = X i j + X' i j := by
  rw [add_def, NMatrix.add_def]; simp; rfl

@[simp] theorem asMatrix_add [Add α] : (X + X').asMatrix = X.asMatrix + X'.asMatrix := by
  ext; simp [asMatrix]

@[default_instance 100]
instance instHMul [Mul α] [AddCommMonoid α] : HMul (EMatrix l m α) (EMatrix m n α) (EMatrix l n α) :=
  inferInstanceAs (HMul (NMatrix _ _ α) (NMatrix _ _ α) (NMatrix _ _ α))
instance instMul [Mul α] [AddCommMonoid α] : Mul (EMatrix m m α) where
  mul a b := a * b


@[simp]
theorem hmul_eq_hmul [Mul α] [AddCommMonoid α] :
      @HMul.hMul (EMatrix m m α) (EMatrix m m α) (EMatrix m m α) instHMul
    = @HMul.hMul (EMatrix m m α) (EMatrix m m α) (EMatrix m m α) (@_root_.instHMul _ instMul) := rfl

instance [AddCommMonoid α] : AddCommMonoid (EMatrix m n α) :=
    inferInstanceAs (AddCommMonoid (NMatrix _ _ α))
@[default_instance 100]
instance instSemiring [Semiring α] : Semiring (EMatrix n n α) :=
    inferInstanceAs (Semiring (NMatrix _ _ α))

instance [OmegaCompletePartialOrder α] :
    OmegaCompletePartialOrder (EMatrix m n α) :=
  inferInstanceAs (OmegaCompletePartialOrder (NMatrix _ _ α))
instance [OmegaCompletePartialOrder α] [OrderBot α] :
    OrderBot (EMatrix m n α) :=
  inferInstanceAs (OrderBot (NMatrix _ _ α))

instance [AddCommMonoid α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] :
    IsPositiveOrderedAddMonoid E𝒲[m, n, α] :=
  inferInstanceAs (IsPositiveOrderedAddMonoid (NMatrix _ _ α))

theorem mul_def  [Mul α] [AddCommMonoid α] : X * Y = X.asNMatrix * Y.asNMatrix := by
  rfl

theorem mul_apply [Fintype n] [Mul α] [AddCommMonoid α] {a b} : (X * Y) a b = ∑ c, X a c * Y c b := by
  simp [mul_def, NMatrix.mul_def, NMatrix.ofMatrix, asNMatrix, Matrix.mul_apply]

theorem mul_assoc [NonUnitalSemiring α] : X * Y * Z = X * (Y * Z) := NMatrix.mul_assoc

-- theorem asMatrix_mul [Fintype n] [Mul α] [AddCommMonoid α] : (X * Y).asMatrix = X.asMatrix * Y.asMatrix := by simp [asMatrix]

section

@[simp]
theorem NMatrix.map_apply {m n : ℕ} {𝒮 𝒮' : Type*} {f : NMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    f.map g i j = g (f i j) := by
  simp
@[simp]
theorem NMatrix.ofFn_map {m n : ℕ} {𝒮 𝒮' : Type*} {f : Fin m → Fin n → 𝒮} {g : 𝒮 → 𝒮'} :
    (NMatrix.ofFn f).map g = NMatrix.ofFn (fun i j ↦ g (f i j)) := by
  ext
  simp
-- @[simp]
-- theorem ofFn_get {m n 𝒮 : Type*} [Listed m] [Listed n] {f : Fin (Listed.size m) → Fin (Listed.size n) → 𝒮} :
--     (ofFn f).get = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
--   ext; simp

@[simp]
theorem ofFn_asMatrix {m n 𝒮 : Type*} [Listed m] [Listed n] {f : Fin (Listed.size m) → Fin (Listed.size n) → 𝒮} :
    (ofFn f).asMatrix = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext; simp [asMatrix]
@[simp]
theorem map_apply {m n 𝒮 𝒮' : Type*} [Listed m] [Listed n] {f : EMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    f.map g i j = g (f i j) := by simp [map]
@[simp]
theorem map_asMatrix {m n 𝒮 𝒮' : Type*} [Listed m] [Listed n] {f : EMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    (f.map g).asMatrix i j = g (f.asMatrix i j) := by
  simp [map]

@[simp]
theorem ofMatrix₂_apply {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {M : 𝒲[m, n, 𝒲[m', n', 𝒮]]} {i j} :
    ofMatrix₂ M i j = ofMatrix (M i j) := by
  ext
  simp
  simp [ofMatrix₂, ofMatrix, map]
@[simp]
theorem toMatrix₂_ofMatrix₂ {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {M : E𝒲[m, n, E𝒲[m', n', 𝒮]]} :
    ofMatrix₂ (asMatrix₂ M) = M := by
  ext; simp

@[simp]
theorem ofMatrix_add {m n 𝒮 : Type*} [Listed m] [Listed n] [Add 𝒮]
    (a b : 𝒲[m, n, 𝒮]) :
    ofMatrix (a + b) = ofMatrix a + ofMatrix b := by
  ext; simp

@[simp]
theorem ofMatrix_sum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι} [DecidableEq ι]
    (f : ι → 𝒲[n, m, 𝒮]) :
    ofMatrix (∑ i ∈ S, f i) = ∑ i ∈ S, ofMatrix (f i) := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S h ih => simp_all


@[simp]
theorem ofMatrix_pow {m 𝒮 : Type*} [Listed m] [Semiring 𝒮] [DecidableEq m] [Fintype m]
    (M : 𝒲[m, m, 𝒮]) (i : ℕ) :
    ofMatrix (M ^ i) = (ofMatrix M)^i := by
  induction i with
  | zero =>
    simp
    ext i j
    simp [EMatrix.one_apply, Matrix.one_apply]
  | succ i ih =>
    simp [pow_succ, ← ih]
    ext a b
    simp [mul_apply, Matrix.mul_apply]

@[simp]
theorem sum_apply {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι}
    (f : ι → E𝒲[m, n, 𝒮]) {x y} :
    (∑ i ∈ S, f i) x y = ∑ i ∈ S, f i x y := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert x S h ih => simp_all

@[simp]
theorem asMatrix_sum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι}
    (f : ι → E𝒲[m, n, 𝒮]) :
    asMatrix (∑ i ∈ S, f i) = ∑ i ∈ S, asMatrix (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert x S h ih => simp_all

open OmegaCompletePartialOrder

@[simp]
theorem ωSum_apply {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → E𝒲[m, n, 𝒮]) {x y} :
    (ω∑ i, f i) x y = ω∑ i, f i x y := by
  simp only [ωSum, ωSup]
  unfold instOmegaCompletePartialOrder._aux_9
  simp only [NMatrix.ofMatrix, ωSup]
  unfold instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9
  simp only [ωSup]
  simp
  congr! 1
  ext k
  simp [Chain.map, OrderHom.comp]
  simp only [DFunLike.coe]
  simp
  induction k with
  | zero =>
    simp
  | succ k ih =>
    simp_all [Finset.sum_range_succ]
    congr!
    split <;> simp_all

@[simp]
theorem asMatrix_ωSum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → E𝒲[m, n, 𝒮]) :
    asMatrix (ω∑ i, f i) = ω∑ i, asMatrix (f i) := by
  ext i j
  simp only [asMatrix, ωSum, ωSup]
  unfold instOmegaCompletePartialOrder._aux_9
  simp only [NMatrix.ofMatrix, ωSup]
  unfold instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9
  simp only [ωSup]
  simp
  congr! 1
  ext k
  simp [Chain.map, OrderHom.comp]
  simp only [DFunLike.coe]
  simp
  induction k with
  | zero => simp
  | succ k ih =>
    simp_all [Finset.sum_range_succ]
    congr
    split <;> simp_all

@[simp]
theorem asMatrix_ωSum' {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → N𝒲[Listed.size m, Listed.size n, 𝒮]) :
    asMatrix (ω∑ i, f i : N𝒲[Listed.size m, Listed.size n, 𝒮]) = ω∑ i, asMatrix (f i) := asMatrix_ωSum f

-- @[simp]
-- theorem mul_simp {m n k 𝒮 : Type*} [Listed m] [Listed n] [Listed k] [Fintype n] [AddCommMonoid 𝒮] [Mul 𝒮]
--     (a : E𝒲[m, n, 𝒮]) (b : E𝒲[n, k, 𝒮]) :
--     a * b = ofMatrix (asMatrix a * asMatrix b) := by
--   ext; simp [asMatrix]
-- -- @[simp]
-- theorem NMatrix.mul_simp {m n k : ℕ} {𝒮 : Type*} [AddCommMonoid 𝒮] [Mul 𝒮]
--     (a : N𝒲[m, n, 𝒮]) (b : N𝒲[n, k, 𝒮]) :
--     a * b = NMatrix.ofMatrix (NMatrix.asMatrix a * NMatrix.asMatrix b) := by
--   ext; simp [NMatrix.asMatrix]

end

attribute [simp, grind =] get_eq_apply

end EMatrix
