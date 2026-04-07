import WeightedNetKAT.Listed
import WeightedNetKAT.NMatrix

def EMatrix (m n α : Type*) [Listed m] [Listed n] := NMatrix (Listed.size m) (Listed.size n) α

namespace WeightingNotation

scoped notation "E𝒲[" x ", " y ", " s "]" => EMatrix x y s
scoped notation "N𝒲[" x ", " y ", " s "]" => NMatrix x y s

end WeightingNotation

open WeightingNotation

namespace EMatrix

variable {l m n α : Type*} [lListed : Listed l] [mListed : Listed m] [nListed : Listed n]
variable {m' n' : Type*} [Listed m'] [Listed n']
variable {X X' : EMatrix m n α}
variable {Y Y' : EMatrix n l α}

def getN (M : EMatrix m n α) (i : Fin (Listed.size m)) (j : Fin (Listed.size n)) : α := NMatrix.get M i j

@[deprecated]
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

theorem get_eq_apply {i} : X.get i = X i := by rfl

@[simp]
theorem dfunlike_coe_NMatrix_ofFn {f : Fin (Listed.size m) → Fin (Listed.size n) → α} {i j} :
    DFunLike.coe (F:=EMatrix m n α) (NMatrix.ofFn f) i j = f (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp [DFunLike.coe]
  simp [get, getN]

@[simp]
theorem nmatrix_apply_eq_apply (i : Fin (Listed.size m)) (j : Fin (Listed.size n)) :
    @DFunLike.coe (NMatrix _ _ α) _ _ _ X i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp only [DFunLike.coe, get]
  simp
  rfl

@[simp]
theorem asNMatrix_apply {i j} : X.asNMatrix i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp [asNMatrix]

@[simp]
theorem getN_eq {i j} : X.getN i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp [getN]

@[ext]
theorem ext (h : ∀ i j, X.get i j = X'.get i j) : X = X' := by
  apply eq_of_asNMatrix
  ext i j
  specialize h (Listed.decodeFin i) (Listed.decodeFin j)
  simp [get] at h
  simp [asNMatrix]
  exact h

def ofFn (f : Fin (Listed.size m) → (Fin (Listed.size n)) → α) : EMatrix m n α :=
  NMatrix.ofFn fun i j ↦ f i j
def ofFnSlow (f : m → n → α) : EMatrix m n α :=
  NMatrix.ofFn fun i j ↦ f (Listed.decodeFin i) (Listed.decodeFin j)

@[simp, grind]
theorem ofFnSlow_get {f : m → n → α} : (ofFnSlow f).get = f := by
  ext i j; simp [ofFnSlow, get]

@[simp, grind]
theorem get_ofFnSlow : ofFnSlow X.get = X := by
  ext; simp [ofFnSlow, get]

@[simp, grind]
theorem ofFn_get {f : Fin (Listed.size m) → Fin (Listed.size n) → α} : (ofFn f).get = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext i j
  simp [ofFn, get]

@[simp, grind]
theorem get_ofFn : ofFn X.getN = X := by ext; simp [ofFn, get]

@[simp, grind]
theorem ofFnSlow_apply {f : m → n → α} {i} : ofFnSlow f i = f i := by
  ext i j
  simp [ofFnSlow]

@[simp, grind]
theorem ofFnSlow_apply₂ {f : m → n → α} {i j} : ofFnSlow f i j = f i j := by
  simp [ofFnSlow, DFunLike.coe]
  simp [get]

@[simp, grind]
theorem apply_ofFnSlow : ofFnSlow X = X := by
  ext; simp [ofFnSlow, get]

@[simp, grind]
theorem ofFn_apply {f : Fin (Listed.size m) → Fin (Listed.size n) → α} : (ofFn f) = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext i j
  simp [ofFn, DFunLike.coe]
  simp [get]

-- @[simp, grind]
-- theorem apply_ofFn : ofFn (DFunLike.coe X) = X := by simp [ofFn]

def asMatrix (M : EMatrix m n α) : Matrix m n α := M.get
def ofMatrix (M : Matrix m n α) : EMatrix m n α := .ofFnSlow M

@[simp, grind]
theorem ofFnSlow_asMatrix {f : m → n → α} : (ofFnSlow f).asMatrix = f := ofFnSlow_get
@[simp, grind]
theorem ofMatrix_get {f : m → n → α} : (EMatrix.ofMatrix f).get = f := ofFnSlow_get
@[simp, grind]
theorem ofMatrix_apply {f : m → n → α} {i} : EMatrix.ofMatrix f i = f i := by simp [ofMatrix]
@[simp, grind]
theorem ofMatrix_apply₂ {f : m → n → α} {i j} : EMatrix.ofMatrix f i j = f i j := by simp [ofMatrix]

@[simp, grind]
theorem asMatrix_apply {f : EMatrix m n α} {i} : EMatrix.asMatrix f i = f i := by simp [asMatrix]; rfl
@[simp, grind]
theorem asMatrix_apply₂ {f : EMatrix m n α} {i j} : EMatrix.asMatrix f i j = f i j := by simp [asMatrix]; rfl

@[simp, grind] theorem asMatrix_ofMatrix : EMatrix.ofMatrix X.asMatrix = X := by
  simp [ofMatrix, asMatrix]
@[simp, grind] theorem ofMatrix_asMatrix {M : Matrix m n α} :
    (EMatrix.ofMatrix M).asMatrix = M := by
  simp [ofMatrix, asMatrix]

def map {β: Type*} (f : α → β) (M : EMatrix m n α) : EMatrix m n β :=
  .ofFn fun i j ↦ f (M.getN i j)

def asNatMatrix (X : EMatrix m n α) : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) α :=
  NMatrix.get X
def ofNatMatrix (X : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) α) : EMatrix m n α :=
  NMatrix.ofFn X

@[simp]
theorem asNatMatrix_apply {i j} :
    asNatMatrix X i j = X (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp [asNatMatrix]
@[simp]
theorem ofNatMatrix_apply {X : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) α} {i j} :
    ofNatMatrix X i j = X (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp [ofNatMatrix]

def asMatrix₂ (M : EMatrix m n (EMatrix m' n' α)) : Matrix m n (Matrix m' n' α) := fun i j i' j' ↦ (M.get i j).get i' j'
def ofMatrix₂ (M : Matrix m n (Matrix m' n' α)) : EMatrix m n (EMatrix m' n' α) := (EMatrix.ofFnSlow M).map .ofMatrix

def asNatMatrix₂ (M : EMatrix m n (EMatrix m' n' α)) :
    Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) (Matrix (Fin (Listed.size m')) (Fin (Listed.size n')) α) :=
  fun i j i' j' ↦ NMatrix.get (NMatrix.get M i j) i' j'
def ofNatMatrix₂ (M : Matrix (Fin (Listed.size m)) (Fin (Listed.size n)) (Matrix (Fin (Listed.size m')) (Fin (Listed.size n')) α)) :
    EMatrix m n (EMatrix m' n' α) := (NMatrix.ofFn M).map .ofNatMatrix

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

instance [Zero α] [One α] : One (EMatrix n n α) := inferInstanceAs (One (NMatrix _ _ α))
instance [Zero α] : Zero (EMatrix m n α) := inferInstanceAs (Zero (NMatrix _ _ α))
instance [Add α] : Add (EMatrix m n α) := inferInstanceAs (Add (NMatrix _ _ α))
theorem add_def [Add α] : X + X' = X.asNMatrix + X'.asNMatrix := rfl
theorem one_def [Zero α] [One α] : (1 : EMatrix n n α) = (1 : EMatrix n n α).asNMatrix := rfl
theorem zero_def [Zero α] : (0 : EMatrix m n α) = (0 : EMatrix m n α).asNMatrix := rfl

@[simp]
theorem zero_get [Zero α] : (0 : EMatrix m n α).get = 0 := by
  rw [zero_def]
  ext i j
  exact NMatrix.zero_apply
@[simp]
theorem zero_apply [Zero α] {i j} : (0 : EMatrix m n α) i j = 0 := by
  suffices (EMatrix.ofMatrix (0 : Matrix _ _ α)).get i j = 0 by convert this
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
theorem add_get [Add α] : (X + X').get = X.get + X'.get := by
  rw [add_def, NMatrix.add_def]; ext; simp [get]; rfl

@[simp]
theorem add_apply [Add α] {i j} : (X + X') i j = X i j + X' i j := by
  rw [add_def, NMatrix.add_def]; simp; rfl

@[simp] theorem asMatrix_add [Add α] : (X + X').asMatrix = X.asMatrix + X'.asMatrix := by
  simp [asMatrix]; rfl

@[default_instance 100]
instance instHMul [Mul α] [AddCommMonoid α] : HMul (EMatrix l m α) (EMatrix m n α) (EMatrix l n α) :=
  inferInstanceAs (HMul (NMatrix _ _ α) (NMatrix _ _ α) (NMatrix _ _ α))
instance instMul [Mul α] [AddCommMonoid α] : Mul (EMatrix m m α) :=
  inferInstanceAs (Mul (NMatrix _ _ α))


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

theorem mul_def [Fintype n] [Mul α] [AddCommMonoid α] : X * Y = X.asNMatrix * Y.asNMatrix := by
  rfl

@[simp]
theorem mul_get [Fintype n] [Mul α] [AddCommMonoid α] : (X * Y).get = X.asMatrix * Y.asMatrix := by
  ext
  simp [mul_def, NMatrix.hmul_def, NMatrix.ofMatrix, asNMatrix, asMatrix, get, Matrix.mul_apply]

@[simp]
theorem mul_apply [Fintype n] [Mul α] [AddCommMonoid α] {a b} : (X * Y) a b = (X.asMatrix * Y.asMatrix) a b := by
  simp [mul_def, NMatrix.hmul_def, NMatrix.ofMatrix, asNMatrix, asMatrix, get, Matrix.mul_apply]
@[simp]
theorem mul'_apply [Fintype m] [Mul α] [AddCommMonoid α] {A B : EMatrix m m α} {a b} :
    (_root_.instHMul.hMul A B) a b = (A.asMatrix * B.asMatrix) a b := by
  conv => left; simp [HMul.hMul, Mul.mul, instMul._aux_1]
  simp [Matrix.mul_apply']
  simp [dotProduct]

theorem asMatrix_mul [Fintype n] [Mul α] [AddCommMonoid α] : (X * Y).asMatrix = X.asMatrix * Y.asMatrix := by simp [asMatrix]

instance [Zero α] [One α] [DecidableEq n] : One (EMatrix n n α) := ⟨EMatrix.ofMatrix 1⟩

section

@[simp]
theorem NMatrix.map_get {m n : ℕ} {𝒮 𝒮' : Type*} {f : NMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    (f.map g).get i j = g (f.get i j) := by
  simp [NMatrix.map, NMatrix.get]
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
theorem get_eq_asMatrix {m n 𝒮 : Type*} [Listed m] [Listed n] {A : EMatrix m n 𝒮} :
    A.get = A.asMatrix := by
  ext; rfl
-- @[simp]
-- theorem ofFnSlow_get {m n 𝒮 : Type*} [Listed m] [Listed n] {f : m → n → 𝒮} :
--     (ofFnSlow f).get = f := by
--   ext; simp
@[simp]
theorem ofFnSlow_NMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n] {f : m → n → 𝒮} :
    NMatrix.get (ofFnSlow f) = fun i j ↦ f (Listed.decodeFin i) (Listed.decodeFin j) := by
  ext; simp [ofFnSlow]
@[simp]
theorem ofFn_NMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n] {f : Fin (Listed.size m) → Fin (Listed.size n) → 𝒮} :
    NMatrix.get (ofFn f) = f := by
  ext; simp [ofFn]
@[simp]
theorem ofFn_asMatrix {m n 𝒮 : Type*} [Listed m] [Listed n] {f : Fin (Listed.size m) → Fin (Listed.size n) → 𝒮} :
    (ofFn f).asMatrix = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext; simp [asMatrix]
@[simp]
theorem NMatrix.ofFn_EMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n] {f : Fin (Listed.size m) → Fin (Listed.size n) → 𝒮} :
    get (NMatrix.ofFn f) = fun i j ↦ f (Listed.encodeFin i) (Listed.encodeFin j) := by
  ext; simp [get]
@[simp]
theorem map_get {m n 𝒮 𝒮' : Type*} [Listed m] [Listed n] {f : EMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    (f.map g).get i j = g (f.get i j) := by
  simp [map]
  rfl
@[simp]
theorem map_apply {m n 𝒮 𝒮' : Type*} [Listed m] [Listed n] {f : EMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    f.map g i j = g (f i j) := by
  simp [DFunLike.coe]
@[simp]
theorem map_asMatrix {m n 𝒮 𝒮' : Type*} [Listed m] [Listed n] {f : EMatrix m n 𝒮} {g : 𝒮 → 𝒮'} {i j} :
    (f.map g).asMatrix i j = g (f.asMatrix i j) := by
  simp [map]
@[simp]
theorem asMatrix₂_apply {m m' n n' 𝒮 : Type*} [Listed m] [Listed m'] [Listed n] [Listed n']
    {m : EMatrix m n (EMatrix m' n' 𝒮)} {i} {j} {x} {y} :
    m.asMatrix₂ i j x y = (m.get i j).get x y := rfl
@[simp]
theorem ofNatMatrix_asMatrix {m n 𝒮 : Type*} [Listed m] [Listed n]
    {m : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]} {i j} :
    (ofNatMatrix m).asMatrix i j = m (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp [ofNatMatrix, asMatrix]

@[simp]
theorem ofNatMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n]
    {m : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]} {i j} :
    (ofNatMatrix m).get i j = m (Listed.encodeFin i) (Listed.encodeFin j) := by
  simp [ofNatMatrix]
@[simp]
theorem ofNatMatrix₂_get {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {m : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒲[Fin (Listed.size m'), Fin (Listed.size n'), 𝒮]]} {i j} :
    (ofNatMatrix₂ m).get i j = ofNatMatrix (m (Listed.encodeFin i) (Listed.encodeFin j)) := by
  ext
  simp
  simp [ofNatMatrix₂, ofNatMatrix]
@[simp]
theorem asNatMatrix₂_apply {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {m : E𝒲[m, n, E𝒲[m', n', 𝒮]]} {i j} :
    (asNatMatrix₂ m) i j = asNatMatrix (m (Listed.decodeFin i) (Listed.decodeFin j)) := by
  ext
  simp only [asNatMatrix, DFunLike.coe, get, Listed.decodeFin_encodeFin]
  simp only [NMatrix.get_eq_apply]
  rfl

-- @[simp]
-- theorem ofMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n]
--     {m : 𝒲[m, n, 𝒮]} {i j} :
--     (ofMatrix m).get i j = m i j := by
--   simp [ofMatrix]
@[simp]
theorem ofMatrix₂_get {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {m : 𝒲[m, n, 𝒲[m', n', 𝒮]]} {i j} :
    (ofMatrix₂ m).get i j = ofMatrix (m i j) := by
  ext
  simp
  simp [ofMatrix₂, ofMatrix, map]
@[simp]
theorem ofMatrix₂_apply {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {m : 𝒲[m, n, 𝒲[m', n', 𝒮]]} {i j} :
    ofMatrix₂ m i j = ofMatrix (m i j) := by
  ext
  simp
  simp [ofMatrix₂, ofMatrix, map]
-- @[simp]
-- theorem ofMatrix₂_asMatrix₂ {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
--     {m : 𝒲[m, n, 𝒲[m', n', 𝒮]]} :
--     (ofMatrix₂ m).asMatrix₂ = m := by
--   ext; simp
@[simp]
theorem toMatrix₂_ofMatrix₂ {m m' n n' 𝒮 : Type*} [Listed m] [Listed n] [Listed m'] [Listed n']
    {m : E𝒲[m, n, E𝒲[m', n', 𝒮]]} :
    ofMatrix₂ (asMatrix₂ m) = m := by
  ext; simp
@[simp]
theorem NMatrix_get {m n 𝒮 : Type*} [Listed m] [Listed n]
    {m : E𝒲[m, n, 𝒮]} {i j} :
    NMatrix.get m i j = m.get (Listed.decodeFin i) (Listed.decodeFin j) := by
  simp [get]

@[simp]
theorem ofNatMatrix_add {m n 𝒮 : Type*} [Listed m] [Listed n] [Add 𝒮]
    (a b : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]) :
    ofNatMatrix (a + b) = ofNatMatrix a + ofNatMatrix b := by
  ext; simp

@[simp]
theorem ofMatrix_add {m n 𝒮 : Type*} [Listed m] [Listed n] [Add 𝒮]
    (a b : 𝒲[m, n, 𝒮]) :
    ofMatrix (a + b) = ofMatrix a + ofMatrix b := by
  ext; simp

theorem sized_eq_of {m n 𝒮 : Type*} [Listed m] [Listed n] [Add 𝒮]
    (a : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]) (b : 𝒲[m, n, 𝒮]) {i j}
    (h : (ofNatMatrix a).get i j = (ofMatrix b).get i j) :
    a (Listed.encodeFin i) (Listed.encodeFin j) = b i j := by
  convert h <;> simp

@[simp]
theorem ofNatMatrix_sum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι} [DecidableEq ι]
    (f : ι → 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]) :
    ofNatMatrix (∑ i ∈ S, f i) = ∑ i ∈ S, ofNatMatrix (f i) := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S h ih => simp_all

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
    simp [get]
    show _ = (1 : NMatrix _ _ 𝒮) (Listed.encodeFin i) (Listed.encodeFin j)
    simp
    rfl
  | succ i ih =>
    simp [pow_succ, ← ih]
    ext a b
    simp only [get, getN_eq, Listed.encodeFin_decodeFin, ofMatrix_apply₂, Matrix.mul_apply,
      mul'_apply, ofMatrix_asMatrix]

@[simp]
theorem sum_apply {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι} [DecidableEq ι]
    (f : ι → E𝒲[m, n, 𝒮]) {x y} :
    (∑ i ∈ S, f i) x y = ∑ i ∈ S, f i x y := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S h ih => simp_all

@[simp]
theorem asMatrix_sum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} {S : Finset ι} [DecidableEq ι]
    (f : ι → E𝒲[m, n, 𝒮]) :
    asMatrix (∑ i ∈ S, f i) = ∑ i ∈ S, asMatrix (f i) := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S h ih => simp_all

open OmegaCompletePartialOrder

@[simp]
theorem ωSum_apply {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι] [DecidableEq ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → E𝒲[m, n, 𝒮]) {x y} :
    (ω∑ i, f i) x y = ω∑ i, f i x y := by
  simp only [ωSum, ωSup]
  unfold instOmegaCompletePartialOrder._aux_9
  simp only [NMatrix.ofMatrix, ωSup, dfunlike_coe_NMatrix_ofFn]
  unfold instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9
  simp only [ωSup]
  congr! 1
  ext k
  simp [Chain.map, OrderHom.comp]
  simp [DFunLike.coe]
  induction k with
  | zero => simp
  | succ k ih =>
    simp_all [Finset.sum_range_succ]
    congr
    split <;> simp_all

@[simp]
theorem asMatrix_ωSum {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι] [DecidableEq ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → E𝒲[m, n, 𝒮]) :
    asMatrix (ω∑ i, f i) = ω∑ i, asMatrix (f i) := by
  ext i j
  simp only [asMatrix, ωSum, ωSup]
  unfold instOmegaCompletePartialOrder._aux_9
  simp only [NMatrix.ofMatrix, ωSup, NMatrix.ofFn_EMatrix_get]
  unfold instOmegaCompletePartialOrderMatrix_weightedNetKAT._aux_9
  simp only [ωSup]
  congr! 1
  ext k
  simp [Chain.map, OrderHom.comp]
  simp [DFunLike.coe]
  induction k with
  | zero => simp
  | succ k ih =>
    simp_all [Finset.sum_range_succ]
    congr
    split <;> simp_all

@[simp]
theorem asMatrix_ωSum' {m n 𝒮 : Type*} [Listed m] [Listed n] [AddCommMonoid 𝒮] {ι : Type*} [Countable ι] [DecidableEq ι]
    [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
    (f : ι → N𝒲[Listed.size m, Listed.size n, 𝒮]) :
    asMatrix (ω∑ i, f i : N𝒲[Listed.size m, Listed.size n, 𝒮]) = ω∑ i, asMatrix (f i) := asMatrix_ωSum f

@[simp]
theorem ofNatMatrix_mul {m n k 𝒮 : Type*} [Listed m] [Listed n] [Listed k] [Fintype n] [AddCommMonoid 𝒮] [Mul 𝒮]
    (a : 𝒲[Fin (Listed.size m), Fin (Listed.size n), 𝒮]) (b : 𝒲[Fin (Listed.size n), Fin (Listed.size k), 𝒮]) :
    ofNatMatrix (a * b) = ofNatMatrix a * ofNatMatrix b := by
  ext; simp [ofNatMatrix, Matrix.mul_apply, asMatrix]

@[simp]
theorem asNatMatrix_ofMatrix_mul {m n k 𝒮 : Type*} [Listed m] [Listed n] [Listed k] [Fintype n] [AddCommMonoid 𝒮] [Mul 𝒮]
    (a : 𝒲[m, n, 𝒮]) (b : 𝒲[n, k, 𝒮]) :
    (ofMatrix a).asNatMatrix * (ofMatrix b).asNatMatrix = fun i j ↦ (a * b) (Listed.decodeFin i) (Listed.decodeFin j) := by
  ext
  simp [Matrix.mul_apply]

-- @[simp]
-- theorem asMatrix_mul {m n k 𝒮 : Type*} [Listed m] [Listed n] [Listed k] [Fintype n] [AddCommMonoid 𝒮] [Mul 𝒮]
--     (a : E𝒲[m, n, 𝒮]) (b : E𝒲[n, k, 𝒮]) :
--     asMatrix (a * b) = asMatrix a * asMatrix b := by
--   ext; simp [asMatrix]

@[simp]
theorem mul_simp {m n k 𝒮 : Type*} [Listed m] [Listed n] [Listed k] [Fintype n] [AddCommMonoid 𝒮] [Mul 𝒮]
    (a : E𝒲[m, n, 𝒮]) (b : E𝒲[n, k, 𝒮]) :
    a * b = ofMatrix (asMatrix a * asMatrix b) := by
  ext; simp [asMatrix]
-- @[simp]
theorem NMatrix.mul_simp {m n k : ℕ} {𝒮 : Type*} [AddCommMonoid 𝒮] [Mul 𝒮]
    (a : N𝒲[m, n, 𝒮]) (b : N𝒲[n, k, 𝒮]) :
    a * b = NMatrix.ofMatrix (NMatrix.asMatrix a * NMatrix.asMatrix b) := by
  ext; simp [NMatrix.asMatrix]

@[simp]
theorem ofMatrix_ofNatMatrix_asNatMatrix {m n 𝒮 : Type*} [Listed m] [Listed n] (a : 𝒲[m, n, 𝒮]) :
    ofNatMatrix (ofMatrix a).asNatMatrix = ofMatrix a := by
  ext; simp

end

attribute [simp, grind =] get_eq_apply

end EMatrix
