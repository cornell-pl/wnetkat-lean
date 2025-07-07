import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Basic

def Tropical (α : Type*) := OrderDual α

attribute [local simp] wLe WeightedSemiring.ofSemiring

@[simp] instance : LinearOrder (Tropical ℕ∞) := inferInstanceAs (LinearOrder (OrderDual ℕ∞))
@[simp] instance : OrderTop (Tropical ℕ∞) := inferInstanceAs (OrderTop (OrderDual ℕ∞))
@[simp] instance : OrderBot (Tropical ℕ∞) := inferInstanceAs (OrderBot (OrderDual ℕ∞))

@[simp] instance : Zero (Tropical ℕ∞) := inferInstanceAs (Zero ℕ∞)
@[simp] instance : Add (Tropical ℕ∞) := inferInstanceAs (Add ℕ∞)

@[simp] instance : WeightedAdd (Tropical ℕ∞) := ⟨@min ℕ∞ _⟩
@[simp] instance : WeightedMul (Tropical ℕ∞) := ⟨(· + ·)⟩
@[simp] instance : WeightedZero (Tropical ℕ∞) := ⟨@Top.top ℕ∞ _⟩
@[simp] instance : WeightedOne (Tropical ℕ∞) := ⟨@Zero.zero ℕ∞ _⟩

instance : AddCommMonoid (Tropical ℕ∞) := inferInstanceAs (AddCommMonoid (OrderDual ℕ∞))
instance : IsOrderedAddMonoid (Tropical ℕ∞) := inferInstanceAs (IsOrderedAddMonoid (OrderDual ℕ∞))

instance : CovariantClass ℕ∞ ℕ∞ (Function.swap (· + ·)) (· ≥ ·) := ⟨by
  intro x y z h n h'
  simp_all [Function.swap]
  have hy : y ≠ ⊤ := by
    contrapose! h'
    subst_eqs
    simp_all
    exact not_eq_of_beq_eq_false rfl
  have hx : x ≠ ⊤ := by
    contrapose! h'
    subst_eqs
    simp_all
    exact not_eq_of_beq_eq_false rfl
  have hz : z ≠ ⊤ := ne_top_of_le_ne_top hy h
  if hn : n = 0 then subst_eqs; simp_all else
  have := (ENat.toNat_eq_iff hn).mpr h'
  subst_eqs
  symm at h'
  have : z + x < ⊤ := ENat.add_lt_top.mpr ⟨hz.lt_top, hx.lt_top⟩
  use (z + x).lift this
  simp_all
  constructor
  · rw [ENat.coe_lift, ENat.coe_lift]
  · rw [ENat.toNat_add hy hx]
    gcongr
    · simp_all; convert h; exact ENat.coe_toNat hy
    · refine ENat.lift_le_iff.mpr <| le_of_eq (ENat.coe_toNat hx).symm⟩
instance : CovariantClass (Tropical ℕ∞) (Tropical ℕ∞) (Function.swap (· + ·)) (· ≤ ·) :=
  inferInstanceAs (CovariantClass ℕ∞ ℕ∞ (Function.swap (· + ·)) (· ≥ ·))

instance : CovariantClass ℕ∞ ℕ∞ (· + ·) (· ≥ ·) := ⟨by
  simp [add_comm]
  conv =>
    arg 3
    ext x y
    rw [add_comm]
  exact CovariantClass.elim⟩
instance : CovariantClass (Tropical ℕ∞) (Tropical ℕ∞) (· + ·) (· ≤ ·) :=
  inferInstanceAs (CovariantClass ℕ∞ ℕ∞ (· + ·) (· ≥ ·))

@[simp]
theorem ashdjasjhd :
  @Bot.bot (Tropical ℕ∞) (inferInstanceAs (OrderBot ℕ∞ᵒᵈ)).toBot =
  @Top.top ℕ∞ _ := by rfl

@[simp]
instance : WeightedSemiring (Tropical ℕ∞) where
  wAdd_assoc := max_assoc
  wZero_add := by simp
  add_wZero := by simp
  wNsmul n x := if n = 0 then ⊥ else x
  wNsmul_wZero := by simp
  wNsmul_succ _ _ := by
    simp; split_ifs
    · exact (@max_eq_left_iff ℕ∞ _ _ _).mp rfl
    · exact (@Set.Iio_subset_Iio_iff ℕ∞ _ _).mp fun ⦃a⦄ a ↦ a
  wAdd_comm := max_comm
  left_distrib := add_max
  right_distrib := max_add
  wZero_mul _ := by rfl
  mul_wZero _ := by simp; rw [add_comm]; rfl
  mul_assoc := add_assoc
  wOne_mul := zero_add
  mul_wOne := add_zero
  natCast n := if n = 0 then ⊥ else ⊤
  natCast_zero := by simp
  natCast_succ _ := by
    simp; split_ifs
    · simp_all; rfl
    · simp_all; exact (@min_eq_right_iff ℕ∞ _ _).mp rfl
  wNpow n x :=
    if n = 0 then
      ⊤
    else
      let x' : ℕ∞ := x;
      n • x'
  wNpow_succ _ _ := by
    simp
    split_ifs
    · simp_all
      symm
      rw [add_comm]
      apply add_zero
    · rw [add_mul]
      simp
  wNpow_zero := by simp; rfl

@[simp]
def WeightedPartialOrder.ofPartialOrder (α : Type*) [PartialOrder α] : WeightedPartialOrder α where
  wle := (· ≤ ·)
  wle_refl := le_refl
  wle_trans := le_trans
  wle_antisymm := le_antisymm

@[simp] instance : WeightedPartialOrder (Tropical ℕ∞) := WeightedPartialOrder.ofPartialOrder _

instance : WeightedMonotonePreSemiring (Tropical ℕ∞) where
  wle_positive a := left_eq_inf.mp rfl
  wAdd_mono s := by
    intro a b hab
    simp_all
    gcongr
    exact hab
  wMul_mono_left s := by
    intro a b hab
    simp_all
    exact add_le_add_left hab s
  wMul_mono_right s := by
    intro a b hab
    simp_all
    exact add_le_add_right hab s

instance {x : ℕ} : OfNat (Tropical ℕ∞) x := ⟨some x⟩

#eval (wnk_pol { ~1 ⨀ ~0 ← 3 } : Pol[Fin 3, Tropical ENat]).compute 10 [fun _ ↦ 0] [fun x ↦ if x = 0 then 3 else 0]
