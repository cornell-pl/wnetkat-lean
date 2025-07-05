import WeightedNetKAT.Computation
import Mathlib.Data.Fintype.Order

open OmegaCompletePartialOrder

def BoolRing := Bool
deriving DecidableEq

instance : HOr BoolRing BoolRing BoolRing := ⟨or⟩
instance : HAnd BoolRing BoolRing BoolRing := ⟨and⟩

instance : HAdd BoolRing BoolRing BoolRing := ⟨or⟩
instance : HMul BoolRing BoolRing BoolRing := ⟨and⟩
instance : Add BoolRing := ⟨or⟩
instance : Mul BoolRing := ⟨and⟩
instance : Zero BoolRing := ⟨false⟩
instance : One BoolRing := ⟨true⟩

@[simp] theorem BoolRing.add_eqq_or {a b : BoolRing} : a + b = (or a b) := by simp [HAdd.hAdd]
@[simp] theorem BoolRing.mul_eqq_and {a b : BoolRing} : a * b = (and a b) := by simp [HMul.hMul]

@[simp] theorem BoolRing.zero_eq_false : (0 : BoolRing) = false := rfl
@[simp] theorem BoolRing.one_eq_true : (1 : BoolRing) = true := rfl

example (a b c : Bool) : (a || b || c) = (a || (b || c)) := by exact Bool.or_assoc a b c

instance : Semiring BoolRing where
  add_assoc := Bool.or_assoc
  zero_add := by simp
  add_zero := by simp
  nsmul n s := if n = 0 then false else s
  nsmul_zero := by simp
  nsmul_succ _ := by simp; split_ifs <;> simp
  add_comm := Bool.or_comm
  left_distrib := Bool.and_or_distrib_left
  right_distrib := Bool.and_or_distrib_right
  zero_mul := by simp
  mul_zero := by simp
  mul_assoc := Bool.and_assoc
  one_mul := by simp
  mul_one := by simp
  natCast n := if n = 0 then false else true
  natCast_zero := by simp
  natCast_succ := by simp
  npow n s := if n = 0 then true else s
  npow_succ := by simp
  npow_zero := by simp

instance : PartialOrder BoolRing := inferInstanceAs (PartialOrder Bool)

noncomputable instance : CompleteLattice BoolRing := inferInstanceAs (CompleteLattice Bool)
noncomputable instance : OmegaCompletePartialOrder BoolRing := inferInstanceAs (OmegaCompletePartialOrder Bool)

instance : MulLeftMono BoolRing := ⟨fun m _ _ h ↦
  Bool.le_and (Bool.and_le_left m _) (le_trans (Bool.and_le_right m _) h)⟩
instance : MulRightMono BoolRing := ⟨fun m _ _ h ↦
  Bool.le_and (le_trans (Bool.and_le_left _ m) h) (Bool.and_le_right _ m)⟩
instance : IsPositiveOrderedAddMonoid BoolRing where
  add_le_add_left _ _ h m := Bool.or_le (Bool.left_le_or _ _) (le_trans h (Bool.right_le_or m _))
  add_le_add_right _ _ h m := Bool.or_le (Bool.le_trans h (Bool.left_le_or _ _)) (Bool.right_le_or _ m)
  bot_eq_zero := rfl
instance : OmegaContinuousNonUnitalSemiring BoolRing where
  ωSup_add_right := by
    intro b
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, ?_⟩
    intro C
    simp [Add.add]
    rcases b <;> simp [Chain.map, OrderHom.comp, Function.comp]
    · rfl
    · unfold Function.comp; simp
  ωSup_add_left := by
    intro b
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, ?_⟩
    intro C
    simp [Add.add]
    rcases b <;> simp [Chain.map, OrderHom.comp, Function.comp]
    · rfl
    · unfold Function.comp; simp
  ωSup_mul_left := by
    intro b
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, ?_⟩
    intro C
    simp [Add.add]
    rcases b <;> simp [Chain.map, OrderHom.comp, Function.comp]
    · unfold Function.comp; simp
    · rfl
  ωSup_mul_right := by
    intro b
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, ?_⟩
    intro C
    simp [Add.add]
    rcases b <;> simp [Chain.map, OrderHom.comp, Function.comp]
    · unfold Function.comp; simp
    · rfl
