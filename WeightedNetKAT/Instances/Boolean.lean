import WeightedNetKAT.Computation

@[simp] instance : WeightedAdd Bool := ⟨(· ∨ ·)⟩
@[simp] instance : WeightedMul Bool := ⟨(· ∧ ·)⟩
@[simp] instance : WeightedZero Bool := ⟨False⟩
@[simp] instance : WeightedOne Bool := ⟨True⟩
@[simp] instance : WeightedLE Bool := ⟨(· ≤ ·)⟩

attribute [local simp] WeightedHMul.wHMul

instance : WeightedSemiring Bool where
  wAdd_assoc := by simp
  wZero_add := by simp
  add_wZero := by simp
  wNsmul n s := if n = 0 then False else s
  wNsmul_wZero := by simp
  wNsmul_succ := by simp
  wAdd_comm := by simp
  left_distrib := by simp
  right_distrib := by simp
  wZero_mul := by simp
  mul_wZero := by simp
  mul_assoc := by simp
  wOne_mul := by simp
  mul_wOne := by simp
  natCast n := if n = 0 then False else True
  natCast_zero := by simp
  natCast_succ := by simp
  wNpow n s := if n = 0 then True else s
  wNpow_succ := by simp
  wNpow_zero := by simp

instance : WeightedPartialOrder Bool where
  wle_refl := by simp [wLe]
  wle_trans := by simp [wLe]
  wle_antisymm := by simp [wLe]

instance : WeightedMonotonePreSemiring Bool where
  wle_positive := by simp [wLe, WeightedZero.wZero, WeightedLE.wle]
  wAdd_mono s a b hab := by
    simp [wLe, WeightedZero.wZero, WeightedLE.wle, WeightedAdd.wAdd, Bool.instLE]
    aesop
  wMul_mono_left s a b hab := by
    simp [wLe, WeightedZero.wZero, WeightedLE.wle, WeightedMul.wMul, Bool.instLE]
    aesop
  wMul_mono_right s a b hab := by
    simp [wLe, WeightedZero.wZero, WeightedLE.wle, WeightedMul.wMul, Bool.instLE]
    aesop

@[simp]
noncomputable instance : WeightedOmegaCompletePartialOrder Bool where
  wSup C := ⨆ i, C i
  le_wSup := by
    intro C i
    simp_all only [wLe, WeightedLE.wle]
    exact le_iSup_iff.mpr fun b a ↦ a i
  wSup_le := by
    intro C x hx
    simp_all only [wLe, WeightedLE.wle]
    exact iSup_le hx

noncomputable instance : WeightedOmegaContinuousPreSemiring Bool where
  wAdd_wSup := by
    intro b C
    simp [WeightedAdd.wAdd]
    magic_simp
    rcases b <;> simp
  wSup_wAdd := by
    intro b C
    simp [WeightedAdd.wAdd]
    magic_simp
    rcases b <;> simp
  wMul_wSup := by
    intro b C
    simp [WeightedMul.wMul]
    magic_simp
    rcases b <;> simp
  wSup_wMul := by
    intro b C
    simp [WeightedMul.wMul]
    magic_simp
    rcases b <;> simp
