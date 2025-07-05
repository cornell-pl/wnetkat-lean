import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Lattice
import WeightedNetKAT.WNKA

def Bottleneck (α : Type) := α

variable {α : Type}

instance [i : Repr α] : Repr (Bottleneck α) := ⟨@reprPrec α i⟩

instance [LE α] : LE (Bottleneck α) := inferInstanceAs (LE α)

instance [PartialOrder α] : PartialOrder (Bottleneck α) := inferInstanceAs (PartialOrder α)
instance [LinearOrder α] : LinearOrder (Bottleneck α) := inferInstanceAs (LinearOrder α)

@[simp] instance [LinearOrder α] : Add (Bottleneck α) := ⟨max⟩
@[simp] instance [LinearOrder α] : Mul (Bottleneck α) := ⟨min⟩

@[simp] theorem Bottleneck.add_eq_max [LinearOrder α] {a b : Bottleneck α} : a + b = max a b := rfl
@[simp] theorem Bottleneck.mul_eq_min [LinearOrder α] {a b : Bottleneck α} : a * b = min a b := rfl

instance [Bot α] : Bot (Bottleneck α) := inferInstanceAs (Bot α)
instance [LE α] [OrderBot α] : OrderBot (Bottleneck α) := inferInstanceAs (OrderBot α)
instance [Top α] : Top (Bottleneck α) := inferInstanceAs (Top α)
instance [LE α] [OrderTop α] : OrderTop (Bottleneck α) := inferInstanceAs (OrderTop α)
instance [LE α] [OrderBot α] : Zero (Bottleneck α) := ⟨⊥⟩
@[simp] theorem Bottlenext.zero_eq_bot [LE α] [OrderBot α] : (0 : Bottleneck α) = ⊥ := rfl
instance [LE α] [OrderTop α] : One (Bottleneck α) := ⟨⊤⟩
@[simp] theorem Bottlenext.one_eq_top [LE α] [OrderTop α] : (1 : Bottleneck α) = ⊤ := rfl
@[simp] instance [LinearOrder α] [OrderBot α] [OrderTop α] : Semiring (Bottleneck α) where
  add_assoc := max_assoc
  zero_add := max_bot_left
  add_zero := max_bot_right
  nsmul n x := if n = 0 then ⊥ else x
  nsmul_zero _ := by rfl
  nsmul_succ _ _  := by simp; split_ifs <;> simp
  add_comm := max_comm
  left_distrib := inf_sup_left
  right_distrib := inf_sup_right
  zero_mul := min_bot_left
  mul_zero := min_bot_right
  mul_assoc := min_assoc
  one_mul := by simp
  mul_one := by simp

instance [LinearOrder α] [OrderBot α] [OrderTop α] : OmegaCompletePartialOrder (Bottleneck α) where
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le := sorry
instance [LinearOrder α] [OrderBot α] [OrderTop α] : MulLeftMono (Bottleneck α) := ⟨sorry⟩
instance [LinearOrder α] [OrderBot α] [OrderTop α] : MulRightMono (Bottleneck α) := ⟨sorry⟩
instance [LinearOrder α] [OrderBot α] [OrderTop α] : IsPositiveOrderedAddMonoid (Bottleneck α) where
  add_le_add_left:= by
    intro a b hab c
    simp
    if hac : a ≤ c then simp_all else
    simp_all
    exact .inr (hac.le.trans hab)
  add_le_add_right := by
    intro a b hab c
    simp
    if hac : a ≤ c then simp_all else
    simp_all
    exact .inl (hac.le.trans hab)
  bot_eq_zero := rfl
instance [LinearOrder α] [OrderBot α] [OrderTop α] : OmegaContinuousNonUnitalSemiring (Bottleneck α) where
  ωSup_add_left := sorry
  ωSup_add_right := sorry
  ωSup_mul_left := sorry
  ωSup_mul_right := sorry
instance [LinearOrder α] [OrderBot α] [OrderTop α] : CanonicallyOrderedAdd (Bottleneck α) where
  exists_add_of_le := by intro a b hab; simp; use b; simp_all
  le_self_add := by simp

instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedNetKAT.FinsuppStar (Bottleneck α) where
  wStar := sorry
instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedNetKAT.LawfulFinsuppStar (Bottleneck α) where
  wStar_eq_sum := sorry

-- instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedMonotonePreSemiring (Bottleneck α) where
--   wle_positive := by simp; apply bot_le
--   add_mono s := by
--     intro a b hab
--     simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]
--     exact LE.le.ge_or_le hab s
--   wMul_mono_left s := by
--     intro a b hab
--     simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]
--   wMul_mono_right s := by
--     intro a b hab
--     simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]

-- instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedOmegaCompletePartialOrder (Bottleneck α) where
--   wSup := sorry
--   wSup_le := sorry
--   le_wSup := sorry
-- instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedOmegaContinuousPreSemiring (Bottleneck α) where
--   add_wSup := sorry
--   wSup_add := sorry
--   wMul_wSup := sorry
--   wSup_wMul := sorry

instance [Countable α] : Countable (Bottleneck α) := inferInstanceAs (Countable α)

example : LinearOrder (Fin 4) := inferInstance
example : OrderBot (Fin 4) := inferInstance
example : OrderTop (Fin 4) := inferInstance

def Secutiy₄ := Fin 4
def Secutiy₄.toFin (s : Secutiy₄) : Fin 4 := s

instance : LinearOrder Secutiy₄ := inferInstanceAs (LinearOrder (Fin 4))
instance : OrderBot Secutiy₄ := inferInstanceAs (OrderBot (Fin 4))
instance : OrderTop Secutiy₄ := inferInstanceAs (OrderTop (Fin 4))

def P : Policy[Fin 3, ℕ, Bottleneck Secutiy₄] := wnk_policy { ~0 ← 3 }

instance {x : ℕ} [OfNat α x] : OfNat (Bottleneck α) x := inferInstanceAs (OfNat α x)
instance : OfNat Secutiy₄ 0 := ⟨0, by simp⟩
instance : OfNat Secutiy₄ 1 := ⟨1, by simp⟩
instance : OfNat Secutiy₄ 2 := ⟨2, by simp⟩
instance : OfNat Secutiy₄ 3 := ⟨3, by simp⟩

instance : Repr Secutiy₄ := ⟨fun s _ ↦ match s with | 0 => "⊥" | 1 => "L" | 2 => "M" | 3 => "H"⟩

def EENat := WithBot ENat
instance (n : ℕ) : OfNat EENat n := ⟨some (some n)⟩

instance : LinearOrder EENat := inferInstanceAs (LinearOrder (WithBot ENat))
instance : OrderBot EENat := inferInstanceAs (OrderBot (WithBot ENat))
instance : OrderTop EENat := inferInstanceAs (OrderTop (WithBot ENat))

instance : Repr ℕ∞ where
  reprPrec p n := if p = ⊤ then "⊤" else reprPrec p.toNat n
instance : Repr EENat where
  reprPrec p n := if p = ⊤ then "⊤" else if p = ⊥ then "⊥" else reprPrec p.get!.toNat n

#eval! (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, ℕ, Bottleneck Secutiy₄]).compute 10 (fun _ ↦ 0, []) (fun x ↦ if x = 0 then 3 else 0, [])
#eval! (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, ℕ, Bottleneck ENat]).compute 10 (fun _ ↦ 0, []) (fun x ↦ if x = 0 then 3 else 0, [])
#eval! (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, ℕ, Bottleneck EENat]).compute 10 (fun _ ↦ 0, []) (fun x ↦ if x = 0 then 3 else 0, [])
