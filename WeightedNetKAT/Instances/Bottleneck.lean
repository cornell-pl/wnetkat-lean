import WeightedNetKAT.Computation
import Mathlib.Data.ENat.Lattice

def Bottleneck (α : Type) := α

variable {α : Type}

instance [i : Repr α] : Repr (Bottleneck α) := ⟨@reprPrec α i⟩

instance [LE α] : LE (Bottleneck α) := inferInstanceAs (LE α)

instance [PartialOrder α] : PartialOrder (Bottleneck α) := inferInstanceAs (PartialOrder α)
instance [LinearOrder α] : LinearOrder (Bottleneck α) := inferInstanceAs (LinearOrder α)

@[simp] instance [LinearOrder α] : WeightedAdd (Bottleneck α) := ⟨max⟩
@[simp] instance [LinearOrder α] : WeightedMul (Bottleneck α) := ⟨min⟩

@[simp]
def WeightedPartialOrder.ofPartialOrder [PartialOrder α] : WeightedPartialOrder α where
  wle := (· ≤ ·)
  wle_refl := le_refl
  wle_trans := le_trans
  wle_antisymm := le_antisymm

instance [Bot α] : Bot (Bottleneck α) := inferInstanceAs (Bot α)
instance [LE α] [OrderBot α] : OrderBot (Bottleneck α) := inferInstanceAs (OrderBot α)
instance [Top α] : Top (Bottleneck α) := inferInstanceAs (Top α)
instance [LE α] [OrderTop α] : OrderTop (Bottleneck α) := inferInstanceAs (OrderTop α)
@[simp] instance [LinearOrder α] [OrderBot α] : WeightedPreSemiring (Bottleneck α) where
  wZero := ⊥
  wAdd_assoc := max_assoc
  wZero_add := max_bot_left
  add_wZero := max_bot_right
  wNsmul n x := if n = 0 then ⊥ else x
  wNsmul_wZero _ := by rfl
  wNsmul_succ _ _  := by simp; split_ifs <;> simp
  wAdd_comm := max_comm
  left_distrib := inf_sup_left
  right_distrib := inf_sup_right
  wZero_mul := min_bot_left
  mul_wZero := min_bot_right
  mul_assoc := min_assoc

instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedSemiring (Bottleneck α) where
  wOne := ⊤
  wOne_mul := min_top_left
  mul_wOne := min_top_right
  natCast n := if n = 0 then ⊥ else ⊤
  natCast_zero := by simp
  natCast_succ := by simp
  wNpow n a := if n = 0 then ⊤ else a
  wNpow_succ _ _ := by simp; split_ifs <;> simp_all
  wNpow_zero := by simp

instance [PartialOrder α] : WeightedPartialOrder (Bottleneck α) := WeightedPartialOrder.ofPartialOrder
instance [LinearOrder α] [OrderBot α] [OrderTop α] : WeightedMonotonePreSemiring (Bottleneck α) where
  wle_positive := by simp; apply bot_le
  wAdd_mono s := by
    intro a b hab
    simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]
    exact LE.le.ge_or_le hab s
  wMul_mono_left s := by
    intro a b hab
    simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]
  wMul_mono_right s := by
    intro a b hab
    simp_all [wLe, instWeightedPartialOrderBottleneckOfPartialOrder]

example : LinearOrder (Fin 4) := inferInstance
example : OrderBot (Fin 4) := inferInstance
example : OrderTop (Fin 4) := inferInstance

def Secutiy₄ := Fin 4
def Secutiy₄.toFin (s : Secutiy₄) : Fin 4 := s

instance : LinearOrder Secutiy₄ := inferInstanceAs (LinearOrder (Fin 4))
instance : OrderBot Secutiy₄ := inferInstanceAs (OrderBot (Fin 4))
instance : OrderTop Secutiy₄ := inferInstanceAs (OrderTop (Fin 4))

def P : Policy[Fin 3, Bottleneck Secutiy₄] := wnk_policy { ~0 ← 3 }

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

#eval (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, Bottleneck Secutiy₄]).compute 10 [fun _ ↦ 0] [fun x ↦ if x = 0 then 3 else 0]
#eval (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, Bottleneck ENat]).compute 10 [fun _ ↦ 0] [fun x ↦ if x = 0 then 3 else 0]
#eval (wnk_policy { ~1 ⨀ ~0 ← 3 } : Policy[Fin 3, Bottleneck EENat]).compute 10 [fun _ ↦ 0] [fun x ↦ if x = 0 then 3 else 0]
