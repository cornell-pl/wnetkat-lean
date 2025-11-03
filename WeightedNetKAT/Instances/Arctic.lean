import WeightedNetKAT.Computation
import WeightedNetKAT.Star
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Tropical.Lattice
import Mathlib.Algebra.Tropical.BigOperators

def Arctic := WithBot (OrderDual ℕ)

namespace Arctic

def arc (n : WithBot (OrderDual ℕ)) : Arctic := n
def unarc (a : Arctic) : WithBot (OrderDual ℕ) := a

@[simp]
instance : Lattice Arctic := inferInstanceAs (Lattice (WithBot (OrderBot ℕ)))
instance : CompleteLattice Arctic := inferInstanceAs (CompleteLattice (WithBot (OrderBot ℕ)))

instance : OmegaCompletePartialOrder Arctic where
  ωSup c := sorry
  ωSup_le := sorry
  le_ωSup := sorry

instance : Mul Arctic where
  mul a b := a.unarc + b.unarc
instance : Add Arctic where
  add a b := a ⊔ b

instance : One Arctic := ⟨arc 0⟩

@[simp] theorem one_eq_zero : instOne.one = arc 0 := by rfl
@[simp] theorem one_eq_zero' : @OfNat.ofNat Arctic 1 One.toOfNat1 = arc 0 := by rfl

instance : Zero Arctic := ⟨none⟩

@[simp] theorem zero_eq_bot : instZero.zero = arc ⊥ := by rfl
@[simp] theorem zero_eq_bot' : @OfNat.ofNat Arctic 0 Zero.toOfNat0 = arc ⊥ := by rfl

@[simp] theorem add_eq_sup {a b} : instAdd.add a b = a ⊔ b := by rfl
@[simp] theorem hAdd_eq_sup {a b} : @HAdd.hAdd Arctic Arctic Arctic instHAdd a b = a ⊔ b := by rfl
@[simp] theorem mul_eq_sup {a b} : instMul.mul a b = a.unarc + b.unarc := by rfl
@[simp] theorem hMul_eq_add {a b} : @HMul.hMul Arctic Arctic Arctic instHMul a b = a.unarc + b.unarc := by rfl

@[simp] theorem sup_unarc {a b : Arctic} : (a ⊔ b).unarc = a ⊔ b := rfl
@[simp] theorem add_unarc {a b : Arctic} : (a + b).unarc = a ⊔ b := rfl
@[simp] theorem unarc_add_unarc {a b : Arctic} : Arctic.unarc (a.unarc + b.unarc) = a.unarc + b.unarc := by
  rfl

@[simp] theorem arc_unarc {a} : arc (unarc a) = a := rfl
@[simp] theorem unarc_arc {a} : unarc (arc a) = a := rfl

instance : Semiring Arctic where
  add_assoc := by simp [sup_assoc]
  zero_add a := by simp; exact bot_le (α:=WithBot ℕ) (a:=a)
  add_zero a := by simp; exact bot_le (α:=WithBot ℕ) (a:=a)
  add_comm := by simp [sup_comm]
  left_distrib a b c := by simp [add_max]; rfl
  right_distrib a b c := by simp [max_add]; rfl
  zero_mul _ := by simp; rfl
  mul_zero _ := by simp; rfl
  mul_assoc _ _ _ := by simp [add_assoc]
  one_mul _ := by simp; rfl
  mul_one _ := by simp; rfl
  nsmul n x := if n = 0 then 0 else x
  nsmul_succ _ _ := by
    simp
    split_ifs
    · exact left_eq_inf.mp rfl
    · rfl
  nsmul_zero := by
    simp

instance : IsPositiveOrderedAddMonoid Arctic where
  add_le_add_left _ _ h _ := by simp [le_sup_of_le_right h]
  bot_eq_zero := rfl

instance : WeightedNetKAT.Star Arctic where
  star x := sorry

instance : WeightedNetKAT.LawfulStar Arctic where
  star_eq_sum := sorry

end Arctic
