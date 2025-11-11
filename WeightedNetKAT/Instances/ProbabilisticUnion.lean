import WeightedNetKAT.Computation
import WeightedNetKAT.Star
import WeightedNetKAT.Instances.ENat
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Tropical.Lattice
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Order.CompletePartialOrder
import Batteries.Data.Rat.Float

open OmegaCompletePartialOrder

def ProbabilisticUnion := WithBot ℚ deriving DecidableEq

namespace ProbabilisticUnion

def prunion (q : WithBot ℚ) : ProbabilisticUnion := q
def pct (q : ℚ) : ProbabilisticUnion := prunion (some (q / 100))
def unprunion (r : ProbabilisticUnion) : WithBot ℚ := r

def max' : ProbabilisticUnion -> ProbabilisticUnion -> ProbabilisticUnion
  | some q₁, some q₂ => if q₁ ≤ q₂ then prunion q₂ else prunion q₁
  | _ , some q | some q , _ => prunion q
  | none , none => prunion ⊥

def union' : ProbabilisticUnion -> ProbabilisticUnion -> ProbabilisticUnion
  | some q₁ , some q₂ => prunion (q₁ + q₂ - (q₁ * q₂))
  | _, _ => prunion ⊥

@[grind]
instance : Zero ProbabilisticUnion where
  zero := prunion ⊥

@[grind, simp]
theorem max'_zero {a} : max' 0 a = a := by
  simp [max']; split <;> simp_all [OfNat.ofNat, Zero.zero, prunion]; rfl
@[grind, simp]
theorem max'_bot {a} : max' (prunion ⊥) a = a := max'_zero
@[grind, simp]
theorem max'_idem {a} : max' a a = a := by
  simp [max']; split <;> simp_all [prunion] <;> rfl
theorem max'_assoc {a b c} : max' (max' a b) c = max' a (max' b c) := by
  simp [max']
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> simp [prunion]
  all_goals (try by_cases a ≤ b) <;> (try by_cases b ≤ c) <;> simp [*] <;> grind
theorem max'_comm {a b} : max' a b = max' b a := by
  simp [max']; split <;> simp_all [prunion]; grind

instance : Semiring ProbabilisticUnion where
  add := max'
  mul := union'
  one := prunion (Rat.ofInt 0)
  add_assoc _ _ _ := max'_assoc
  add_comm _ _ := max'_comm
  zero_add a := by
    simp [HAdd.hAdd, max', OfNat.ofNat, prunion]
    rcases a with _ | a <;> rfl
  add_zero a := by
    simp [HAdd.hAdd, max', OfNat.ofNat, prunion]
    rcases a with _ | a <;> rfl
  nsmul n x := if n = 0 then prunion ⊥ else x
  nsmul_succ n x := by simp [HAdd.hAdd]; grind
  nsmul_zero x := by simp; rfl
  left_distrib a b c := by
    simp [HAdd.hAdd, HMul.hMul]
    simp [union', max']
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> simp [prunion]
    sorry
  right_distrib a b c := by
    simp [HAdd.hAdd, HMul.hMul]
    simp [union', max']
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> simp [prunion]
    sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : WeightedNetKAT.Star ProbabilisticUnion where
  star
  | none => some 0
  | some q => if q = 0 then 0 else 1

instance : Repr ProbabilisticUnion where
  reprPrec r _ :=
    match r with
    | none => "-∞"
    | some q => reprStr (q : Float)
