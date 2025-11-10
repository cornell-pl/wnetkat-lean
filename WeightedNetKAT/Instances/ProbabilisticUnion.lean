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

instance : Semiring ProbabilisticUnion where
  add := max'
  zero := prunion ⊥
  mul := union'
  one := prunion (Rat.ofInt 0)
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul n x := if n = 0 then prunion ⊥ else x
  nsmul_succ := sorry
  nsmul_zero := sorry
  add_comm := sorry
  left_distrib := sorry
  right_distrib := sorry
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
