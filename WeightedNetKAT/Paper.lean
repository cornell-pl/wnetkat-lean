import WeightedNetKAT.WNKA
import WeightedNetKAT.Instances.ENat

namespace WeightedNetKAT.Paper

namespace Section2

section

/- ## Semirings -/

/--
info: class Semiring.{u} (α : Type u) : Type u
number of parameters: 1
parents:
  Semiring.toNonUnitalSemiring : NonUnitalSemiring α
  Semiring.toNonAssocSemiring : NonAssocSemiring α
  Semiring.toMonoidWithZero : MonoidWithZero α
fields:
  Add.add : α → α → α
  AddSemigroup.add_assoc : ∀ (a b c : α), a + b + c = a + (b + c)
  Zero.zero : α
  AddZeroClass.zero_add : ∀ (a : α), 0 + a = a
  AddZeroClass.add_zero : ∀ (a : α), a + 0 = a
  AddMonoid.nsmul : ℕ → α → α
  AddMonoid.nsmul_zero : ∀ (x : α), AddMonoid.nsmul 0 x = 0 := by
    intros; rfl
  AddMonoid.nsmul_succ : ∀ (n : ℕ) (x : α), AddMonoid.nsmul (n + 1) x = AddMonoid.nsmul n x + x := by
    intros; rfl
  AddCommMagma.add_comm : ∀ (a b : α), a + b = b + a
  Mul.mul : α → α → α
  Distrib.left_distrib : ∀ (a b c : α), a * (b + c) = a * b + a * c
  Distrib.right_distrib : ∀ (a b c : α), (a + b) * c = a * c + b * c
  MulZeroClass.zero_mul : ∀ (a : α), 0 * a = 0
  MulZeroClass.mul_zero : ∀ (a : α), a * 0 = 0
  Semigroup.mul_assoc : ∀ (a b c : α), a * b * c = a * (b * c)
  One.one : α
  MulOneClass.one_mul : ∀ (a : α), 1 * a = a
  MulOneClass.mul_one : ∀ (a : α), a * 1 = a
  NatCast.natCast : ℕ → α :=
    Nat.unaryCast
  AddMonoidWithOne.natCast_zero : ↑0 = 0 := by
    intros; rfl
  AddMonoidWithOne.natCast_succ : ∀ (n : ℕ), ↑(n + 1) = ↑n + 1 := by
    intros; rfl
  Monoid.npow : ℕ → α → α :=
    npowRecAuto
  Monoid.npow_zero : ∀ (x : α), Semiring.npow 0 x = 1 := by
    intros; rfl
  Monoid.npow_succ : ∀ (n : ℕ) (x : α), Semiring.npow (n + 1) x = Semiring.npow n x * x := by
    intros; rfl
constructor:
  Semiring.mk.{u} {α : Type u} [toNonUnitalSemiring : NonUnitalSemiring α] [toOne : One α]
    (one_mul : ∀ (a : α), 1 * a = a) (mul_one : ∀ (a : α), a * 1 = a) [toNatCast : NatCast α]
    (natCast_zero : ↑0 = 0 := by intros; rfl) (natCast_succ : ∀ (n : ℕ), ↑(n + 1) = ↑n + 1 := by intros; rfl)
    (npow : ℕ → α → α) (npow_zero : ∀ (x : α), npow 0 x = 1 := by intros; rfl)
    (npow_succ : ∀ (n : ℕ) (x : α), npow (n + 1) x = npow n x * x := by intros; rfl) : Semiring α
field notation resolution order:
  Semiring, NonUnitalSemiring, NonAssocSemiring, MonoidWithZero, NonUnitalNonAssocSemiring, Monoid, MulZeroOneClass, SemigroupWithZero, AddCommMonoidWithOne, MulOneClass, AddMonoidWithOne, AddCommMonoid, Distrib, Semigroup, MulZeroClass, NatCast, AddMonoid, One, AddCommSemigroup, AddSemigroup, AddZeroClass, Mul, Zero, AddCommMagma, Add
-/
#guard_msgs in
#print Semiring

variable {𝒮 : Type*} [Semiring 𝒮]
variable {s₁ s₂ s₃ : 𝒮}

/-- **(1)** (𝒮, +, 𝟘) is a commutative monoid -/
example : AddMonoid 𝒮 × AddCommMagma 𝒮 := (inferInstance, inferInstance)

/-- **(2)** (𝒮, ·, 𝟙) is a monoid -/
example : Monoid 𝒮 := inferInstance

/-- **(3)** multiplication _distributes_ over _addition_ -/
example : LeftDistribClass 𝒮 ∧ RightDistribClass 𝒮 :=
  ⟨Distrib.leftDistribClass 𝒮, Distrib.rightDistribClass 𝒮⟩

/-- **(4)** _multiplication_ with 𝟘 is _annihilating_ -/
example : 0 * s₁ = 0 ∧ s₁ * 0 = 0 := by simp

end

section

/-! ## ω-continuous semiring

As a sligth deviation from the paper, we introduce both _semirings_ (as in the paper), but also a
weaker structure called _non-unital semirings_ where `𝟙` is not defined.

An example of of non-unital semirings are functions over semirings with finite support where the
codomain is neither.

In general we might declare theorems with the minimal set of requirements; thus if something does
not require unit, then well prove it for [`NonUnitalSemiring`].

For comparison operators, we will alwasy use `≤` over `≼` to fit into Leans and Mathlibs definition
and classes.

-/

variable {𝒮 : Type*} [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

example : NonUnitalSemiring 𝒮 := inferInstance

/-- **(1)** 𝒮 is a semiring -/
example : Semiring 𝒮 := inferInstance

/-- **(2)** 𝒮 is an ω-complete partial order -/
example : OmegaCompletePartialOrder 𝒮 := inferInstance

/-- **(3)** ≤ is positive, i.e., 𝟘 is least element of ≤ -/
example : OrderBot 𝒮 := inferInstance

/-- **(4)** both + and * are ω-continuous.

These exists under [`OmegaContinuousNonUnitalSemiring`] as
- [`ωScottContinuous_add_right`]
- [`ωScottContinuous_add_left`]
- [`ωScottContinuous_mul_right`]
- [`ωScottContinuous_mul_left`]
 -/
example : OmegaContinuousNonUnitalSemiring 𝒮  := inferInstance

/-- **(5)** 𝒮 admits countable sums

We define a new sum operator [`ωSum`] (`ω∑`) for countable sums as opposed to using [`tsum`] (`∑'`)
from Mathlib which uses topological limits of filters. These may be equivalent under the right
topology, but we make no such claim.

-/
example : 0 ≤ ω∑ (i : ℕ), (i : ENat) := by
  simp

end

end Section2

namespace Section3

/-! # wNetKAT: Syntax and Semantics

The language (wNetKat) is defined by [`WeightedNetKat`]. We provide custom syntax to ease writing
policies and tests.

Polices ([`Pol`]) are generic over three types:

- `F`: fields
- `N`: values
- `W`: weights

-/

inductive ExFields where | a | b | c deriving Fintype, DecidableEq
open ExFields

variable {𝒮 : Type} [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

example {π} {h} {r₁ r₂ : 𝒮} :
      (wnk_pol[ExFields,Fin 2,𝒮] {
        (~(r₁) ⨀ a ← 1) ⨁ (~(r₂) ⨀ b ← 2)
      }).sem (π, h) (π[a ↦ 1], h)
    = r₁ + if π[b ↦ 0] = π[a ↦ 1] then r₂ else 0 := by
  simp [Pol.sem]; grind

end Section3

namespace Section4

/-! # wNetKAT Subsumes NetKAT and Guarded ProbNetKAT

TODO

-/

end Section4

namespace Section5

/-! # Language Model -/

section

/-! ## Reduced Syntax

Policies of the reduced syntax are modeled by a new inductive definition ([`RPol`]), with a new
associated semantics ([`RPol.sem`]).

The reduction from full polices to reduced are given by [`Pol.toRPol`] and is proven semantically
sound by [`Pol.toRol_sem_eq_sem`]

-/

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]

variable [Listed F]
variable [Listed N] [Inhabited N]

/-- ### Theorem 3 (Soundness of Reduction) -/
example (p : Pol[F,N,𝒮]) : p.toRPol.sem = p.sem := Pol.toRol_sem_eq_sem p

end

section

/-! ## Guarded Strings

Guarded strings ([`GS`]) modeled as a packet pair, interposed by a (possibly empty) sequence of
packets. For maximal compatibility between definitions and theorems, we make no distinction between
_packets_, _packet tests_, and _packet assignments_.

Their semantics is defined by [`G`].

-/

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

/-- ### Theorem 4 (Denotation-Language Correspondence)-/
example {p : RPol[F,N,𝒮]} :
    p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h := RPol.sem_G p

end

end Section5

namespace Section6

/-! # wNetKat Automata



-/

/--
info: structure WeightedNetKAT.WNKA (F N 𝒮 Q : Type) [Semiring 𝒮] : Type
number of parameters: 5
fields:
  WeightedNetKAT.WNKA.ι : 𝒲[𝟙, Q, 𝒮]
  WeightedNetKAT.WNKA.δ : Pk[F,N] → Pk[F,N] → 𝒲[Q, Q, 𝒮]
  WeightedNetKAT.WNKA.𝒪 : Pk[F,N] → Pk[F,N] → 𝒲[Q, 𝟙, 𝒮]
constructor:
  WeightedNetKAT.WNKA.mk {F N 𝒮 Q : Type} [Semiring 𝒮] (ι : 𝒲[𝟙, Q, 𝒮]) (δ : Pk[F,N] → Pk[F,N] → 𝒲[Q, Q, 𝒮])
    (𝒪 : Pk[F,N] → Pk[F,N] → 𝒲[Q, 𝟙, 𝒮]) : WNKA F N 𝒮 Q
-/
#guard_msgs in
#print WNKA

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F] [Listed F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N]

variable [Star 𝒮] [LawfulStar 𝒮]

/-- ### Theorem 5 (Soundness of Thompson) -/
example {p : RPol[F,N,𝒮]} : p.wnka.sem = G p := p.wnka_sem

/-- ### Corollary 1 -/
example {p : Pol[F,N,𝒮]} {π} {h} : p.sem ⟨π, []⟩ h = p.toRPol.wnka.sem (π, h.2.reverse, h.1) :=
  the_complete_theorem _ _ _

end Section6

end WeightedNetKAT.Paper
