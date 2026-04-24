module

public import WeightedNetKAT.Examples.Common
public import WeightedNetKAT.WNKA
public import WeightedNetKAT.WNKA.Explicit
public import WeightedNetKAT.rSafety
public import WeightedNetKAT.rReachability
public meta import WeightedNetKAT.WeightedSemiring.Instances
public import WeightedNetKAT.WeightedSemiring.Instances
public import WeightedNetKAT.Papers.PLDI2026
public import WeightedNetKAT.Perf
public import Lake.Util.Log

@[expose] public section

/-!

# Abilene

This file contains a simplified version of the _Abilene_ network

-/

/-- A version of `List.sum` that doesn't leave a trailing `0`

Useful for non-`AddZeroClass` instances of add.  -/
def List.sum' {α : Type*} [Add α] [Zero α] (a : List α) : α :=
  match a with
  | [] => 0
  | [x] => x
  | x::y::z => x + sum' (y::z)

/-- A version of `Array.sum` that doesn't leave a trailing `0`

Useful for non-`AddZeroClass` instances of add.  -/
def Array.sum' {α : Type*} [Add α] [Zero α] (a : Array α) : α := a.toList.sum'

namespace WeightedNetKAT

namespace Abilene

@[grind]
inductive Switch where | sw
deriving DecidableEq, Fintype, Inhabited, Repr
open Switch

instance : Listed Switch where
  array := #[sw]
  nodup := by simp
  complete := by simp
  encode _ := 0

@[grind]
inductive City where
  | SEA | CHI | NYC | BAY | DEN | KAN | IND | DC | LA | HOU | ATL
deriving DecidableEq, Fintype, Inhabited, Repr
open City

instance : Listed City where
  array := #[SEA, CHI, NYC, BAY, DEN, KAN, IND, DC, LA, HOU, ATL]
  nodup := by simp [Array.Nodup, Array.Pairwise]
  complete := by simp; grind
  encode
  | SEA => 0 | CHI => 1 | NYC => 2 | BAY => 3 | DEN => 4 | KAN => 5
  | IND => 6 | DC => 7 | LA => 8 | HOU => 9 | ATL => 10
  encode_len := by rintro (_ | _) <;> simp
  encode_prop := by rintro (_ | _) <;> simp

instance : Std.ToFormat Pk[Switch,City] where
  format x :=
    match x .sw with
    | .SEA => "SEA"
    | .CHI => "CHI"
    | .NYC => "NYC"
    | .BAY => "BAY"
    | .DEN => "DEN"
    | .KAN => "KAN"
    | .IND => "IND"
    | .DC => "DC"
    | .LA => "LA"
    | .HOU => "HOU"
    | .ATL => "ATL"
instance (priority := 1000000) {Q} [Std.ToFormat Q] : Repr Run[Switch,City,Q] where
  reprPrec := fun (ρ, (α, β), n) _ ↦ f!"⟨{ρ.reverse.map fun ⟨q₀, (α', β'), q₁⟩ ↦ (q₀, (β', α'), q₁)}, ({α}, {β}), {n}⟩"

instance {𝒮} {p : RPol[Switch,City,𝒮]} : Std.ToFormat (@S Switch instListedSwitch City 𝒮 p) where
  format x := reprStr x

def mod {𝒮} [Semiring 𝒮] {α : Type*} (c : α) : RPol[Switch,α,𝒮] :=
  .Mod (.fill c)
def test {𝒮} [Semiring 𝒮] {α : Type*} (c : α) : RPol[Switch,α,𝒮] :=
  .Test (.fill c)

def latency : City → City → Option Weighted.Arctic
  | SEA, DEN => ms 3
  | SEA, BAY => ms 2

  | CHI, NYC => ms 3
  | CHI, IND => ms 2

  | BAY, DEN => ms 4
  | BAY, LA  => ms 1

  | DEN, KAN => ms 3

  | KAN, IND => ms 2
  | KAN, HOU => ms 3

  | IND, ATL => ms 3

  | DC, NYC  => ms 1

  | LA, HOU  => ms 6

  | HOU, ATL => ms 3

  | ATL, DC  => ms 2

  | _, _ => none
where ms := some

def bandwidth : City → City → Option Weighted.Bottleneck
  | SEA, DEN  | DEN, SEA => mbps 500
  | SEA, BAY  | BAY, SEA => mbps 1000

  | CHI, NYC  | NYC, CHI => mbps 1500
  | CHI, IND  | IND, CHI => mbps 950

  | BAY, DEN  | DEN, BAY => mbps 800
  | BAY, LA   | LA, BAY => mbps 1500

  | DEN, KAN  | KAN, DEN => mbps 450

  | KAN, IND  | IND, KAN => mbps 875
  | KAN, HOU  | HOU, KAN => mbps 750

  | IND, ATL  | ATL, IND => mbps 600

  | DC, NYC   | NYC, DC => mbps 2500

  | LA, HOU   | HOU, LA => mbps 900

  | HOU, ATL  | ATL, HOU => mbps 700

  | ATL, DC   | DC, ATL => mbps 900

  | _, _ => none
where mbps := some

theorem bandwidth_is_symm {a b} : bandwidth a b = bandwidth b a := by
  cases a <;> cases b <;> rfl

open scoped Computability

open OmegaCompletePartialOrder

@[simp]
theorem OrderRingIso.ωSum_nat_eq_of_lawfulkstar {α β : Type*}
    [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [KStar α] [LawfulKStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]
    [Semiring β] [OmegaCompletePartialOrder β] [OrderBot β] [IsPositiveOrderedAddMonoid β] [KStar β] [LawfulKStar β] [MulLeftMono β] [MulRightMono β] [OmegaContinuousNonUnitalSemiring β]
    (e : α ≃+*o β) (f : ℕ → α) :
    e (ω∑ i, f i) = ω∑ i, e (f i) := by
  apply le_antisymm
  · apply e.symm.map_le_map_iff'.mp
    simp [ωSum_nat_eq_ωSup]
    apply fun i ↦ e.map_le_map_iff'.mp ?_
    simp
    apply le_ωSup_of_le i (by rfl)
  · simp [ωSum_nat_eq_ωSup]
    intro i
    apply e.symm.map_le_map_iff'.mp
    simp
    apply le_ωSup_of_le i
    rfl

@[simp]
theorem OrderRingIso.kstar_eq_of_lawfulkstar {α β : Type*}
    [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [KStar α] [LawfulKStar α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]
    [Semiring β] [OmegaCompletePartialOrder β] [OrderBot β] [IsPositiveOrderedAddMonoid β] [KStar β] [LawfulKStar β] [MulLeftMono β] [MulRightMono β] [OmegaContinuousNonUnitalSemiring β]
    (e : α ≃+*o β) (a : α) :
    e a∗ = (e a)∗ := by
  simp [LawfulKStar.kstar_eq_sum]

def build_of_rel {α β : Type} [Listed α] [DecidableEq α] [Semiring β] (r : α → α → Option β) : RPol[Switch,α,β] :=
  Listed.arrayOf α |>.filterMap (fun x ↦
    let s : RPol[Switch,α,β] :=
      Listed.arrayOf α |>.filterMap (fun y ↦ do some wnk_rpol { ~(← r x y) ⨀ ~(mod y) }) |>.sum'
    match s with
    | .Drop => none
    | _ => some wnk_rpol { ~(test x) ; ~s }
  ) |>.sum'

def run : IO Unit := do
  let pol := wnk_rpol { (~(build_of_rel bandwidth) ; dup)* }
  let n : EWNKA Switch City Weighted.Bottleneck (S pol) ← Perf.time "wnka" fun _ ↦ pol.ewnka
  println! " ∘ WNKA has been built!"

  let v ← Perf.time "rSafety sem" fun _ ↦ rSafety.Esem' n
  println! f!" ∘ rSafety: {reprStr v}"

  if v ≠ ⊤ then
    println! " ∘ extracting witness..."
    let ρ ← Perf.time "witness" fun _ ↦ rSafety.extraction n v
    println! f!" ∘ rSafety(witness): {reprStr (ρ.pks.map fun π ↦ π Switch.sw)}"
  else
    println! " ∘ rSafety is ⊤!"

  -- let ρ := rReachability.all n |>.filter fun (a, b) ↦ b ≠ Arctic.arc 0
  -- letI : Std.ToFormat (S pol) := instToFormatSSwitchCity
  -- println! f!" ∘ rReachability: {(ρ.map fun (a, b) ↦ ((instReprRunSwitchCityOfToFormat.reprPrec a 0), reprStr b))}"
