import WeightedNetKAT.Examples.Common
import WeightedNetKAT.WNKA
import WeightedNetKAT.rSafety
import WeightedNetKAT.rReachability
import WeightedNetKAT.Instances.Language
import WeightedNetKAT.Instances.ENat
import WeightedNetKAT.Instances.Arctic

def List.sum' {α : Type} [Add α] [Zero α] (a : List α) : α :=
  match a with
  | [] => 0
  | [x] => x
  | x::y::z => x + sum' (y::z)

def Array.sum' {α : Type} [Add α] [Zero α] (a : Array α) : α := a.toList.sum'

namespace WeightedNetKAT

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

def mod {𝒮} [Semiring 𝒮] {α : Type} (c : α) : RPol[Switch,α,𝒮] :=
  .Mod (.fill c)
def test {𝒮} [Semiring 𝒮] {α : Type} (c : α) : RPol[Switch,α,𝒮] :=
  .Test (.fill c)

def latency : City → City → Option Arctic
  -- | SEA, DEN => ms 3
  -- | SEA, BAY => ms 2

  -- | CHI, NYC => ms 3
  -- | CHI, IND => ms 2

  -- | BAY, DEN => ms 4
  -- | BAY, LA => ms 1

  -- | DEN, KAN => ms 3

  -- | KAN, IND => ms 2
  -- | KAN, HOU => ms 3

  | IND, ATL => ms 3

  -- | DC, NYC => ms 1

  | LA, HOU => ms 6

  | HOU, ATL => ms 3

  | ATL, DC => ms 2

  | _, _ => none
where ms := Arctic.arc

def bandwidth : City → City → Option (Bottleneck EENat)
  -- | SEA, DEN => mbps 500
  -- | SEA, BAY => mbps 1000

  -- | CHI, NYC => mbps 1500
  -- | CHI, IND => mbps 950

  -- | BAY, DEN => mbps 800
  -- | BAY, LA => mbps 1500

  -- | DEN, KAN => mbps 450

  -- | KAN, IND => mbps 875
  -- | KAN, HOU => mbps 750

  | IND, ATL => mbps 600

  | DC, NYC => mbps 2500

  | LA, HOU => mbps 900

  | HOU, ATL => mbps 700

  | ATL, DC => mbps 900

  | _, _ => none
where mbps := some ∘ id


def build_of_rel {α β : Type} [Listed α] [DecidableEq α] [Semiring β] (r : α → α → Option β) : RPol[Switch,α,β] :=
  Listed.arrayOf α |>.filterMap (fun x ↦
    let s : RPol[Switch,α,β] :=
      Listed.arrayOf α |>.filterMap (fun y ↦ do some wnk_rpol { ~(← r x y) ⨀ ~(mod y) }) |>.sum'
    match s with
    | .Drop => none
    | _ => some wnk_rpol { ~(test x) ; ~s }
  ) |>.sum'

def p_latency := build_of_rel latency
def p_bandwidth := build_of_rel bandwidth

def p' {𝒮} [Semiring 𝒮] : City → RPol[Switch,City,𝒮]
| SEA => wnk_rpol { 1 ⨀ ~(mod BAY) ⨁ 2 ⨀ ~(mod DEN) }
| CHI => wnk_rpol { 1 ⨀ ~(mod NYC) ⨁ 2 ⨀ ~(mod IND) }
| NYC => wnk_rpol { skip }
| BAY => wnk_rpol { 1 ⨀ ~(mod DEN) ⨁ 2 ⨀ ~(mod LA) }
| DEN => wnk_rpol { 1 ⨀ ~(mod KAN) }
| KAN => wnk_rpol { 1 ⨀ ~(mod IND) ⨁ 2 ⨀ ~(mod HOU) }
| IND => wnk_rpol { 1 ⨀ ~(mod ATL) }
| DC  => wnk_rpol { 1 ⨀ ~(mod NYC) }
| LA  => wnk_rpol { 1 ⨀ ~(mod HOU) }
| HOU => wnk_rpol { 1 ⨀ ~(mod ATL) }
| ATL => wnk_rpol { 1 ⨀ ~(mod DC) }

def p (𝒮) [Semiring 𝒮] : RPol[Switch,City,𝒮] := wnk_rpol {
  (~(test SEA) ; ~(p' SEA)) ⨁
  (~(test CHI) ; ~(p' CHI)) ⨁
  (~(test NYC) ; ~(p' NYC)) ⨁
  (~(test BAY) ; ~(p' BAY)) ⨁
  (~(test DEN) ; ~(p' DEN)) ⨁
  (~(test KAN) ; ~(p' KAN)) ⨁
  (~(test IND) ; ~(p' IND)) ⨁
  (~(test DC)  ; ~(p' DC))  ⨁
  (~(test LA)  ; ~(p' LA))  ⨁
  (~(test HOU) ; ~(p' HOU)) ⨁
  (~(test ATL) ; ~(p' ATL))
}

example : p _ = p_latency := by
  simp [p, p_latency, build_of_rel, latency, Listed.arrayOf, Listed.array, p', latency.ms, Array.sum', List.sum']
  simp only [HAdd.hAdd, Zero.zero, OfNat.ofNat]
  simp only [Nat.zero_eq, WithTop.coe_zero, Nat.cast_ofNat, -RPol.Add.injEq, -RPol.Seq.injEq,
    reduceCtorEq, and_false, RPol.Weight.injEq, and_true, true_and, false_and, and_self]
  sorry

-- p_0 = 2 (*) sw <- 1
--         (+)
--       3 (*) sw <- 2

-- p_1 = 2 (*) sw <- 3

-- p_2 = 1 (*) sw <- 3

-- p = sw = 0 ; p_0 (+)
--     sw = 1 ; p_1 (+)
--     sw = 2 ; p_2 (+)
--     sw = 3

-- net = (p; dup)*

open Arctic in
def p₀ : Fin 4 → RPol[Switch,Fin 4,Arctic]
| 0 => wnk_rpol { ~(arc 2) ⨀ ~(mod 1) ⨁ ~(arc 3) ⨀ ~(mod 2) }
| 1 => wnk_rpol { ~(arc 2) ⨀ ~(mod 3) }
| 2 => wnk_rpol { ~(arc 1) ⨀ ~(mod 3) }
| 3 => wnk_rpol { skip }

def p₀' : RPol[Switch,Fin 4,Arctic] := wnk_rpol {
  (~(test 0) ; ~(p₀ 0)) ⨁
  (~(test 1) ; ~(p₀ 1)) ⨁
  (~(test 2) ; ~(p₀ 2)) ⨁
  (~(test 3))
}

-- p_0 = 2 (*) sw <- 1
-- p = sw = 0 ; p_0
--         (+)
--       sw = 1
-- net = (p; dup)*

open Arctic in
def p₁ : RPol[Switch,Fin 2,Arctic] := wnk_rpol {
  (~(test 0) ; ~(arc 2) ⨀ ~(mod 1)) ⨁
  (~(test 1))
}

end WeightedNetKAT

open WeightedNetKAT

-- class Test (α : Type) where
--   things : List α

-- instance (α : Type) : Test α :=
--   printprint "wow" {things := []}

-- #wnka_eval[Switch, City, ℕ∞] { skip }

-- instance : Listed Pk[Switch,City] := Listed.pi Switch City

-- def test (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Listed α] [Listed β] [Inhabited β] [Repr α] [Repr β] : IO Unit := do
--   println! "Start"
--   let a : Array Pk[α,β] := Listed.array
--   println! "1 {a.map reprStr}"
--   let b : Array Pk[α,β] := Listed.array
--   println! "b {b.map reprStr}"
--   let c : Array Pk[α,β] := Listed.array
--   println! "c {c.map reprStr}"

example {Q : Type} [Repr Q] : Repr (rReachability.Run (F:=Switch) (N:=City) (Q:=Q)) := inferInstance

-- /-- info: 'WeightedNetKAT.RPol.wnka' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- #guard_msgs in
-- #print axioms RPol.wnka
-- /--
-- info: 'WeightedNetKAT.the_complete_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms the_complete_theorem
-- /--
-- info: 'WeightedNetKAT.rSafety.sem'' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms rSafety.sem'

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

instance {𝒮} {p : RPol[Switch,City,𝒮]} : Std.ToFormat (S p) where
  format x := reprStr x

def main : IO Unit := do
  -- test Switch City

  -- println! "Start"
  -- let a : List ℕ := Test.things
  -- println! "1 {a}"
  -- let b : List ℕ := Test.things
  -- println! "2 {b}"
  -- let c : List ℕ := Test.things
  -- println! "3 {c}"
  -- let d : List ℕ := Test.things
  -- println! "4 {d}"
  -- let res := wnk_rpol { ~(p ℕ∞) }.eval
  -- let n : ℕ := 12
  -- let res := unsafe unsafeIO (println! "star_fin({n})")
  -- let xs : Array Pk[Switch,City] := Listed.pi_array (α:=Switch) (β:=City)
  -- println! f!"Pk[Switch,City]: {reprStr xs}"
  -- let := Listed.ofArray xs Listed.pi_array_nodup (fun _ ↦ Listed.mem_pi_array)
  -- let pol := wnk_rpol { ~p₁ }
  -- let pol := wnk_rpol { (~p₁ ; dup)* }
  -- let pol := wnk_rpol { (~(p Arctic) ; dup)* }
  let pol := wnk_rpol { (~p_latency ; dup)* }
  -- let res ← pol.eval
  let n : WNKA _ _ _ (S pol) := pol.wnka

  println! " ∘ WNKA has been built!"

  let v := rSafety.sem' n
  println! f!" ∘ rSafety: {reprStr v}"

  if v ≠ ⊤ then
    println! " ∘ extracting witness..."
    let ρ := rSafety.extraction n.toEWNKA v
    println! f!" ∘ rSafety(witness): {reprStr (ρ.pks.map fun π ↦ π Switch.sw)}"
  else
    println! " ∘ rSafety is ⊤!"

  let ρ := rReachability.all n |>.filter fun (a, b) ↦ b ≠ Arctic.arc 0
  println! f!" ∘ rReachability: {(ρ.map fun (a, b) ↦ ((instReprRunSwitchCityOfToFormat.reprPrec a 0), reprStr b))}"
