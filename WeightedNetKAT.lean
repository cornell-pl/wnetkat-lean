import WeightedNetKAT.Examples.Common
import WeightedNetKAT.WNKA
import WeightedNetKAT.Instances.Language
import WeightedNetKAT.Instances.ENat

namespace WeightedNetKAT

open Fields

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

def mod {𝒮} [Semiring 𝒮] (c : City) : RPol[Switch,City,𝒮] :=
  .Mod fun _ ↦ c
def test {𝒮} [Semiring 𝒮] (c : City) : RPol[Switch,City,𝒮] :=
  .Test fun _ ↦ c

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
-- | ATL => wnk_rpol { skip

def p (𝒮) [Semiring 𝒮] : RPol[Switch,City,𝒮] := wnk_rpol {
  -- (~(test SEA) ; ~(p' SEA)) ⨁
  -- (~(test CHI) ; ~(p' CHI)) ⨁
  -- (~(test NYC) ; ~(p' NYC)) ⨁
  -- (~(test BAY) ; ~(p' BAY)) ⨁
  -- (~(test DEN) ; ~(p' DEN)) ⨁
  -- (~(test KAN) ; ~(p' KAN)) ⨁
  -- (~(test IND) ; ~(p' IND)) ⨁
  -- (~(test DC)  ; ~(p' DC))  ⨁
  -- (~(test LA)  ; ~(p' LA))  ⨁
  -- (~(test HOU) ; ~(p' HOU)) ⨁
  (~(test ATL) ; ~(p' ATL))
}

end WeightedNetKAT

open WeightedNetKAT

-- class Test (α : Type) where
--   things : List α

-- instance (α : Type) : Test α :=
--   printprint "wow" {things := []}

-- #wnka_eval[Switch, City, ℕ∞] { skip }

instance : Listed Pk[Switch,City] := Listed.pi _ _

-- def test (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Listed α] [Listed β] [Inhabited β] [Repr α] [Repr β] : IO Unit := do
--   println! "Start"
--   let a : Array Pk[α,β] := Listed.array
--   println! "1 {a.map reprStr}"
--   let b : Array Pk[α,β] := Listed.array
--   println! "b {b.map reprStr}"
--   let c : Array Pk[α,β] := Listed.array
--   println! "c {c.map reprStr}"


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

  let res ← wnk_rpol { (~(p ℕ∞))* }.eval
  println! f!"{res}"
