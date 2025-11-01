import WeightedNetKAT.Examples.Common
import WeightedNetKAT.WNKA
import WeightedNetKAT.Instances.Language
import WeightedNetKAT.Instances.ENat

namespace WeightedNetKAT

open Fields

inductive Switch where | sw
deriving DecidableEq, Fintype, Inhabited, Repr
open Switch

instance : Listed Switch where
  list := [sw]
  nodup := by simp
  complete := by intro c; cases c; simp

inductive City where | SEA | CHI | NYC | BAY | DEN | KAN | IND | DC | LA | HOU | ATL
deriving DecidableEq, Fintype, Inhabited, Repr
open City

instance : Listed City where
  list := [SEA, CHI, NYC, BAY, DEN, KAN, IND, DC, LA, HOU, ATL]
  nodup := by simp
  complete := by intro c; cases c <;> simp

def p' {𝒮} [Semiring 𝒮] : City → Pol[Switch,City,𝒮]
| SEA => wnk_pol { 1 ⨀ sw ← BAY ⨁ 2 ⨀ sw ← DEN }
| CHI => wnk_pol { 1 ⨀ sw ← NYC ⨁ 2 ⨀ sw ← IND }
| NYC => wnk_pol { skip }
| BAY => wnk_pol { 1 ⨀ sw ← DEN ⨁ 2 ⨀ sw ← LA }
| DEN => wnk_pol { 1 ⨀ sw ← KAN }
| KAN => wnk_pol { 1 ⨀ sw ← IND ⨁ 2 ⨀ sw ← HOU }
| IND => wnk_pol { 1 ⨀ sw ← ATL }
| DC  => wnk_pol { 1 ⨀ sw ← NYC }
| LA  => wnk_pol { 1 ⨀ sw ← HOU }
| HOU => wnk_pol { 1 ⨀ sw ← ATL }
| ATL => wnk_pol { 1 ⨀ sw ← DC }

def p (𝒮) [Semiring 𝒮] : Pol[Switch,City,𝒮] := wnk_pol {
  (sw = SEA ; ~(p' SEA)) ⨁
  (sw = CHI ; ~(p' CHI)) ⨁
  (sw = NYC ; ~(p' NYC)) ⨁
  (sw = BAY ; ~(p' BAY)) ⨁
  (sw = DEN ; ~(p' DEN)) ⨁
  (sw = KAN ; ~(p' KAN)) ⨁
  (sw = IND ; ~(p' IND)) ⨁
  (sw = DC  ; ~(p' DC))  ⨁
  (sw = LA  ; ~(p' LA))  ⨁
  (sw = HOU ; ~(p' HOU)) ⨁
  (sw = ATL ; ~(p' ATL))
}

#wnka_eval[_, _, ℕ∞] { ~(p ℕ∞).toRPol }

example : (p ENat).toRPol = sorry := by
  simp [p, p', Pol.toRPol, Listed.list, Listed.listOf, Listed.encode, instListedCity, Listed.instVectorOfDecidableEq]

-- instance : Repr (Language A) := inferInstance
-- instance : DecidableEq (Language A) := fun a b ↦
--   sorry

-- #wnka_eval[Fin 2, Fin 2, Language A] { skip }

-- #wnka_eval[Fin 2, Fin 2, ℕ∞] { dup }
-- #wnka_eval[Fin 2, Fin 2, ℕ∞] { ~3 ⨀ dup }
-- #wnka_eval[Fin 2, Fin 2, ℕ∞] { skip ⨁ (~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) }
-- #wnka_eval[Fin 2, Fin 2, ℕ∞] { skip ⨁ (~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) }
-- #wnka_eval[Fin 2, Fin 2, ℕ∞] { (~3 ⨀ dup)* }
-- #wnk_eval[ℕ∞, 8, (⟨pk[], []⟩ : H[Fields,ℕ])] { (~3 ⨀ dup)* }
-- #eval G (F:=Fields) (N:=Fin 2) wnk_rpol { (~(3 : ℕ∞) ⨀ dup)* } gs[pk[];pk[]]

end WeightedNetKAT
