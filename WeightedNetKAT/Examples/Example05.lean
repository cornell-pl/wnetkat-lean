import WeightedNetKAT.Examples.Common
import WeightedNetKAT.WNKA
import WeightedNetKAT.Instances.Language
import WeightedNetKAT.Instances.ENat

namespace WeightedNetKAT

open Fields

-- inductive A where | a | b
-- deriving DecidableEq, Fintype, Repr

-- instance : Repr (Language A) := inferInstance
-- instance : DecidableEq (Language A) := fun a b ↦
--   sorry

-- #wnka_eval[Fin 2, Fin 2, Language A] { skip }

#wnka_eval[Fin 2, Fin 2, ℕ∞] { dup }
#wnka_eval[Fin 2, Fin 2, ℕ∞] { ~3 ⨀ dup }
#wnka_eval[Fin 2, Fin 2, ℕ∞] { skip ⨁ (~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) }
#wnka_eval[Fin 2, Fin 2, ℕ∞] { skip ⨁ (~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) ⨁ (~3 ⨀ dup; ~3 ⨀ dup) }
#wnka_eval[Fin 2, Fin 2, ℕ∞] { (~3 ⨀ dup)* }
#wnk_eval[ℕ∞, 8, (⟨pk[], []⟩ : H[Fields,ℕ])] { (~3 ⨀ dup)* }
-- #eval G (F:=Fields) (N:=Fin 2) wnk_rpol { (~(3 : ℕ∞) ⨀ dup)* } gs[pk[];pk[]]

end WeightedNetKAT
