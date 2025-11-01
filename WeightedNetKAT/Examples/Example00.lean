import WeightedNetKAT.Examples.Common

namespace WeightedNetKAT

open Fields

/-- info: {(([(dst, 0), (pt, 3), (sw, 0)], []), 3), (([(dst, 0), (pt, 4), (sw, 0)], []), 2)} -/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/--
info: {(([(dst, 0), (pt, 3), (sw, 0)], []), none), (([(dst, 0), (pt, 4), (sw, 0)], []), some 2)}
-/
#guard_msgs in
#wnk_eval[Bottleneck ℕ∞,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/--
info: {(([(dst, 0), (pt, 3), (sw, 0)], []), some none), (([(dst, 0), (pt, 4), (sw, 0)], []), some (some 2))}
-/
#guard_msgs in
#wnk_eval[Bottleneck EENat,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/-- info: {(([(dst, 0), (pt, 3), (sw, 0)], []), true)} -/
#guard_msgs in
#wnk_eval[BoolRing,1] { pt ← 3 ⨁ ~false ⨀ pt ← 4 }

end WeightedNetKAT
