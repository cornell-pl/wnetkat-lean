import WeightedNetKAT.Examples.Common

open Fields

/-- info: {([{dst↦0,pt↦3,sw↦0}], 3), ([{dst↦0,pt↦4,sw↦0}], 2)} -/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }
