import WeightedNetKAT.Examples.Common

open Fields

/-- info: {([{dst↦0,pt↦3,sw↦0}], H), ([{dst↦0,pt↦4,sw↦0}], M)} -/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/-- info: {([{dst↦0,pt↦3,sw↦0}], ⊤), ([{dst↦0,pt↦4,sw↦0}], 2)} -/
#guard_msgs in
#wnk_eval[Bottleneck ℕ∞,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/-- info: {([{dst↦0,pt↦3,sw↦0}], ⊤), ([{dst↦0,pt↦4,sw↦0}], 2)} -/
#guard_msgs in
#wnk_eval[Bottleneck EENat,1] { pt ← 3 ⨁ 2 ⨀ pt ← 4 }

/-- info: {([{dst↦0,pt↦3,sw↦0}], true)} -/
#guard_msgs in
#wnk_eval[Bool,1] { pt ← 3 ⨁ ~false ⨀ pt ← 4 }
