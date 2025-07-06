import WeightedNetKAT.Examples.Common

namespace WeightedNetKAT

open Fields

def p {𝒮 : Type} : Pol[Fields,ℕ,𝒮] := wnk_policy {
  if dst = H₄ then pt ← 2 ⨁ pt ← 3 ⨁ pt ← 5 else
  if dst = H₃ then pt ← 3 ⨁ pt ← 5 else
  if dst = H₂ then pt ← 2 ⨁ pt ← 5 else
  drop
}

def l {𝒮 : Type} : Pol[Fields,ℕ,𝒮] := wnk_policy {
  if pt = 2 then sw ← S₂ ; pt ← 1 else
  if pt = 3 then sw ← S₃ ; pt ← 1 else
  if pt = 5 then sw ← S₅ ; pt ← 1 else
  drop
}

/--
info: {(({dst↦4,pt↦2,sw↦0}, [{dst↦4,pt↦0,sw↦0}]), 3),
 (({dst↦4,pt↦3,sw↦0}, [{dst↦4,pt↦0,sw↦0}]), 3),
 (({dst↦4,pt↦5,sw↦0}, [{dst↦4,pt↦0,sw↦0}]), 3),
 (({dst↦4,pt↦2,sw↦2}, [{dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}]), 3),
 (({dst↦4,pt↦3,sw↦2}, [{dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}]), 3),
 (({dst↦4,pt↦5,sw↦2}, [{dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}]), 3)}
-/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄, 2, ⟨pk[dst ↦ H₄], []⟩] {
  dst = H₄;   dup; (~p; ~l; dup)*; ~p;   true
}

end WeightedNetKAT
