import WeightedNetKAT.Examples.Common

open Fields

def p {𝒮 : Type} : Policy[Fields,𝒮] := wnk_policy {
  match
  | dst = H₄ ↦ pt ← 2 ⨁ pt ← 3 ⨁ pt ← 5
  | dst = H₃ ↦ pt ← 3 ⨁ pt ← 5
  | dst = H₂ ↦ pt ← 2 ⨁ pt ← 5
}
def l {𝒮 : Type} : Policy[Fields,𝒮] := wnk_policy {
  match
  | pt = 2 ↦ sw ← S₂ ; pt ← 1
  | pt = 3 ↦ sw ← S₃ ; pt ← 1
  | pt = 5 ↦ sw ← S₅ ; pt ← 1
}

/--
info: {([{dst↦4,pt↦2,sw↦0}, {dst↦4,pt↦0,sw↦0}], 3),
 ([{dst↦4,pt↦3,sw↦0}, {dst↦4,pt↦0,sw↦0}], 3),
 ([{dst↦4,pt↦5,sw↦0}, {dst↦4,pt↦0,sw↦0}], 3),
 ([{dst↦4,pt↦2,sw↦2}, {dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}], 3),
 ([{dst↦4,pt↦3,sw↦2}, {dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}], 3),
 ([{dst↦4,pt↦5,sw↦2}, {dst↦4,pt↦1,sw↦2}, {dst↦4,pt↦0,sw↦0}], 3)}
-/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄, 2, [pk[dst ↦ H₄]]] {
  dst = H₄;   dup; (~p; ~l; dup)*; ~p;   true
}

def p' {𝒮 : Type} : Policy[Fields,𝒮] := wnk_policy {
  if dst = H₄ then pt ← 2 ⨁ pt ← 3 ⨁ pt ← 5 else
  if dst = H₃ then pt ← 3 ⨁ pt ← 5 else
  if dst = H₂ then pt ← 2 ⨁ pt ← 5 else
  drop
}
example (𝒮) : p (𝒮:=𝒮) = p' := by rfl
def l' {𝒮 : Type} : Policy[Fields,𝒮] := wnk_policy {
  if pt = 2 then sw ← S₂ ; pt ← 1 else
  if pt = 3 then sw ← S₃ ; pt ← 1 else
  if pt = 5 then sw ← S₅ ; pt ← 1 else
  drop
}
example (𝒮) : l (𝒮:=𝒮) = l' := by rfl
