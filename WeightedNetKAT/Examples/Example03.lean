import WeightedNetKAT.Examples.Common

open Fields

/-! Example showing the `match`-syntax sugar. -/

def p {𝒮 : Type} : Policy[Fields,𝒮] := wnk_policy {
  match
  | dst = H₂ ↦ pt ← 3 ⨁ pt ← 4
  | dst = H₁ ↦ pt ← 1
}
def l {𝒮 : Type} [OfNat 𝒮 2] : Policy[Fields,𝒮] := wnk_policy {
  match
  | pt = 2 ↦ 2 ⨀ sw ← S₂ ; pt ← 1
  | pt = 3 ↦ sw ← S₃ ; pt ← 1
  | pt = 5 ↦ sw ← S₅ ; pt ← 1
}

/--
info: {([{dst↦2,pt↦3,sw↦0}, {dst↦2,pt↦0,sw↦0}], H), ([{dst↦2,pt↦4,sw↦0}, {dst↦2,pt↦0,sw↦0}], H)}
-/
#guard_msgs in
#wnk_eval[Bottleneck Secutiy₄, 2, [pk[dst ↦ H₂]]] {
  dst = H₂;   dup; (~p; ~l; dup)*; ~p;   true
}

/-- info: ∅ -/
#guard_msgs in
#wnk_eval[Bottleneck ℕ∞, 2, [pk[dst ↦ H₄]]] {
  dst = H₄;   dup; (~p; ~l; dup)*; ~p;   true
}
