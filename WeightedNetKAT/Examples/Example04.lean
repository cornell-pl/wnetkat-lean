import WeightedNetKAT.Examples.Common
import WeightedNetKAT.WNKA

namespace WeightedNetKAT

open Weighted (Bottleneck)

open Fields

/--
info: ι := [♡ = ⊤]
δ := []
𝓁 := [[♡ = ⊤ [0, 0];[0, 0]], [♡ = ⊤ [1, 0];[1, 0]], [♡ = ⊤ [0, 1];[0, 1]], [♡ = ⊤ [1, 1];[1, 1]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { skip }

#wnka_dot[Fin 2, Fin 2, Bottleneck] { skip }

#wnka_eval[Fin 2, Fin 2, Bottleneck] { (3 ⨀ skip)* }

/-- info: some 1 -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* } ( gs[pk[];pk[]] )
/-- info: some 3 -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* } ( gs[pk[];pk[];dup;pk[]] )
/-- info: some 9 -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* } ( gs[pk[];pk[];dup;pk[];dup;pk[]] )
/-- info: some 27 -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* } ( gs[pk[];pk[];dup;pk[];dup;pk[];dup;pk[]] )

/-- info: some 0 -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ skip)* } ( gs[pk[];pk[];dup;pk[];dup;pk[];dup;pk[]] )
/-- info: none -/
#guard_msgs in
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ skip)* } ( gs[pk[];pk[]] )

-- TODO: precedence of 3 ⨀ dup ⨁ 2 ⨀ dup

#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { ((3 ⨀ dup) ⨁ 2 ⨀ dup)* } ( gs[pk[];pk[];dup;pk[]] )
#wnka_eval_str[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* ⨁ (skip*) } ( gs[pk[];pk[];dup;pk[]] )

#wnka_eval_str[Fin 1, Fin 2, ℕ∞] {
    ((@test ~pk[0 ↦ 1] ; 3 ⨀ @mod ~pk[0 ↦ 0]) ⨁
     (@test ~pk[0 ↦ 1] ; 2 ⨀ @mod ~pk[0 ↦ 1]))*
  } (
    gs[pk[0 ↦ 1];pk[]]
  )

inductive Alpha where | a | b | c | d
deriving DecidableEq, Fintype

instance : Repr Alpha where
  reprPrec n _ := match n with
  | .a => "a"
  | .b => "b"
  | .c => "c"
  | .d => "d"

instance : Listed Alpha where
  list := [.a, .b, .c, .d]
  nodup := by simp
  complete := by sorry

#wnka_eval_str[Fin 1, Fin 2, (RegularExpression Alpha)] {
    ((~(.char .a) ⨀ (@mod ~pk[0 ↦ 0])) ⨁
    (~(.char .b) ⨀ (@mod ~pk[0 ↦ 1])))*
  } (
    gs[pk[];pk[]]
    -- gs[pk[];pk[];dup;pk[]]
  )

/--
info: {((![0], []), some 1),
 ((![0], [![0]]), some 1),
 ((![0], [![0], ![0]]), some 1),
 ((![0], [![0], ![0], ![0]]), some 1),
 ((![0], [![0], ![0], ![0], ![0]]), some 1),
 ((![0], [![0], ![0], ![0], ![0], ![0]]), some 1)}
-/
#guard_msgs in
#wnk_eval[ℕ∞, 6, ⟨(pk[] : Pk[Fin 1, Fin 2]), []⟩] {
  dup*
}

/--
info: {((![0], []), some 1),
 ((![0], [![0]]), some 3),
 ((![0], [![0], ![0]]), some 9),
 ((![0], [![0], ![0], ![0]]), some 27),
 ((![0], [![0], ![0], ![0], ![0]]), some 81),
 ((![0], [![0], ![0], ![0], ![0], ![0]]), some 243)}
-/
#guard_msgs in
#wnk_eval[ℕ∞, 6, ⟨(pk[] : Pk[Fin 1, Fin 2]), []⟩] {
  (3 ⨀ dup)*
}

-- ι p ⊠ λ p = fun α β ↦ ι p × λ p α β
#wnka_eval_str[Fin 2, Fin 2, ℕ∞] { (3 ⨀ dup) } ( ⟨pk[], [], pk[]⟩ )
#wnka_eval[Fin 1, Fin 2, ℕ∞] { (3 ⨀ dup)* }

#wnka_eval[Fin 2, Fin 2, Bottleneck] { (3 ⨀ dup)* }

#wnka_eval'[Fin 1, Fin 1, Bottleneck] {
    -- skip; dup
    if 0 = 0 then 2 ⨀ 1 ← 0; 0 ← 1 else
    if 0 = 1 then 4 ⨀ 1 ← 1; 0 ← 1 else drop
  }


/--
info: ι := [ll♡ = ⊤, lrl♡ = ⊤, lrrl♡ = ⊤, lrrrl♡ = ⊤, lrrrr♡ = ⊤]
δ := []
𝓁 := [[rlll♡ = ⊤ [0, 0, 0];[0, 0, 1], rllr♡ = ⊤ [0, 0, 0];[0, 0, 1], rlrrrrlr♡ = ⊤ [0, 0, 0];[0, 0, 1]],
 [rlrlr♡ = ⊤ [0, 0, 0];[1, 0, 1], rlrrrrrlr♡ = ⊤ [0, 0, 0];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [0, 0, 0];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [0, 0, 0];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [0, 0, 0];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [0, 0, 0];[1, 1, 1]],
 [rllr♡ = ⊤ [1, 0, 0];[0, 0, 1], rlrrrrlr♡ = ⊤ [1, 0, 0];[0, 0, 1]],
 [rlrll♡ = ⊤ [1, 0, 0];[1, 0, 1], rlrlr♡ = ⊤ [1, 0, 0];[1, 0, 1], rlrrrrrlr♡ = ⊤ [1, 0, 0];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [1, 0, 0];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [1, 0, 0];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [1, 0, 0];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [1, 0, 0];[1, 1, 1]],
 [rllr♡ = ⊤ [0, 1, 0];[0, 0, 1], rlrrrrlr♡ = ⊤ [0, 1, 0];[0, 0, 1]],
 [rlrlr♡ = ⊤ [0, 1, 0];[1, 0, 1], rlrrrrrlr♡ = ⊤ [0, 1, 0];[1, 0, 1]],
 [ll♡ = 2 [0, 1, 0];[0, 1, 1],
  rlrrll♡ = ⊤ [0, 1, 0];[0, 1, 1],
  rlrrlr♡ = ⊤ [0, 1, 0];[0, 1, 1],
  rlrrrrrrlr♡ = ⊤ [0, 1, 0];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [0, 1, 0];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [0, 1, 0];[1, 1, 1]],
 [rllr♡ = ⊤ [1, 1, 0];[0, 0, 1], rlrrrrlr♡ = ⊤ [1, 1, 0];[0, 0, 1]],
 [rlrlr♡ = ⊤ [1, 1, 0];[1, 0, 1], rlrrrrrlr♡ = ⊤ [1, 1, 0];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [1, 1, 0];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [1, 1, 0];[0, 1, 1]],
 [lrl♡ = 2 [1, 1, 0];[1, 1, 1],
  rlrrrll♡ = ⊤ [1, 1, 0];[1, 1, 1],
  rlrrrlr♡ = ⊤ [1, 1, 0];[1, 1, 1],
  rlrrrrrrrlr♡ = ⊤ [1, 1, 0];[1, 1, 1]],
 [rllr♡ = ⊤ [0, 0, 1];[0, 0, 1], rlrrrrll♡ = ⊤ [0, 0, 1];[0, 0, 1], rlrrrrlr♡ = ⊤ [0, 0, 1];[0, 0, 1]],
 [rlrlr♡ = ⊤ [0, 0, 1];[1, 0, 1], rlrrrrrlr♡ = ⊤ [0, 0, 1];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [0, 0, 1];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [0, 0, 1];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [0, 0, 1];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [0, 0, 1];[1, 1, 1]],
 [rllr♡ = ⊤ [1, 0, 1];[0, 0, 1], rlrrrrlr♡ = ⊤ [1, 0, 1];[0, 0, 1]],
 [rlrlr♡ = ⊤ [1, 0, 1];[1, 0, 1], rlrrrrrll♡ = ⊤ [1, 0, 1];[1, 0, 1], rlrrrrrlr♡ = ⊤ [1, 0, 1];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [1, 0, 1];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [1, 0, 1];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [1, 0, 1];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [1, 0, 1];[1, 1, 1]],
 [rllr♡ = ⊤ [0, 1, 1];[0, 0, 1], rlrrrrlr♡ = ⊤ [0, 1, 1];[0, 0, 1]],
 [rlrlr♡ = ⊤ [0, 1, 1];[1, 0, 1], rlrrrrrlr♡ = ⊤ [0, 1, 1];[1, 0, 1]],
 [lrrl♡ = 2 [0, 1, 1];[0, 1, 1],
  rlrrlr♡ = ⊤ [0, 1, 1];[0, 1, 1],
  rlrrrrrrll♡ = ⊤ [0, 1, 1];[0, 1, 1],
  rlrrrrrrlr♡ = ⊤ [0, 1, 1];[0, 1, 1]],
 [rlrrrlr♡ = ⊤ [0, 1, 1];[1, 1, 1], rlrrrrrrrlr♡ = ⊤ [0, 1, 1];[1, 1, 1]],
 [rllr♡ = ⊤ [1, 1, 1];[0, 0, 1], rlrrrrlr♡ = ⊤ [1, 1, 1];[0, 0, 1]],
 [rlrlr♡ = ⊤ [1, 1, 1];[1, 0, 1], rlrrrrrlr♡ = ⊤ [1, 1, 1];[1, 0, 1]],
 [rlrrlr♡ = ⊤ [1, 1, 1];[0, 1, 1], rlrrrrrrlr♡ = ⊤ [1, 1, 1];[0, 1, 1]],
 [lrrrl♡ = 2 [1, 1, 1];[1, 1, 1],
  rlrrrlr♡ = ⊤ [1, 1, 1];[1, 1, 1],
  rlrrrrrrrll♡ = ⊤ [1, 1, 1];[1, 1, 1],
  rlrrrrrrrlr♡ = ⊤ [1, 1, 1];[1, 1, 1]]]
-/
#guard_msgs in
#wnka_eval'[Fields, Fin 2, Bottleneck] {
  if pt = 3 then ~2 ⨀ sw ← 3 else drop
  -- if pt = 4 then ~4 ⨀ sw ← 4 else drop
}

/--
info: ι := [l♡ = ⊤, r♡ = ⊤]
δ := []
𝓁 := [[l♡ = ⊤ [0, 0];[0, 0]]]
-/
#guard_msgs in
#wnka_eval'[Fin 2, Fin 1, Bottleneck] { ~1 = ~1 }

/--
info: ι := [♡ = ⊤]
δ := [[♡ -> ♣ = ⊤ [0, 0];[0, 0]], [♡ -> ♣ = ⊤ [1, 0];[1, 0]], [♡ -> ♣ = ⊤ [0, 1];[0, 1]], [♡ -> ♣ = ⊤ [1, 1];[1, 1]]]
𝓁 := [[♣ = ⊤ [0, 0];[0, 0]], [♣ = ⊤ [1, 0];[1, 0]], [♣ = ⊤ [0, 1];[0, 1]], [♣ = ⊤ [1, 1];[1, 1]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { dup }

/--
info: ι := [♡ = 10]
δ := [[♡ -> ♣ = ⊤ [0, 0];[0, 0]], [♡ -> ♣ = ⊤ [1, 0];[1, 0]], [♡ -> ♣ = ⊤ [0, 1];[0, 1]], [♡ -> ♣ = ⊤ [1, 1];[1, 1]]]
𝓁 := [[♣ = ⊤ [0, 0];[0, 0]], [♣ = ⊤ [1, 0];[1, 0]], [♣ = ⊤ [0, 1];[0, 1]], [♣ = ⊤ [1, 1];[1, 1]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { ~10 ⨀ dup }

/--
info: ι := [l♡ = ⊤]
δ := [[l♡ -> r♣ = 10 [0, 0];[0, 0], r♡ -> r♣ = ⊤ [0, 0];[0, 0]],
 [l♡ -> r♣ = 10 [1, 0];[1, 0], r♡ -> r♣ = ⊤ [1, 0];[1, 0]],
 [l♡ -> r♣ = 10 [0, 1];[0, 1], r♡ -> r♣ = ⊤ [0, 1];[0, 1]],
 [l♡ -> r♣ = 10 [1, 1];[1, 1], r♡ -> r♣ = ⊤ [1, 1];[1, 1]]]
𝓁 := [[r♣ = ⊤ [0, 0];[0, 0]], [r♣ = ⊤ [1, 0];[1, 0]], [r♣ = ⊤ [0, 1];[0, 1]], [r♣ = ⊤ [1, 1];[1, 1]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { skip ; ~10 ⨀ dup }

/--
info: ι := [♡ = ⊤]
δ := []
𝓁 := [[♡ = ⊤ [0, 0];[1, 0]], [♡ = ⊤ [1, 0];[1, 0]], [♡ = ⊤ [0, 1];[1, 0]], [♡ = ⊤ [1, 1];[1, 0]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { @mod ~pk[0 ↦ 1] }

/--
info: ι := [l♡ = ⊤, r♡ = ⊤]
δ := []
𝓁 := [[l♡ = ⊤ [0, 0];[1, 0]],
 [r♡ = ⊤ [0, 0];[0, 1]],
 [l♡ = ⊤ [1, 0];[1, 0]],
 [r♡ = ⊤ [1, 0];[0, 1]],
 [l♡ = ⊤ [0, 1];[1, 0]],
 [r♡ = ⊤ [0, 1];[0, 1]],
 [l♡ = ⊤ [1, 1];[1, 0]],
 [r♡ = ⊤ [1, 1];[0, 1]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { @mod ~pk[0 ↦ 1] ⨁ @mod ~pk[1 ↦ 1] }

/--
info: ι := [ll♡ = ⊤, lr♡ = ⊤]
δ := [[rl♡ -> rl♣ = ⊤ [0, 0];[0, 0]],
 [ll♡ -> rl♣ = ⊤ [0, 0];[1, 0]],
 [lr♡ -> rl♣ = ⊤ [0, 0];[0, 1]],
 [ll♡ -> rl♣ = ⊤ [1, 0];[1, 0], rl♡ -> rl♣ = ⊤ [1, 0];[1, 0]],
 [lr♡ -> rl♣ = ⊤ [1, 0];[0, 1]],
 [ll♡ -> rl♣ = ⊤ [0, 1];[1, 0]],
 [lr♡ -> rl♣ = ⊤ [0, 1];[0, 1], rl♡ -> rl♣ = ⊤ [0, 1];[0, 1]],
 [ll♡ -> rl♣ = ⊤ [1, 1];[1, 0]],
 [lr♡ -> rl♣ = ⊤ [1, 1];[0, 1]],
 [rl♡ -> rl♣ = ⊤ [1, 1];[1, 1]]]
𝓁 := [[rl♣ = ⊤ [1, 0];[1, 0], rr♡ = ⊤ [1, 0];[1, 0]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] {
  (@mod ~pk[0 ↦ 1] ⨁ @mod ~pk[1 ↦ 1]) ; dup ; @test ~pk[0 ↦ 1]
}

/--
info: ι := [l♡ = ⊤]
δ := [[l♡ -> rll♣ = ⊤ [0, 0];[0, 0], rll♡ -> rll♣ = ⊤ [0, 0];[0, 0]],
 [l♡ -> rll♣ = ⊤ [1, 0];[1, 0], rll♡ -> rll♣ = ⊤ [1, 0];[1, 0]],
 [l♡ -> rll♣ = ⊤ [0, 1];[0, 1], rll♡ -> rll♣ = ⊤ [0, 1];[0, 1]],
 [l♡ -> rll♣ = ⊤ [1, 1];[1, 1], rll♡ -> rll♣ = ⊤ [1, 1];[1, 1]]]
𝓁 := [[rll♣ = 1 [0, 0];[0, 0],
  rlrr♡ = ⊤ [0, 0];[0, 0],
  rrl♡ = ⊤ [0, 0];[0, 0],
  rrrl♡ = ⊤ [0, 0];[0, 0],
  rrrr♡ = ⊤ [0, 0];[0, 0]]]
-/
#guard_msgs in
#wnka_eval[Fin 2, Fin 2, Bottleneck] { skip; (dup; @mod ~pk[0 ↦ 1] ⨁ ~1 ⨀ skip); skip; skip; @test ~pk[0 ↦ 0] }

end WeightedNetKAT
