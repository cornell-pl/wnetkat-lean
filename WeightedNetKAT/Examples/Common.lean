module

public import Mathlib.Logic.Encodable.Pi
public import WeightedNetKAT.Computation
public import WeightedNetKAT.WNKA.Explicit
public import WeightedNetKAT.WeightedSemiring.Instances

@[expose] public section

open MatrixNotation

namespace WeightedNetKAT

inductive Fields where
  | dst | pt | sw
deriving DecidableEq, Fintype

open Fields

instance : Listed Fields where
  array := #[dst, pt, sw]
  nodup := by simp [Array.Nodup, Array.Pairwise]
  complete := by intro a; cases a <;> simp
  encode | dst => 0 | pt => 1 | sw => 2

instance : Encodable Fields where
  encode f := match f with | dst => 0 | pt => 1 | sw => 2
  decode n := match n with | 0 => some dst | 1 => some pt | 2 => some sw | _ => none
  encodek x := by cases x <;> simp

instance : Repr Fields where
  reprPrec f _ := match f with | dst => "dst" | pt => "pt" | sw => "sw"

abbrev H₁ := 1
abbrev H₂ := 2
abbrev H₃ := 3
abbrev H₄ := 4

abbrev S₂ := 2
abbrev S₃ := 3
abbrev S₄ := 4
abbrev S₅ := 5

def Network {F N 𝒮 : Type*} (ingress : Pred[F,N]) (p l : Pol[F,N,𝒮]) (egress : Pred[F,N]) :
    Pol[F,N,𝒮] :=
  wnk_pol { @filter ~ingress; dup; (~p; ~l; dup)*; ~p; @filter ~egress }

syntax "#wnk_eval[" term "," term ("," term)? "]" "{" cwnk_pol "}" : command

macro_rules
| `(#wnk_eval[$S, $n] { $p }) => `(#wnk_eval[$S, $n, ⟨0, []⟩] { $p })
| `(#wnk_eval[$S, $n, $h] { $p }) => `(#eval! wnk_pol { $p }.compute (𝒮:=$S) $n $h |>.pretty)

def S.repr {F N 𝒮 : Type*} [Listed F] {p : RPol[F,N,𝒮]} (s : S p) : String :=
  match p with
  | wnk_rpol { drop } => "♡"
  | wnk_rpol { skip } => "♡"
  | wnk_rpol { @test ~_ } => "♡"
  | wnk_rpol { @mod ~_ } => "♡"
  | wnk_rpol { dup } =>
    match s with
    | ♡ => "♡"
    | ♣ => "♣"
  | wnk_rpol { ~_ ⨁ ~_ } =>
    match s with
    | .inl x => s!"l{x.repr}"
    | .inr x => s!"r{x.repr}"
  | wnk_rpol { ~_ ; ~_ } =>
    match s with
    | .inl x => s!"l{x.repr}"
    | .inr x => s!"r{x.repr}"
  | wnk_rpol { ~_ ⨀ ~p₁ } => let s' : S p₁ := s; s'.repr
  | wnk_rpol { ~p₁* } =>
    match s with
    | .inl s => let s' : S p₁ := s; s'.repr
    | .inr () => "♡*"

instance {F N 𝒮 : Type*} [Listed F] {p : RPol[F,N,𝒮]} : Repr (S p) where
  reprPrec s _ := s.repr

instance {X : Type*} [Repr X] : Repr (Unit × X) where
  reprPrec x n := reprPrec x.2 n
instance {X : Type*} [Repr X] : Repr (X × Unit) where
  reprPrec x n := reprPrec x.1 n

def RPol.eval {F N 𝒮 : Type*}
    [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [Listed F] [Listed N] [Inhabited N]
    [Semiring 𝒮] [DecidableEq 𝒮] [KStar 𝒮] [Repr 𝒮] [Repr F] [Repr N] (p : RPol[F,N,𝒮]) :
    IO Std.Format := do
  println! "computing wnka"
  let n : EWNKA F N 𝒮 (S p) := p.ewnka
  println! "accessing ι"
  let ι := n.ι
  println! "accessing δ"
  let δ : List (Pk[F,N] × Pk[F,N] × EMatrix (S p) (S p) 𝒮) := (Listed.listOf (Pk[F,N] × Pk[F,N])).map (fun (α, β) ↦ (α, β, n.δ.get α β)) -- |>.filter (·.2.2 ≠ 0)
  println! "accessing 𝓁"
  let 𝓁 : List (Pk[F,N] × Pk[F,N] × EMatrix (S p) (𝟙) 𝒮) := (Listed.listOf (Pk[F,N] × Pk[F,N])).map (fun (α, β) ↦ (α, β, n.𝒪.get α β)) -- |>.filter (·.2.2 ≠ 0)
  println! "fin"

  println! "start \{"
  println! "  ι := {reprStr ι.data}"
  println! "  𝓁 := {reprStr (𝓁.map (reprStr ·.2.2.data))}"
  println! "  δ := {reprStr (δ.map (reprStr ·.2.2.data))}"
  println! "} end"

  let q : Pk[F,N] → String := fun x ↦ reprStr <| Listed.array.map x

  let ιp := Listed.listOf (S p) |>.filter (ι.get () · ≠ 0) |>.map (fun s ↦ s!"{reprStr s} = {reprStr (ι.get () s)}")
  println! "computed ιp"
  let δp := δ.map (fun (α, β, x) ↦
    Listed.listOf (S p × S p) |>.filter (fun (s, s') ↦ x.get s s' ≠ 0) |>.map (fun (s, s') ↦ s!"{reprStr s} -> {reprStr s'} = {reprStr (x.get s s')} {q α};{q β}")
  )
  println! "computed δp"
  let 𝓁p := 𝓁.map (fun (α, β, x) ↦
    Listed.listOf (S p) |>.filter (x.get · () ≠ 0) |>.map (fun s ↦ s!"{reprStr s} = {reprStr (x.get s ())} {q α};{q β}")
  )
  println! "computed 𝓁p"

  return f!"ι := {ιp}\nδ := {δp}\n𝓁 := {𝓁p}"

  -- (ι, δ, 𝓁)

def RPol.eval_string {F N 𝒮 : Type*}
    [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [Listed F] [Listed N] [Inhabited N]
    [Semiring 𝒮] [DecidableEq 𝒮] [KStar 𝒮] (p : RPol[F,N,𝒮]) (s : GS[F,N])
    :=
      p.ewnka.sem s

instance myRepr {α A B : Type*} [DecidableEq α] [Zero α] [DecidableEq A] [DecidableEq B]
    [Listed A] [Listed B] [Repr α] [Repr A] [Repr B] : Repr 𝕄[A, B, α] where
  reprPrec m n :=
    reprPrec (Listed.listOf (A × B) |>.filter (fun (a, b) ↦ m a b ≠ 0) |>.map (fun (a, b) ↦ s!"{reprStr a},{reprStr b}↦{reprStr (m a b)}")) n

instance {F N 𝒮 : Type*}
    [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [Listed F] [Listed N] [Inhabited N]
    [Listed Pk[F,N]]
    [Semiring 𝒮] [DecidableEq 𝒮] [KStar 𝒮] [Repr 𝒮] [Repr F] [Repr N] (p : RPol[F,N,𝒮]) :
    Repr (WNKA F N 𝒮 (S p)) where
  reprPrec m _ :=
    let ι := m.ι
    let δ : List (Pk[F,N] × Pk[F,N] × 𝕄[S p, S p, 𝒮]) := (Listed.listOf (Pk[F,N] × Pk[F,N])).map (fun (α, β) ↦ (α, β, m.δ α β)) |>.filter (·.2.2 ≠ 0)
    let 𝓁 : List (Pk[F,N] × Pk[F,N] × 𝕄[S p, 𝟙, 𝒮]) := (Listed.listOf (Pk[F,N] × Pk[F,N])).map (fun (α, β) ↦ (α, β, m.𝒪 α β)) |>.filter (·.2.2 ≠ 0)

    let q : Pk[F,N] → String := fun x ↦ reprStr <| Listed.array.map x

    -- reprPrec (Listed.listOf (A × B) |>.map (fun (a, b) ↦ s!"≫{reprStr a},{reprStr b}↦{reprStr (m a b)}")) n

    let x :=
        Listed.listOf (S p) |>.filter (ι () · ≠ 0) |>.map (fun s ↦ s!"{reprStr s} [label=\"{reprStr s} {reprStr (ι () s)}\"]")
    let y :=
        δ.map (fun (α, β, x) ↦
          Listed.listOf (S p × S p) |>.filter (fun (s, s') ↦ x s s' ≠ 0) |>.map (fun (s, s') ↦ s!"{reprStr s} -> {reprStr s'} [label=\"{reprStr (x s s')} {q α};{q β}\"]")
        )
    let z :=
        𝓁.map (fun (α, β, x) ↦
          Listed.listOf (S p) |>.filter (x · () ≠ 0) |>.map (fun s ↦ s!"{reprStr s} -> F{reprStr s} [label=\"{reprStr (x s ())} {q α};{q β}\"]")
        )

    f!"{x ++ y.flatten ++ z.flatten |> "\n".intercalate}"
    -- f!"ι := {
    --     Listed.listOf (S p) |>.filter (ι () · ≠ 0) |>.map (fun s ↦ s!"{reprStr s} = {reprStr (ι () s)}")
    --   }\nδ := {
    --     δ.map (fun (α, β, x) ↦
    --       Listed.listOf (S p × S p) |>.filter (fun (s, s') ↦ x s s' ≠ 0) |>.map (fun (s, s') ↦ s!"{reprStr s} -> {reprStr s'} = {reprStr (x s s')} {q α};{q β}")
    --     )
    --   }\n𝓁 := {
    --     𝓁.map (fun (α, β, x) ↦
    --       Listed.listOf (S p) |>.filter (x · () ≠ 0) |>.map (fun s ↦ s!"{reprStr s} = {reprStr (x s ())} {q α};{q β}")
    --     )
    --   }"

syntax "#wnka_eval[" term "," term "," term "]" "{" cwnk_rpol "}" : command

macro_rules
| `(#wnka_eval[$f, $n, $s] { $p }) => `(#eval! wnk_rpol { $p }.eval (F:=$f) (N:=$n) (𝒮:=$s))

syntax "#wnka_dot[" term "," term "," term "]" "{" cwnk_rpol "}" : command

macro_rules
| `(#wnka_dot[$f, $n, $s] { $p }) => `(#eval! wnk_rpol { $p }.wnka (F:=$f) (N:=$n) (𝒮:=$s))

syntax "#wnka_eval_str[" term "," term "," term "]" "{" cwnk_rpol "}" "(" term ")" : command

macro_rules
| `(#wnka_eval_str[$f, $n, $s] { $p } ( $x )) => `(#eval! wnk_rpol { $p }.eval_string (F:=$f) (N:=$n) (𝒮:=$s) $x)

syntax "#wnka_eval'[" term "," term "," term "]" "{" cwnk_pol "}" : command

macro_rules
| `(#wnka_eval'[$f, $n, $s] { $p }) => `(#eval! wnk_pol { $p }.toRPol.eval (F:=$f) (N:=$n) (𝒮:=$s))

declare_syntax_cat pk_entry
syntax term "↦" term : pk_entry
syntax "pk[" pk_entry,* "]" : term

macro_rules
| `(pk[ $ts:pk_entry,* ]) => do
  return ← ts.getElems.foldlM (β:=Lean.TSyntax `term) (fun x y ↦
    match y with
    | `(pk_entry|$k:term ↦ $v) => `(fun a ↦ if a = $k then $v else $x a)
    | _ => return x
    ) (← `(fun _ ↦ 0))

declare_syntax_cat' wnk_match_case
macro_rules|`(wnk_match_case{~$t})=>`($t)

syntax "|" cwnk_pred "↦" cwnk_pol : cwnk_match_case
syntax "|" "_" "↦" cwnk_pol : cwnk_match_case
syntax "|" cwnk_pred "=>" cwnk_pol : cwnk_match_case
syntax "|" "_" "=>" cwnk_pol : cwnk_match_case

syntax "match" cwnk_match_case* : cwnk_pol

macro_rules
| `(wnk_pol { match $cases:cwnk_match_case* }) => do
  let p := ← cases.foldrM (β:=Lean.TSyntax `cwnk_pol) (fun y x ↦
    match y with
    | `(cwnk_match_case|| $t ↦ $p) | `(cwnk_match_case|| $t => $p) =>
      `(cwnk_pol|if $t then $p else $x)
    | `(cwnk_match_case|| _ ↦ $p) | `(cwnk_match_case|| _ => $p) =>
      pure p
    | _ => return x
    ) (← `(cwnk_pol|drop))
  `(wnk_pol {$p})

end WeightedNetKAT
