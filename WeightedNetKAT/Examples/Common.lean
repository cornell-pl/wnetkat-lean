import Mathlib.Logic.Encodable.Pi
import WeightedNetKAT.Computation
import WeightedNetKAT.WNKA
import WeightedNetKAT.Instances.Boolean
import WeightedNetKAT.Instances.Bottleneck

namespace WeightedNetKAT

inductive Fields where
  | dst | pt | sw
deriving DecidableEq

open Fields

instance : Fintype Fields where
  elems := {dst, pt, sw}
  complete x := by cases x <;> simp

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

def Network {F N 𝒮 : Type} (ingress : Predicate[F,N]) (p l : Policy[F,N,𝒮]) (egress : Predicate[F,N]) :
    Policy[F,N,𝒮] :=
  wnk_policy { @filter ~ingress; dup; (~p; ~l; dup)*; ~p; @filter ~egress }

syntax "#wnk_eval[" term "," term ("," term)? "]" "{" cwnk_policy "}" : command

macro_rules
| `(#wnk_eval[$S, $n] { $p }) => `(#wnk_eval[$S, $n, [0]] { $p })
| `(#wnk_eval[$S, $n, $h] { $p }) => `(#eval wnk_policy { $p }.compute (𝒮:=$S) $n $h |>.pretty)

def S.repr {F N 𝒮 : Type} {p : RPol[F,N,𝒮]} (s : S p) : String :=
  match p with
  | wnk_rpol { drop } => "♡"
  | wnk_rpol { skip } => "♡"
  | wnk_rpol { @test ~_ } => "♡"
  | wnk_rpol { @mod ~_ } => "♡"
  | wnk_rpol { dup } =>
    match s.1 with
    | ♡ => "♡"
    | ♣ => "♣"
  | wnk_rpol { ¬~_ } => "♡"
  | wnk_rpol { ~_ ⨁ ~_ } =>
    match s with
    | .inl x => s!"l{x.repr}"
    | .inr x => s!"r{x.repr}"
  | wnk_rpol { ~_ ; ~_ } =>
    match s with
    | .inl x => s!"l{x.repr}"
    | .inr x => s!"r{x.repr}"
  | wnk_rpol { ~_ ⨀ ~p₁ } => let s' : S p₁ := s; s'.repr
  | wnk_rpol { ~p₁* } => let s' : S p₁ := s; s'.repr

instance {F N 𝒮 : Type} {p : RPol[F,N,𝒮]} : Repr (S p) where
  reprPrec s _ := s.repr

instance {X : Type} [Repr X] : Repr (Unit × X) where
  reprPrec x n := reprPrec x.2 n
instance {X : Type} [Repr X] : Repr (X × Unit) where
  reprPrec x n := reprPrec x.1 n

def Pk.all (F N : Type) [Fintype F] [DecidableEq F] [Fintype N] : Finset Pk[F,N] := Fintype.elems
def Pk.pairs (F N : Type) [Fintype F] [DecidableEq F] [Fintype N] : Finset (Pk[F,N] × Pk[F,N]) := Fintype.elems

unsafe def RPol.eval {F N 𝒮 : Type} [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [WeightedSemiring 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] (p : RPol[F,N,𝒮]) :=
  let N := p.wnka
  let ι := N.ι
  let δ := Pk.pairs _ _ |>.val.unquot.map (fun (α, β) ↦ (α, β, N.δ α β)) |>.filter (·.2.2.finSupp ≠ ∅)
  let 𝓁 := Pk.pairs _ _ |>.val.unquot.map (fun (α, β) ↦ (α, β, N.𝓁 α β)) |>.filter (·.2.2.finSupp ≠ ∅)
  (ι, δ, 𝓁)

syntax "#wnka_eval[" term "," term "," term "]" "{" cwnk_rpol "}" : command

macro_rules
| `(#wnka_eval[$f, $n, $s] { $p }) => `(#eval wnk_rpol { $p }.eval (F:=$f) (N:=$n) (𝒮:=$s))

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

syntax "|" cwnk_pred "↦" cwnk_policy : cwnk_match_case
syntax "|" "_" "↦" cwnk_policy : cwnk_match_case
syntax "|" cwnk_pred "=>" cwnk_policy : cwnk_match_case
syntax "|" "_" "=>" cwnk_policy : cwnk_match_case

syntax "match" cwnk_match_case* : cwnk_policy

macro_rules
| `(wnk_policy { match $cases:cwnk_match_case* }) => do
  let p := ← cases.foldrM (β:=Lean.TSyntax `cwnk_policy) (fun y x ↦
    match y with
    | `(cwnk_match_case|| $t ↦ $p) | `(cwnk_match_case|| $t => $p) =>
      `(cwnk_policy|if $t then $p else $x)
    | `(cwnk_match_case|| _ ↦ $p) | `(cwnk_match_case|| _ => $p) =>
      pure p
    | _ => return x
    ) (← `(cwnk_policy|drop))
  `(wnk_policy {$p})

end WeightedNetKAT
