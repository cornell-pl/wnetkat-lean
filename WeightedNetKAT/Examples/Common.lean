import WeightedNetKAT.Computation
import WeightedNetKAT.Instances.Bottleneck
import Mathlib.Logic.Encodable.Pi

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

def Network {F 𝒮 : Type} (ingress : Predicate[F]) (p l : Policy[F,𝒮]) (egress : Predicate[F]) :
    Policy[F,𝒮] :=
  wnk_policy { @filter ~ingress; dup; (~p; ~l; dup)*; ~p; @filter ~egress }

syntax "#wnk_eval[" term "," term ("," term)? "]" "{" cwnk_policy "}" : command

macro_rules
| `(#wnk_eval[$S, $n] { $p }) => `(#wnk_eval[$S, $n, [0]] { $p })
| `(#wnk_eval[$S, $n, $h] { $p }) => `(#eval wnk_policy { $p }.compute (𝒮:=$S) $n $h |>.pretty)

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
