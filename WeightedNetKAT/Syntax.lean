import WeightedNetKAT.Weightings

namespace WeightedNetKAT

variable {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]

abbrev Pk := F → N
notation "Pk[" F "," N "]" => Pk (F:=F) (N:=N)

abbrev H := List Pk[F,N]
notation "H[" F "," N "]" => H (F:=F) (N:=N)

inductive Predicate where
  | Bool (b : Bool)
  | Test (f : F) (n : N)
  | Dis (t u : Predicate)
  | Con (t u : Predicate)
  | Not (t : Predicate)

notation "Predicate[" F "," N "]" => Predicate (F:=F) (N:=N)

inductive Policy (W : Type) where
  | Filter (t : Predicate[F,N])
  | Mod (f : F) (n : N)
  | Dup
  | Seq (p q : Policy W)
  | Weight (w : W) (p : Policy W)
  | Add (p q : Policy W)
  | Iter (p : Policy W)

notation "Policy[" f "," n "," w "]" => Policy (F:=f) (N:=n) (W:=w)

section Syntax

open Lean Elab PrettyPrinter Delaborator Meta Command Term

syntax (name := declare_syntax_cat') "declare_syntax_cat'" ident : command
syntax (name := declare_syntax_cat'?) "declare_syntax_cat'?" ident : command

macro_rules
| `(declare_syntax_cat' $name) =>
  let cat : TSyntax `ident := mkIdent $ Name.mkSimple s!"c{name.getId.toString}"
  let sname : TSyntax `str := ⟨Syntax.mkStrLit name.getId.toString⟩
  `(declare_syntax_cat $cat
    syntax (name := $cat) $sname:str ppHardSpace "{" $cat:ident "}" : term
    syntax:max "~" term:max : $cat
    )
elab "declare_syntax_cat'?" name:ident : command => do
  let cmd ← `(declare_syntax_cat' $name)
  logWarning s!"Try this: macro_rules|`({Name.mkSimple name.getId.toString}\{~$t})=>`($t)"
  elabCommand cmd

declare_syntax_cat' wnk_field
macro_rules|`(wnk_field{~$t})=>`($t)
declare_syntax_cat' wnk_nat
macro_rules|`(wnk_nat{~$t})=>`($t)
declare_syntax_cat' wnk_weight
macro_rules|`(wnk_weight{~$t})=>`($t)
declare_syntax_cat' wnk_pred
declare_syntax_cat' wnk_policy

syntax term:max : cwnk_field
macro_rules|`(wnk_field{$t:term})=>`($t)
syntax term:max : cwnk_nat
macro_rules|`(wnk_nat{$t:term})=>`($t)
syntax num : cwnk_weight
macro_rules|`(wnk_weight{$t:num})=>`($t)

syntax num : cwnk_nat

macro_rules
| `(wnk_nat { $n:num }) => `($n)

syntax ident : cwnk_pred
syntax cwnk_field " = " cwnk_nat : cwnk_pred
syntax cwnk_pred " ∨ " cwnk_pred : cwnk_pred
-- TODO: we need this, but we need to fix the precedence so it doens't interfere with Policy.Seq
-- syntax cwnk_pred "; " cwnk_pred : cwnk_pred
syntax "¬" cwnk_pred : cwnk_pred
syntax "(" cwnk_pred ")" : cwnk_pred

macro_rules
| `(wnk_pred { true }) => `(Predicate.Bool true)
| `(wnk_pred { false }) => `(Predicate.Bool false)
| `(wnk_pred { $f:cwnk_field = $n:cwnk_nat }) => `(Predicate.Test wnk_field {$f} wnk_nat {$n})
| `(wnk_pred { $l:cwnk_pred ∨ $r:cwnk_pred }) => `(Predicate.Dis wnk_pred {$l} wnk_pred {$r})
-- | `(wnk_pred { $l:cwnk_pred ; $r:cwnk_pred }) => `(Predicate.And wnk_pred {$l} wnk_pred {$r})
| `(wnk_pred { ¬$l:cwnk_pred }) => `(Predicate.Not wnk_pred {$l})
| `(wnk_pred { ($t) }) => `(wnk_pred {$t})


syntax cwnk_pred:min : cwnk_policy
syntax cwnk_field " ← " cwnk_nat : cwnk_policy
syntax "dup" : cwnk_policy
syntax cwnk_policy "; " cwnk_policy : cwnk_policy
syntax cwnk_weight " ⨀ " cwnk_policy : cwnk_policy
syntax cwnk_policy " ⨁ " cwnk_policy : cwnk_policy
syntax cwnk_policy "*" : cwnk_policy
syntax "(" cwnk_policy ")" : cwnk_policy
syntax "@filter" ppHardSpace cwnk_pred:min : cwnk_policy

-- Sugar

syntax "skip" : cwnk_policy
syntax "drop" : cwnk_policy
syntax "if" ppHardSpace cwnk_pred ppHardSpace "then"
  ppHardSpace cwnk_policy ppHardSpace "else" ppHardSpace cwnk_policy : cwnk_policy
syntax "while" ppHardSpace cwnk_pred ppHardSpace "do"
  ppHardSpace cwnk_policy : cwnk_policy

macro_rules
| `(wnk_policy { $t:cwnk_pred }) => `(Policy.Filter wnk_pred {$t})
| `(wnk_policy { @filter $t:cwnk_pred }) => `(Policy.Filter wnk_pred {$t})
| `(wnk_policy { $p:cwnk_field ← $q:cwnk_nat }) => `(Policy.Mod wnk_field {$p} wnk_nat {$q})
| `(wnk_policy { dup }) => `(Policy.Dup)
| `(wnk_policy { $p ; $q }) => `(Policy.Seq wnk_policy {$p} wnk_policy {$q})
| `(wnk_policy { $w:cwnk_weight ⨀ $p }) => `(Policy.Weight wnk_weight {$w} wnk_policy {$p})
| `(wnk_policy { $p ⨁ $q }) => `(Policy.Add wnk_policy {$p} wnk_policy {$q})
| `(wnk_policy { $p * }) => `(Policy.Iter wnk_policy {$p})
| `(wnk_policy { ($t:cwnk_policy) }) => `(wnk_policy {$t})
-- Sugar
| `(wnk_policy { if $t then $p else $q }) => `(wnk_policy { $t:cwnk_pred ; $p ⨁ ¬$t ; $q })
| `(wnk_policy { while $t do $p }) => `(wnk_policy { ($t:cwnk_pred ; $p)* ; ¬$t })
| `(wnk_policy { skip }) => `(wnk_policy { true })
| `(wnk_policy { drop }) => `(wnk_policy { false })

/--
info: (Policy.Filter (Predicate.Test 123 1)).Seq
  ((Policy.Filter ((Predicate.Bool false).Dis (Predicate.Bool true)).Not).Seq
    (Policy.Weight 1 ((Policy.Mod 12 2).Seq (Policy.Dup.Add Policy.Dup.Iter)))) : Policy ℕ
-/
#guard_msgs in
#check wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~1 ⨀ ~12 ← 2 ; dup ⨁ dup* }

macro_rules|`(wnk_pred{~$t})=>`($t)
macro_rules|`(wnk_policy{~$t})=>`($t)

@[app_unexpander Predicate.Bool]
def Predicate.unexpandBool : Unexpander
| `($(_) $x) =>
  match x with
  | `(true)  => let s := mkIdent $ .mkSimple "true";  `(wnk_pred { $s:ident })
  | `(false) => let s := mkIdent $ .mkSimple "false"; `(wnk_pred { $s:ident })
  | _ => throw ()
| _ => throw ()

@[app_unexpander Predicate.Not]
def Predicate.unexpandNot : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  `(wnk_pred { ¬$x })
| _ => throw ()

@[app_unexpander Predicate.Dis]
def Predicate.unexpandDis : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  let y ← match y with
    | `(wnk_pred{$y}) => pure y
    | _ => `(cwnk_pred|~$y)
  `(wnk_pred { $x ∨ $y })
| _ => throw ()

@[app_unexpander Predicate.Test]
def Predicate.unexpandTest : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_field{$x}) => pure x
    | _ => `(cwnk_field|~$x)
  let y ← match y with
    | `(wnk_nat{$y}) => pure y
    | _ => `(cwnk_nat|~$y)
  `(wnk_pred { $x:cwnk_field = $y })
| _ => throw ()

@[app_unexpander Policy.Filter]
def Policy.unexpandFilter : Unexpander
| `($(_) $f) =>
  match f with
  | `(wnk_pred {$f}) => `(wnk_policy {$f:cwnk_pred})
  | _ => throw ()
| _ => throw ()

/-- info: wnk_policy {true} : Policy Unit -/
#guard_msgs in
#check (wnk_policy { true } : Policy Unit)

@[app_unexpander Policy.Dup]
def Policy.unexpandDup : Unexpander
| _ => `(wnk_policy { dup })

@[app_unexpander Policy.Seq]
def Policy.unexpandSeq : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x ; $y })
| _ => throw ()

@[app_unexpander Policy.Mod]
def Policy.unexpandMod : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_field{$x}) => pure x
    | _ => `(cwnk_field|~$x)
  let y ← match y with
    | `(wnk_nat{$y}) => pure y
    | _ => `(cwnk_nat|~$y)
  `(wnk_policy { $x:cwnk_field ← $y })
| _ => throw ()

@[app_unexpander Policy.Add]
def Policy.unexpandAdd : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x ⨁ $y })
| _ => throw ()

@[app_unexpander Policy.Weight]
def Policy.unexpandWeight : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_weight{$x}) => pure x
    | _ => `(cwnk_weight|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x:cwnk_weight ⨀ $y })
| _ => throw ()

@[app_unexpander Policy.Iter]
def Policy.unexpandIter : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  `(wnk_policy { $x * })
| _ => throw ()

/-- info: wnk_policy {dup ⨁ dup} : Policy Unit -/
#guard_msgs in
#check (wnk_policy { dup ⨁ dup } : Policy Unit)

/-- info: wnk_policy {~123 = ~1; ¬false ∨ true; ~3 ⨀ ~12 ← ~2; dup ⨁ dup*} : Policy ℕ -/
#guard_msgs in
#check (wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~3 ⨀ ~12 ← 2 ; dup ⨁ dup* } : Policy ℕ)

-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_pred]
def cwnk_pred.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_pred true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_pred prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_policy]
def cwnk_policy.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_policy true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_policy prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- info: wnk_policy {~"x" = ~2; true ⨁ ¬~"x" = ~2; false} : Policy Unit -/
#guard_msgs in
#check (wnk_policy { if ~"x" = 2 then skip else drop } : Policy Unit)

/-- info: wnk_policy {(~"x" = ~2; true)*; ¬~"x" = ~2} : Policy Unit -/
#guard_msgs in
#check (wnk_policy { while ~"x" = 2 do skip } : Policy Unit)

end Syntax

end WeightedNetKAT
