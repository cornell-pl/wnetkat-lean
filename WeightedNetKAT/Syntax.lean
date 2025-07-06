import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Encodable.Pi

namespace WeightedNetKAT

variable {𝒮 : Type}

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]

abbrev Pk := F → N
notation "Pk[" f "," n "]" => Pk (F:=f) (N:=n)

def H := Pk[F,N] × List Pk[F,N]
notation "H[" f "," n "]" => H (F:=f) (N:=n)

instance : DecidableEq H[F,N] := inferInstanceAs (DecidableEq (_ × _))
instance : Countable H[F,N] := inferInstanceAs (Countable (_ × _))
instance [Encodable F] [Encodable N] : Encodable H[F,N] := inferInstanceAs (Encodable (_ × _))

inductive Pred where
  | Bool (b : Bool)
  | Test (f : F) (n : N)
  | Dis (t u : Pred)
  | Con (t u : Pred)
  | Not (t : Pred)

notation "Pred[" F "," N "]" => Pred (F:=F) (N:=N)

inductive Pol (W : Type) where
  | Filter (t : Pred[F,N])
  | Mod (f : F) (n : N)
  | Dup
  | Seq (p q : Pol W)
  | Weight (w : W) (p : Pol W)
  | Add (p q : Pol W)
  | Iter (p : Pol W)

notation "Pol[" f "," n "," w "]" => Pol (F:=f) (N:=n) (W:=w)

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
-- TODO: we need this, but we need to fix the precedence so it doens't interfere with Pol.Seq
-- syntax cwnk_pred "; " cwnk_pred : cwnk_pred
syntax "¬" cwnk_pred : cwnk_pred
syntax "(" cwnk_pred ")" : cwnk_pred

macro_rules
| `(wnk_pred { true }) => `(Pred.Bool true)
| `(wnk_pred { false }) => `(Pred.Bool false)
| `(wnk_pred { $f:cwnk_field = $n:cwnk_nat }) => `(Pred.Test wnk_field {$f} wnk_nat {$n})
| `(wnk_pred { $l:cwnk_pred ∨ $r:cwnk_pred }) => `(Pred.Dis wnk_pred {$l} wnk_pred {$r})
-- | `(wnk_pred { $l:cwnk_pred ; $r:cwnk_pred }) => `(Pred.And wnk_pred {$l} wnk_pred {$r})
| `(wnk_pred { ¬$l:cwnk_pred }) => `(Pred.Not wnk_pred {$l})
| `(wnk_pred { ($t) }) => `(wnk_pred {$t})

-- TODO: add proper precedence
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
| `(wnk_policy { $t:cwnk_pred }) => `(Pol.Filter wnk_pred {$t})
| `(wnk_policy { @filter $t:cwnk_pred }) => `(Pol.Filter wnk_pred {$t})
| `(wnk_policy { $p:cwnk_field ← $q:cwnk_nat }) => `(Pol.Mod wnk_field {$p} wnk_nat {$q})
| `(wnk_policy { dup }) => `(Pol.Dup)
| `(wnk_policy { $p ; $q }) => `(Pol.Seq wnk_policy {$p} wnk_policy {$q})
| `(wnk_policy { $w:cwnk_weight ⨀ $p }) => `(Pol.Weight wnk_weight {$w} wnk_policy {$p})
| `(wnk_policy { $p ⨁ $q }) => `(Pol.Add wnk_policy {$p} wnk_policy {$q})
| `(wnk_policy { $p * }) => `(Pol.Iter wnk_policy {$p})
| `(wnk_policy { ($t:cwnk_policy) }) => `(wnk_policy {$t})
-- Sugar
| `(wnk_policy { if $t then $p else $q }) => `(wnk_policy { $t:cwnk_pred ; $p ⨁ ¬$t ; $q })
| `(wnk_policy { while $t do $p }) => `(wnk_policy { ($t:cwnk_pred ; $p)* ; ¬$t })
| `(wnk_policy { skip }) => `(wnk_policy { true })
| `(wnk_policy { drop }) => `(wnk_policy { false })

/--
info: (Pol.Filter (Pred.Test 123 1)).Seq
  ((Pol.Filter ((Pred.Bool false).Dis (Pred.Bool true)).Not).Seq
    (Pol.Weight 1 ((Pol.Mod 12 2).Seq (Pol.Dup.Add Pol.Dup.Iter)))) : Pol ℕ
-/
#guard_msgs in
#check wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~1 ⨀ ~12 ← 2 ; dup ⨁ dup* }

macro_rules|`(wnk_pred{~$t})=>`($t)
macro_rules|`(wnk_policy{~$t})=>`($t)

@[app_unexpander Pred.Bool]
def Pred.unexpandBool : Unexpander
| `($(_) $x) =>
  match x with
  | `(true)  => let s := mkIdent $ .mkSimple "true";  `(wnk_pred { $s:ident })
  | `(false) => let s := mkIdent $ .mkSimple "false"; `(wnk_pred { $s:ident })
  | _ => throw ()
| _ => throw ()

@[app_unexpander Pred.Not]
def Pred.unexpandNot : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  `(wnk_pred { ¬$x })
| _ => throw ()

@[app_unexpander Pred.Dis]
def Pred.unexpandDis : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  let y ← match y with
    | `(wnk_pred{$y}) => pure y
    | _ => `(cwnk_pred|~$y)
  `(wnk_pred { $x ∨ $y })
| _ => throw ()

@[app_unexpander Pred.Test]
def Pred.unexpandTest : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_field{$x}) => pure x
    | _ => `(cwnk_field|~$x)
  let y ← match y with
    | `(wnk_nat{$y}) => pure y
    | _ => `(cwnk_nat|~$y)
  `(wnk_pred { $x:cwnk_field = $y })
| _ => throw ()

@[app_unexpander Pol.Filter]
def Pol.unexpandFilter : Unexpander
| `($(_) $f) =>
  match f with
  | `(wnk_pred {$f}) => `(wnk_policy {$f:cwnk_pred})
  | _ => throw ()
| _ => throw ()

/-- info: wnk_policy {true} : Pol Unit -/
#guard_msgs in
#check (wnk_policy { true } : Pol Unit)

@[app_unexpander Pol.Dup]
def Pol.unexpandDup : Unexpander
| _ => `(wnk_policy { dup })

@[app_unexpander Pol.Seq]
def Pol.unexpandSeq : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x ; $y })
| _ => throw ()

@[app_unexpander Pol.Mod]
def Pol.unexpandMod : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_field{$x}) => pure x
    | _ => `(cwnk_field|~$x)
  let y ← match y with
    | `(wnk_nat{$y}) => pure y
    | _ => `(cwnk_nat|~$y)
  `(wnk_policy { $x:cwnk_field ← $y })
| _ => throw ()

@[app_unexpander Pol.Add]
def Pol.unexpandAdd : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x ⨁ $y })
| _ => throw ()

@[app_unexpander Pol.Weight]
def Pol.unexpandWeight : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_weight{$x}) => pure x
    | _ => `(cwnk_weight|~$x)
  let y ← match y with
    | `(wnk_policy{$y}) => pure y
    | _ => `(cwnk_policy|~$y)
  `(wnk_policy { $x:cwnk_weight ⨀ $y })
| _ => throw ()

@[app_unexpander Pol.Iter]
def Pol.unexpandIter : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_policy{$x}) => pure x
    | _ => `(cwnk_policy|~$x)
  `(wnk_policy { $x * })
| _ => throw ()

/-- info: wnk_policy {dup ⨁ dup} : Pol Unit -/
#guard_msgs in
#check (wnk_policy { dup ⨁ dup } : Pol Unit)

/-- info: wnk_policy {~123 = ~1; ¬false ∨ true; ~3 ⨀ ~12 ← ~2; dup ⨁ dup*} : Pol ℕ -/
#guard_msgs in
#check (wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~3 ⨀ ~12 ← 2 ; dup ⨁ dup* } : Pol ℕ)

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

/-- info: wnk_policy {~"x" = ~2; true ⨁ ¬~"x" = ~2; false} : Pol Unit -/
#guard_msgs in
#check (wnk_policy { if ~"x" = 2 then skip else drop } : Pol Unit)

/-- info: wnk_policy {(~"x" = ~2; true)*; ¬~"x" = ~2} : Pol Unit -/
#guard_msgs in
#check (wnk_policy { while ~"x" = 2 do skip } : Pol Unit)

end Syntax

end WeightedNetKAT
