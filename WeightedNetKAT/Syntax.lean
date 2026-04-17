module

public import Mathlib.Data.Countable.Basic
public import Mathlib.Logic.Encodable.Pi
public import WeightedNetKAT.Listed.Vector

@[expose] public section

namespace WeightedNetKAT

variable {𝒮 : Type}

variable {F : Type} [Listed F] [DecidableEq F]
variable {N : Type} [DecidableEq N]

-- abbrev Pk (F N : Type) := F → N
-- notation "Pk[" F "," N "]" => Pk F N

structure Pk (F N : Type) [Listed F] where
  data : Vector N (Listed.size (α:=F))
deriving DecidableEq, Inhabited
notation "Pk[" F "," N "]" => Pk F N

instance : FunLike Pk[F,N] F N where
  coe f i := f.data[Listed.encodeFin i]
  coe_injective' := by
    intro ⟨α⟩ ⟨β⟩ h
    simp_all
    ext i hi
    replace h := congrFun h (Listed.decodeFin ⟨i, hi⟩)
    simpa using h

def Pk.fill (x : N) : Pk[F,N] := ⟨.ofFn fun _ ↦ x⟩
def Pk.ofFn (f : F → N) : Pk[F,N] := ⟨.ofFn fun i ↦ f (Listed.decodeFin i)⟩

instance Pk.listed [Listed N] : Listed Pk[F,N] :=
  Listed.lift (α:=Vector N (Listed.size (α:=F))) ⟨(⟨·⟩), (·.data), by grind, by grind⟩
instance Pk.fintype [Listed N] : Fintype Pk[F,N] := Listed.fintype

instance Pk.ofNat {n : ℕ} [OfNat N n] : OfNat Pk[F,N] n where
  ofNat := .fill (OfNat.ofNat n)

-- omit [Fintype F] [Fintype N] [DecidableEq F] [DecidableEq N] in
-- instance [Listed F] [Listed N] [Inhabited N] : Listed Pk[F,N] := Listed.pi F N

instance {F : Type} [Listed F] [Repr F] [Repr N] : Repr Pk[F,N] where
  reprPrec x _ := s!"\{{Listed.listOf _ |>.map (fun k ↦ s!"{reprStr k}↦{reprStr (x k)}") |> ",".intercalate}}"

notation "H[" F "," N "]" => Pk[F,N] × List Pk[F,N]

instance : DecidableEq H[F,N] := inferInstanceAs (DecidableEq (_ × _))
instance [Listed N] : Countable H[F,N] := inferInstanceAs (Countable (_ × _))
-- instance [Encodable F] [Encodable N] : Encodable H[F,N] := inferInstanceAs (Encodable (_ × _))

inductive Pred (F N : Type) where
  | Bool (b : Bool)
  | Test (f : F) (n : N)
  | Dis (t u : Pred F N)
  | Con (t u : Pred F N)
  | Not (t : Pred F N)

notation "Pred[" F "," N "]" => Pred F N

inductive Pol (F N W : Type) where
  | Filter (t : Pred[F,N])
  | Mod (f : F) (n : N)
  | Dup
  | Seq (p q : Pol F N W)
  | Weight (w : W) (p : Pol F N W)
  | Add (p q : Pol F N W)
  | Iter (p : Pol F N W)

notation "Pol[" F "," N "," W "]" => Pol F N W

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
declare_syntax_cat' wnk_pol
syntax "wnk_pol[" term "," term "," term "]" ppHardSpace "{" cwnk_pol "}" : term
macro_rules|`(wnk_pol[$F,$N,$𝒮] {$p}) => `((wnk_pol {$p} : Pol[$F,$N,$𝒮]))

syntax term:max : cwnk_field
macro_rules|`(wnk_field{$t:term})=>`($t)
syntax term:max : cwnk_nat
macro_rules|`(wnk_nat{$t:term})=>`($t)
syntax num : cwnk_weight
macro_rules|`(wnk_weight{$t:num})=>`($t)

syntax num : cwnk_nat

macro_rules
| `(wnk_nat { $n:num }) => `($n)

-- TODO: add proper precedence
syntax ident : cwnk_pred
syntax:50 cwnk_field:50 " = " cwnk_nat:50 : cwnk_pred
syntax:30 cwnk_pred:30 " ∨ " cwnk_pred:31 : cwnk_pred
syntax:35 cwnk_pred:35 " ∧ " cwnk_pred:36 : cwnk_pred
syntax:max "¬" cwnk_pred : cwnk_pred
syntax "(" cwnk_pred ")" : cwnk_pred

macro_rules
| `(wnk_pred { true }) => `(Pred.Bool true)
| `(wnk_pred { false }) => `(Pred.Bool false)
| `(wnk_pred { $f:cwnk_field = $n:cwnk_nat }) => `(Pred.Test wnk_field {$f} wnk_nat {$n})
| `(wnk_pred { $l:cwnk_pred ∨ $r:cwnk_pred }) => `(Pred.Dis wnk_pred {$l} wnk_pred {$r})
| `(wnk_pred { $l:cwnk_pred ∧ $r:cwnk_pred }) => `(Pred.Con wnk_pred {$l} wnk_pred {$r})
| `(wnk_pred { ¬$l:cwnk_pred }) => `(Pred.Not wnk_pred {$l})
| `(wnk_pred { ($t) }) => `(wnk_pred {$t})

/-- info: ((Pred.Bool true).Con (Pred.Bool false)).Dis (Pred.Bool true).Not : Pred[Unit,ℕ] -/
#guard_msgs in
#check (wnk_pred { true ∧ false ∨ ¬true } : Pred[Unit,ℕ])

-- TODO: add proper precedence
syntax cwnk_pred : cwnk_pol
syntax:100 cwnk_field " ← " cwnk_nat : cwnk_pol
syntax "dup" : cwnk_pol
syntax:55 cwnk_pol:55 "; " cwnk_pol:56 : cwnk_pol
syntax cwnk_weight " ⨀ " cwnk_pol : cwnk_pol
syntax cwnk_pol " ⨁ " cwnk_pol : cwnk_pol
syntax cwnk_pol "*" : cwnk_pol
syntax "(" cwnk_pol ")" : cwnk_pol
syntax "@filter" ppHardSpace cwnk_pred:min : cwnk_pol

-- Sugar

syntax "skip" : cwnk_pol
syntax "drop" : cwnk_pol
syntax "if" ppHardSpace cwnk_pred ppHardSpace "then"
  ppHardSpace cwnk_pol ppHardSpace "else" ppHardSpace cwnk_pol : cwnk_pol
syntax "while" ppHardSpace cwnk_pred ppHardSpace "do"
  ppHardSpace cwnk_pol : cwnk_pol

macro_rules
| `(wnk_pol { $t:cwnk_pred }) => `(Pol.Filter wnk_pred {$t})
| `(wnk_pol { @filter $t:cwnk_pred }) => `(Pol.Filter wnk_pred {$t})
| `(wnk_pol { $p:cwnk_field ← $q:cwnk_nat }) => `(Pol.Mod wnk_field {$p} wnk_nat {$q})
| `(wnk_pol { dup }) => `(Pol.Dup)
| `(wnk_pol { $p ; $q }) => `(Pol.Seq wnk_pol {$p} wnk_pol {$q})
| `(wnk_pol { $w:cwnk_weight ⨀ $p }) => `(Pol.Weight wnk_weight {$w} wnk_pol {$p})
| `(wnk_pol { $p ⨁ $q }) => `(Pol.Add wnk_pol {$p} wnk_pol {$q})
| `(wnk_pol { $p * }) => `(Pol.Iter wnk_pol {$p})
| `(wnk_pol { ($t:cwnk_pol) }) => `(wnk_pol {$t})
-- Sugar
| `(wnk_pol { if $t then $p else $q }) => `(wnk_pol { $t:cwnk_pred ; $p ⨁ ¬$t ; $q })
| `(wnk_pol { while $t do $p }) => `(wnk_pol { ($t:cwnk_pred ; $p)* ; ¬$t })
| `(wnk_pol { skip }) => `(wnk_pol { true })
| `(wnk_pol { drop }) => `(wnk_pol { false })

/--
info: ((Pol.Filter (Pred.Test 123 1)).Seq (Pol.Filter ((Pred.Bool false).Dis (Pred.Bool true)).Not)).Seq
  (Pol.Weight 1 ((Pol.Mod 12 2).Seq (Pol.Dup.Add Pol.Dup.Iter))) : Pol[ℕ,ℕ,ℕ]
-/
#guard_msgs in
#check wnk_pol { ~123 = 1 ; ¬false ∨ true ; ~1 ⨀ ~12 ← 2 ; dup ⨁ dup* }

macro_rules|`(wnk_pred{~$t})=>`($t)
macro_rules|`(wnk_pol{~$t})=>`($t)

@[app_unexpander Pred.Bool]
meta def Pred.unexpandBool : Unexpander
| `($(_) $x) =>
  match x with
  | `(true)  => let s := mkIdent $ .mkSimple "true";  `(wnk_pred { $s:ident })
  | `(false) => let s := mkIdent $ .mkSimple "false"; `(wnk_pred { $s:ident })
  | _ => throw ()
| _ => throw ()

@[app_unexpander Pred.Not]
meta def Pred.unexpandNot : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  `(wnk_pred { ¬$x })
| _ => throw ()

@[app_unexpander Pred.Dis]
meta def Pred.unexpandDis : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  let y ← match y with
    | `(wnk_pred{$y}) => pure y
    | _ => `(cwnk_pred|~$y)
  `(wnk_pred { $x ∨ $y })
| _ => throw ()

@[app_unexpander Pred.Con]
meta def Pred.unexpandCon : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pred{$x}) => pure x
    | _ => `(cwnk_pred|~$x)
  let y ← match y with
    | `(wnk_pred{$y}) => pure y
    | _ => `(cwnk_pred|~$y)
  `(wnk_pred { $x ∧ $y })
| _ => throw ()

@[app_unexpander Pred.Test]
meta def Pred.unexpandTest : Unexpander
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
meta def Pol.unexpandFilter : Unexpander
| `($(_) $f) =>
  match f with
  | `(wnk_pred {$f}) => `(wnk_pol {$f:cwnk_pred})
  | _ => throw ()
| _ => throw ()

/-- info: wnk_pol {true ∧ ¬false ∨ true} : Pol[Unit,Unit,Unit] -/
#guard_msgs in
#check (wnk_pol { true ∧ ¬false ∨ true } : Pol[Unit,Unit,Unit])

@[app_unexpander Pol.Dup]
meta def Pol.unexpandDup : Unexpander
| _ => `(wnk_pol { dup })

@[app_unexpander Pol.Seq]
meta def Pol.unexpandSeq : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pol{$x}) => pure x
    | _ => `(cwnk_pol|~$x)
  let y ← match y with
    | `(wnk_pol{$y}) => pure y
    | _ => `(cwnk_pol|~$y)
  `(wnk_pol { $x ; $y })
| _ => throw ()

@[app_unexpander Pol.Mod]
meta def Pol.unexpandMod : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_field{$x}) => pure x
    | _ => `(cwnk_field|~$x)
  let y ← match y with
    | `(wnk_nat{$y}) => pure y
    | _ => `(cwnk_nat|~$y)
  `(wnk_pol { $x:cwnk_field ← $y })
| _ => throw ()

@[app_unexpander Pol.Add]
meta def Pol.unexpandAdd : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_pol{$x}) => pure x
    | _ => `(cwnk_pol|~$x)
  let y ← match y with
    | `(wnk_pol{$y}) => pure y
    | _ => `(cwnk_pol|~$y)
  `(wnk_pol { $x ⨁ $y })
| _ => throw ()

@[app_unexpander Pol.Weight]
meta def Pol.unexpandWeight : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_weight{$x}) => pure x
    | _ => `(cwnk_weight|~$x)
  let y ← match y with
    | `(wnk_pol{$y}) => pure y
    | _ => `(cwnk_pol|~$y)
  `(wnk_pol { $x:cwnk_weight ⨀ $y })
| _ => throw ()

@[app_unexpander Pol.Iter]
meta def Pol.unexpandIter : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_pol{$x}) => pure x
    | _ => `(cwnk_pol|~$x)
  `(wnk_pol { $x * })
| _ => throw ()

/-- info: wnk_pol {dup ⨁ dup} : Pol[Unit,Unit,Unit] -/
#guard_msgs in
#check (wnk_pol { dup ⨁ dup } : Pol[Unit,Unit,Unit])

/-- info: wnk_pol {~123 = ~1; ¬false ∨ true; ~3 ⨀ ~12 ← ~2; dup ⨁ dup*} : Pol[ℕ,ℕ,ℕ] -/
#guard_msgs in
#check (wnk_pol { ~123 = 1 ; ¬false ∨ true ; ~3 ⨀ ~12 ← 2 ; dup ⨁ dup* } : Pol[ℕ,ℕ,ℕ])

-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_pred]
meta def cwnk_pred.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_pred true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_pred prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_pol]
meta def cwnk_pol.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_pol true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_pol prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-- info: wnk_pol {~"x" = ~2; true ⨁ ¬~"x" = ~2; false} : Pol[String,ℕ,Unit] -/
#guard_msgs in
#check (wnk_pol { if ~"x" = 2 then skip else drop } : Pol[String,ℕ,Unit])

/-- info: wnk_pol {(~"x" = ~2; true)*; ¬~"x" = ~2} : Pol[String,ℕ,Unit] -/
#guard_msgs in
#check (wnk_pol { while ~"x" = 2 do skip } : Pol[String,ℕ,Unit])

end Syntax

end WeightedNetKAT
