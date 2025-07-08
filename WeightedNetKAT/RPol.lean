import WeightedNetKAT.Syntax

namespace WeightedNetKAT

variable {𝒮 : Type*}
variable {F : Type*} [Fintype F] [DecidableEq F]
variable {N : Type*} [Fintype N] [DecidableEq N]

inductive RPol (W : Type*) where
  | Drop
  | Skip
  | Test (pk : Pk[F,N])
  | Mod (pk : Pk[F,N])
  | Dup
  | Seq (p q : RPol W)
  | Weight (w : W) (p : RPol W)
  | Add (p q : RPol W)
  | Iter (p : RPol W)
-- TODO: we need to figure out how we can get `DecidableEq Pk[F,N]` to get this
-- deriving DecidableEq

notation "RPol[" f "," n "," w "]" => RPol (F:=f) (N:=n) (W:=w)

section Syntax

open Lean Elab PrettyPrinter Delaborator Meta Command Term

declare_syntax_cat' wnk_rpol
declare_syntax_cat' wnk_pk

syntax cwnk_pk:min : cwnk_rpol
syntax cwnk_field " ← " cwnk_nat : cwnk_rpol
syntax "dup" : cwnk_rpol
syntax cwnk_rpol "; " cwnk_rpol : cwnk_rpol
syntax cwnk_weight " ⨀ " cwnk_rpol : cwnk_rpol
syntax cwnk_rpol " ⨁ " cwnk_rpol : cwnk_rpol
syntax cwnk_rpol "*" : cwnk_rpol
syntax "(" cwnk_rpol ")" : cwnk_rpol
syntax "@test" ppHardSpace cwnk_pk:min : cwnk_rpol
syntax "@mod" ppHardSpace cwnk_pk:min : cwnk_rpol

-- Sugar

syntax "skip" : cwnk_rpol
syntax "drop" : cwnk_rpol
syntax "if" ppHardSpace cwnk_pk ppHardSpace "then"
  ppHardSpace cwnk_rpol ppHardSpace "else" ppHardSpace cwnk_rpol : cwnk_rpol
syntax "while" ppHardSpace cwnk_pk ppHardSpace "do"
  ppHardSpace cwnk_rpol : cwnk_rpol

macro_rules
| `(wnk_rpol { @test $t:cwnk_pk }) => `(RPol.Test wnk_pk {$t})
| `(wnk_rpol { @mod $t:cwnk_pk }) => `(RPol.Mod wnk_pk {$t})
| `(wnk_rpol { dup }) => `(RPol.Dup)
| `(wnk_rpol { $p ; $q }) => `(RPol.Seq wnk_rpol {$p} wnk_rpol {$q})
| `(wnk_rpol { $w:cwnk_weight ⨀ $p }) => `(RPol.Weight wnk_weight {$w} wnk_rpol {$p})
| `(wnk_rpol { $p ⨁ $q }) => `(RPol.Add wnk_rpol {$p} wnk_rpol {$q})
| `(wnk_rpol { $p * }) => `(RPol.Iter wnk_rpol {$p})
| `(wnk_rpol { ($t:cwnk_rpol) }) => `(wnk_rpol {$t})
| `(wnk_rpol { skip }) => `(RPol.Skip)
| `(wnk_rpol { drop }) => `(RPol.Drop)

macro_rules|`(wnk_pk{~$t})=>`($t)
macro_rules|`(wnk_rpol{~$t})=>`($t)

@[app_unexpander RPol.Test]
def RPol.unexpandTest : Unexpander
| `($(_) $x) => do
  let x ← match x with
  | `(wnk_pk{$x}) => pure x
  | _ => `(cwnk_pk|~$x)
  `(wnk_rpol { @test $x:cwnk_pk })
| _ => throw ()

@[app_unexpander RPol.Dup]
def RPol.unexpandDup : Unexpander
| _ => `(wnk_rpol { dup })

@[app_unexpander RPol.Seq]
def RPol.unexpandSeq : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_rpol{$x}) => pure x
    | _ => `(cwnk_rpol|~$x)
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | _ => `(cwnk_rpol|~$y)
  `(wnk_rpol { $x ; $y })
| _ => throw ()

@[app_unexpander RPol.Mod]
def RPol.unexpandMod : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_pk{$x}) => pure x
    | _ => `(cwnk_pk|~$x)
  `(wnk_rpol { @mod $x:cwnk_pk })
| _ => throw ()

@[app_unexpander RPol.Add]
def RPol.unexpandAdd : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_rpol{$x}) => pure x
    | _ => `(cwnk_rpol|~$x)
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | _ => `(cwnk_rpol|~$y)
  `(wnk_rpol { $x ⨁ $y })
| _ => throw ()

@[app_unexpander RPol.Weight]
def RPol.unexpandWeight : Unexpander
| `($(_) $x $y) => do
  let x ← match x with
    | `(wnk_weight{$x}) => pure x
    | _ => `(cwnk_weight|~$x)
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | _ => `(cwnk_rpol|~$y)
  `(wnk_rpol { $x:cwnk_weight ⨀ $y })
| _ => throw ()

@[app_unexpander RPol.Iter]
def RPol.unexpandIter : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_rpol{$x}) => pure x
    | _ => `(cwnk_rpol|~$x)
  `(wnk_rpol { $x * })
| _ => throw ()

/-- info: wnk_rpol {dup ⨁ dup} : RPol Unit -/
#guard_msgs in
#check (wnk_rpol { dup ⨁ dup } : RPol Unit)

/-- info: fun x ↦ wnk_rpol {@test ~x; ~3 ⨀ @mod ~x; dup ⨁ dup*} : Pk[F,N] → RPol ℕ -/
#guard_msgs in
#check fun x : Pk[F,N] ↦ (wnk_rpol { @test ~x ; ~3 ⨀ @mod ~x ; dup ⨁ dup* } : RPol[F,N,ℕ])

-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_pk]
def cwnk_pk.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_pk true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_pk prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed.
@[category_parenthesizer cwnk_rpol]
def cwnk_rpol.parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `cwnk_rpol true wrapParens prec $
    Parenthesizer.parenthesizeCategoryCore `cwnk_rpol prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

end Syntax

section Semantics

@[simp]
def RPol.iter (p : RPol[F,N,𝒮]) : ℕ → RPol[F,N,𝒮]
  | 0 => .Skip
  | n+1 => p.Seq (p.iter n)

@[simp, reducible] instance RPol.instHPow : HPow RPol[F,N,𝒮] ℕ RPol[F,N,𝒮] where hPow p n := p.iter n

@[simp]
def RPol.iterDepth : RPol[F,N,𝒮] → ℕ
| wnk_rpol { skip } | wnk_rpol { drop } | wnk_rpol { @test ~_ } | wnk_rpol { @mod ~_ } | wnk_rpol { dup } => 0
| wnk_rpol {~p ⨁ ~q} | wnk_rpol {~p; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_rpol { ~_ ⨀ ~q } => q.iterDepth
| wnk_rpol {~p*} => p.iterDepth + 1

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
@[simp]
theorem RPol.iterDepth_iter {p : RPol[F,N,𝒮]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

end Semantics

section Repr

def RPol.repr {F : Type*} [i : Fintype F] [e : Encodable F] [Repr F] [Repr N] [Repr 𝒮] : RPol[F,N,𝒮] → String
| wnk_rpol { @test ~t } => s!"@test {reprStr t}"
| wnk_rpol { @mod ~t } => s!"@mod {reprStr t}"
| wnk_rpol { dup } => s!"dup"
| wnk_rpol { ~p ; ~q } => s!"{p.repr} ; {q.repr}"
| wnk_rpol { ~w ⨀ ~p } => s!"{reprStr w} ⨀ {p.repr}"
| wnk_rpol { ~p ⨁ ~q } => s!"{p.repr} ⨁ {q.repr}"
| wnk_rpol { ~p * } => s!"{p.repr}*"
| wnk_rpol { skip } => s!"skip"
| wnk_rpol { drop } => s!"drop"

instance {F : Type*} [i : Fintype F] [e : Encodable F] [Repr F] [Repr N] [Repr 𝒮] : Repr RPol[F,N,𝒮] where
  reprPrec p _ := p.repr

end Repr

end WeightedNetKAT
