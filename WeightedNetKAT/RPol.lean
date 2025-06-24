import WeightedNetKAT.Syntax

variable {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
variable {F : Type} [Fintype F] [DecidableEq F]

inductive RPol (W : Type) where
  | Drop
  | Skip
  | Test (pk : Pk[F])
  | Mod (pk : Pk[F])
  | Neg (p : RPol W)
  | Dup
  | Seq (p q : RPol W)
  | Weight (w : W) (p : RPol W)
  | Add (p q : RPol W)
  | Iter (p : RPol W)

notation "RPol[" α "," β "]" => RPol (F:=α) (W:=β)


@[simp]
def RPol.iter (p : RPol[F,𝒮]) : ℕ → RPol[F,𝒮]
  | 0 => .Skip
  | n+1 => p.Seq (p.iter n)

@[simp, reducible] instance RPol.instHPow : HPow RPol[F,𝒮] ℕ RPol[F,𝒮] where hPow p n := p.iter n

@[simp]
def RPol.iterDepth : RPol[F,𝒮] → ℕ
| .Skip | .Drop | .Test _ | .Mod _ | .Dup => 0
| .Add p q | .Seq p q => p.iterDepth ⊔ q.iterDepth
| .Neg q | .Weight _ q => q.iterDepth
| .Iter p => p.iterDepth + 1

omit [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype F] [DecidableEq F] in
@[simp]
theorem RPol.iterDepth_iter {p : RPol[F,𝒮]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

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
syntax "¬" cwnk_rpol : cwnk_rpol
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
| `(wnk_rpol { ¬ $p }) => `(RPol.Neg wnk_rpol {$p})
| `(wnk_rpol { ($t:cwnk_rpol) }) => `(wnk_rpol {$t})
| `(wnk_rpol { skip }) => `(RPol.Skip)
| `(wnk_rpol { drop }) => `(RPol.Drop)

macro_rules|`(wnk_pk{~$t})=>`($t)
macro_rules|`(wnk_rpol{~$t})=>`($t)


@[app_unexpander RPol.Neg]
def RPol.unexpandNot : Unexpander
| `($(_) $x) => do
  let x ← match x with
    | `(wnk_rpol{$x}) => pure x
    | _ => `(cwnk_rpol|~$x)
  `(wnk_rpol { ¬$x })
| _ => throw ()

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

/-- info: fun x ↦ wnk_rpol {@test ~x; ~3 ⨀ @mod ~x; dup ⨁ dup*} : Pk → RPol ℕ -/
#guard_msgs in
#check fun x : Pk[F] ↦ (wnk_rpol { @test ~x ; ~3 ⨀ @mod ~x ; dup ⨁ dup* } : RPol ℕ)

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
