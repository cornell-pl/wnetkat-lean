import Mathlib.Data.Set.Finite.Basic
import WeightedNetKAT.Domain
import WeightedNetKAT.Subst
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Countable

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

abbrev W (X : Type) (𝒮 : Type) := X → 𝒮

def W.supp {X : Type} (m : W X 𝒮) := {x : X | m x ≠ 𝟘}

omit [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem W.supp_mem_iff {X : Type} {x} (m : W X 𝒮) : x ∈ m.supp ↔ m x ≠ 𝟘 := by rfl

noncomputable def W.mass (m : W X 𝒮) [Encodable m.supp] := ⨁' x : m.supp, m x.val

def 𝒲 (𝒮 : Type) [WeightedSemiring 𝒮] (X : Type) := {m : W X 𝒮 // Countable m.supp}

omit [WeightedOmegaContinuousPreSemiring 𝒮] in
@[ext]
theorem Countable.ext (C₁ C₂ : 𝒲 𝒮 X)
    (h : C₁.val = C₂.val) : C₁ = C₂ := by cases C₁; cases C₂; congr

abbrev 𝒲.supp (m : 𝒲 𝒮 X) := m.val.supp

instance : FunLike (𝒲 𝒮 X) X 𝒮 where
  coe m := m.val
  coe_injective' := by intro ⟨_, _⟩; simp_all

instance {m : 𝒲 𝒮 X} : Countable m.val.supp := m.prop
noncomputable instance {m : 𝒲 𝒮 X} : Encodable m.val.supp := Encodable.ofCountable _

section CountablePi

open Pi in
instance WeightedAdd.instCountablePi : WeightedAdd (𝒲 𝒮 X) where
  wAdd := fun a b ↦ ⟨a.val ⨁ b.val, by
    let ⟨a_underlying, a_prop⟩ := a
    let ⟨b_underlying, b_prop⟩ := b
    simp [wAdd]
    apply @Function.Injective.countable _ (Sum a_underlying.supp b_underlying.supp) _
    case f =>
      intro ⟨m_val, m_prop⟩
      simp [instPi] at m_prop
      by_cases a_underlying m_val = 𝟘
      case pos h =>
        apply Sum.inr
        exact ⟨ m_val, m_prop h ⟩
      case neg h =>
        apply Sum.inl
        exact ⟨ m_val, h⟩
    case hf =>
      dsimp
      intro ⟨v₁, p₁⟩ ⟨v₂, p₂⟩
      grind
    ⟩

instance WeightedMul.instCountablePi : WeightedMul (𝒲 𝒮 X) where
  wMul := fun ⟨ a_underlying, a_property ⟩ ⟨ b_underlying, b_property ⟩ => by
    refine ⟨a_underlying ⨀ b_underlying, ?_ ⟩
    apply @Function.Injective.countable ((a_underlying ⨀ b_underlying).supp) (Prod a_underlying.supp b_underlying.supp) _
    case f =>
      intro ⟨ m_val, m_prop ⟩
      simp at m_prop
      refine ⟨ ⟨ m_val, ?goal1 ⟩, ⟨ m_val, ?goal2 ⟩⟩
      all_goals (simp ; grind only [wMul, instPi, cases WeightedPreSemiring, cases WeightedSemiring])
    case hf =>
      intro ⟨v₁, p₁⟩ ⟨v₂, p₂ ⟩
      grind only

instance WeightedZero.instCountablePi : WeightedZero (𝒲 𝒮 X) where
  wZero := by
    refine ⟨ fun x => 𝟘, ?_⟩
    refine ⟨ fun x => 0, ?_ ⟩
    intro ⟨v1, p1⟩ ⟨v2, p2⟩
    trivial


def 𝓦.wNsmul (n : ℕ) (w : 𝒲 𝒮 X) : 𝒲 𝒮 X := match n with
  | 0 => 𝟘
  | n + 1 => wNsmul n w ⨁ w

instance WeightedPreSemiring.instCountablePi : WeightedPreSemiring (𝒲 𝒮 X) where
  wAdd_assoc _ _ _ := by ext x; apply wAdd_assoc
  wZero_add _ := by ext X; apply wZero_add
  add_wZero _ := by ext X; apply add_wZero
  wNsmul := 𝓦.wNsmul
  wNsmul_wZero _ := by rfl
  wNsmul_succ _ _ := by rfl
  wAdd_comm _ _ := by ext x; apply wAdd_comm
  left_distrib _ _ _ := by ext x; apply left_distrib
  right_distrib _ _ _ := by ext x; apply right_distrib
  wZero_mul _ := by ext x; apply wZero_mul
  mul_wZero _ := by ext x; apply mul_wZero
  mul_assoc _ _ _ := by ext x; apply mul_assoc

instance WeightedLE.instCountablePi : WeightedLE (𝒲 𝒮 X) where
  wle := fun ⟨a, _⟩ ⟨ b, _ ⟩ => a ≼ b

instance WeightedPartialOrder.instCountablePi  : WeightedPartialOrder (𝒲 𝒮 X) where
  wle_refl a x := by simp
  wle_trans {a b c} hab hbc x := wle_trans (hab x) (hbc x)
  wle_antisymm { a b} hab hba := by
    have ⟨ a_val, a_prop ⟩ := a
    have ⟨ b_val, b_prop ⟩ := b
    suffices a_val = b_val by
      grind only
    ext x
    exact wle_antisymm (hab x) (hba x)

attribute [simp] WeightedZero.instCountablePi

instance WeightedOmegaCompletePartialOrder.instCountablePi :
    WeightedOmegaCompletePartialOrder (𝒲 𝒮 X) where
  wSup C := ⟨fun i ↦ wSup (C.map (· i) sorry), sorry⟩
  le_wSup := sorry
  wSup_le := sorry

open WeightedOmegaCompletePartialOrder in
instance WeightedOmegaContinuousPreSemiring.instCountablePi :
    WeightedOmegaContinuousPreSemiring (𝒲 𝒮 X) where
  wle_positive := sorry
  wAdd_mono := sorry
  wMul_mono_left := sorry
  wMul_mono_right := sorry
  wAdd_wSup := sorry
  wSup_wAdd := sorry
  wMul_wSup := sorry
  wSup_wMul := sorry

end CountablePi

def η [DecidableEq X] (x : X) : 𝒲 𝒮 X := ⟨fun y ↦ if x = y then 𝟙 else 𝟘, by
  suffices Finite (W.supp (𝒮:=𝒮) fun y ↦ if x = y then 𝟙 else 𝟘) by apply Finite.to_countable
  if (𝟙 : 𝒮) = 𝟘 then
    apply Set.Finite.ofFinset {}
    simpa
  else
    apply Set.Finite.ofFinset {x}
    simpa [eq_comm]⟩

notation "η[" 𝒮 "]" => η (𝒮:=𝒮)

-- TODO: these should be moved somewhere more appropriate
theorem wMul_eq_zero_of {α : Type} [WeightedPreSemiring α] {a b : α} : a = 𝟘 ∨ b = 𝟘 → a ⨀ b = 𝟘 := by
  rintro (h | h) <;> subst_eqs <;> simp
@[simp]
theorem nonzero_wMul_nonzero {α : Type} [WeightedPreSemiring α] {a b : α} : ¬a ⨀ b = 𝟘 → ¬a = 𝟘 ∧ ¬b = 𝟘 := by
  contrapose!
  intro h
  apply wMul_eq_zero_of
  symm
  simp_all [or_iff_not_imp_right]

theorem Set.Countable.subst {α : Type} {S T : Set α} (hS : Countable S) (h : T ⊆ S) :
    Countable T :=
  mono h hS

set_option maxHeartbeats 500000 in
noncomputable def 𝒲.bind {Y : Type} (m : 𝒲 𝒮 X) (f : X → 𝒲 𝒮 Y) :
    𝒲 𝒮 Y :=
  ⟨fun y ↦ ⨁' x : m.supp, m x ⨀ f x y, by
    let s : Set _ := ⋃ x ∈ m.supp, (f x).supp
    apply Set.Countable.mono _ (Set.Countable.biUnion m.prop fun a _ ↦ (f a).prop : Countable s)
    intro y
    simp only [W.supp_mem_iff, ne_eq, WeightedSum_eq_zero_iff, Subtype.forall, not_forall,
      Classical.not_imp, Set.mem_iUnion, exists_prop, forall_exists_index, and_imp, s]
    intro x h₁ h₂
    use x, h₁
    intro h
    have : f x y = 𝟘 := h
    simp_all⟩

infixr:50 " ≫= " => 𝒲.bind

instance {Y : Type} [Countable X] {m : 𝒲 𝒮 X} (f : X → 𝒲 𝒮 Y) :
    Countable (m ≫= f).val.supp := (m ≫= f).prop

variable {F : Type} [Fintype F] [DecidableEq F]

abbrev Pk := F → ℕ
notation "Pk[" F "]" => Pk (F:=F)

abbrev H := List Pk[F]
notation "H[" F "]" => H (F:=F)

inductive Predicate where
  | Bool (b : Bool)
  | Test (f : F) (n : ℕ)
  | Dis (t u : Predicate)
  | Con (t u : Predicate)
  | Not (t : Predicate)

notation "Predicate[" F "]" => Predicate (F:=F)

inductive Policy where
  | Filter (t : Predicate[F])
  | Mod (f : F) (n : ℕ)
  | Dup
  | Seq (p q : Policy)
  | Weight (w : 𝒲 𝒮 H[F]) (p : Policy)
  | Add (p q : Policy)
  | Iter (p : Policy)

notation "Policy[" F "," W "]" => Policy (F:=F) (W:=W)

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
    (Policy.Weight ⟨fun x ↦ 1, ⋯⟩ ((Policy.Mod 12 2).Seq (Policy.Dup.Add Policy.Dup.Iter)))) : Policy
-/
#guard_msgs in
#check wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~⟨fun x ↦ 1, sorry⟩ ⨀ ~12 ← 2 ; dup ⨁ dup* }

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

/-- info: wnk_policy {true} : Policy -/
#guard_msgs in
#check wnk_policy { true }

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

/-- info: wnk_policy {dup ⨁ dup} : Policy -/
#guard_msgs in
#check wnk_policy { dup ⨁ dup }

/-- info: wnk_policy {~123 = ~1; ¬false ∨ true; ~⟨fun x ↦ 1, ⋯⟩ ⨀ ~12 ← ~2; dup ⨁ dup*} : Policy -/
#guard_msgs in
#check wnk_policy { ~123 = 1 ; ¬false ∨ true ; ~⟨fun x ↦ 1, sorry⟩ ⨀ ~12 ← 2 ; dup ⨁ dup* }

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

/-- info: wnk_policy {~"x" = ~2; true ⨁ ¬~"x" = ~2; false} : Policy -/
#guard_msgs in
#check wnk_policy { if ~"x" = 2 then skip else drop }

/-- info: wnk_policy {(~"x" = ~2; true)*; ¬~"x" = ~2} : Policy -/
#guard_msgs in
#check wnk_policy { while ~"x" = 2 do skip }

end Syntax
