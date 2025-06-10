import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.Defs.PartialOrder

class WeightedAdd (α : Type) where
  /-- Weighted addition. Type `a ⨁ b` using `\O+`. -/
  wAdd : α → α → α

class WeightedMul (α : Type) where
  /-- Weighted multiplication. Type `a ⨀ b` using `\O.`. -/
  wMul : α → α → α

@[inherit_doc] infixl:65 " ⨁ " => WeightedAdd.wAdd
@[inherit_doc] infixl:70 " ⨀ " => WeightedMul.wMul

instance : WeightedAdd ℕ := ⟨(· + ·)⟩
instance : WeightedMul ℕ := ⟨(· * ·)⟩

/-- info: 1 ⨁ 2 ⨀ 3 : ℕ -/
#guard_msgs in
#check 1 ⨁ 2 ⨀ 3

  /-- Weighted zero. Type `𝟘` using `\b0`. -/
class WeightedZero (α : Type) where wZero : α
  /-- Weighted one. Type `𝟙` using `\b1`. -/
class WeightedOne (α : Type) where wOne : α

notation "𝟘" => WeightedZero.wZero
notation "𝟙" => WeightedOne.wOne

class WeightedSemiring (α : Type) extends
    WeightedAdd α, WeightedMul α, WeightedZero α, WeightedOne α where
  wAdd_assoc (a b c : α) : a ⨁ b ⨁ c = a ⨁ (b ⨁ c)
  wZero_add (a : α) : 𝟘 ⨁ a = a
  add_wZero (a : α) : a ⨁ 𝟘 = a
  wNsmul : ℕ → α → α
  wNsmul_wZero (a : α) : wNsmul 0 a = 𝟘
  wNsmul_succ (n : ℕ) (x : α) : wNsmul (n + 1) x = wNsmul n x ⨁ x
  wAdd_comm (a b : α) : a ⨁ b = b ⨁ a
  left_distrib (a b c : α) : a ⨀ (b ⨁ c) = a ⨀ b ⨁ a ⨀ c
  right_distrib (a b c : α) : (a ⨁ b) ⨀ c = a ⨀ c ⨁ b ⨀ c
  wZero_mul (a : α) : 𝟘 ⨀ a = 𝟘
  mul_wZero (a : α) : a ⨀ 𝟘 = 𝟘
  mul_assoc (a b c : α) : a ⨀ b ⨀ c = a ⨀ (b ⨀ c)
  wOne_mul (a : α) : 𝟙 ⨀ a = a
  mul_wOne (a : α) : a ⨀ 𝟙 = a
  natCast : ℕ → α
  natCast_zero : natCast 0 = 𝟘
  natCast_succ (n : ℕ) : natCast (n + 1) = natCast n ⨁ 𝟙
  wNpow : ℕ → α → α
  wNpow_zero (x : α) : wNpow 0 x = 𝟙
  wNpow_succ (n : ℕ) (x : α) : wNpow (n + 1) x = wNpow n x ⨀ x

attribute [simp] WeightedSemiring.wZero_add
attribute [simp] WeightedSemiring.add_wZero
attribute [simp] WeightedSemiring.wOne_mul
attribute [simp] WeightedSemiring.mul_wOne

variable {α : Type}

instance [WeightedSemiring α] : Std.Commutative (fun (a b : α) ↦ a ⨁ b) :=
  ⟨WeightedSemiring.wAdd_comm⟩
instance [WeightedSemiring α] : Std.Associative (fun (a b : α) ↦ a ⨁ b) :=
  ⟨WeightedSemiring.wAdd_assoc⟩

def WeightedSemiring.toSemiring (α : Type) [i : WeightedSemiring α] : Semiring α where
  add := i.wAdd
  add_assoc := i.wAdd_assoc
  zero := i.wZero
  zero_add := i.wZero_add
  add_zero := i.add_wZero
  nsmul := i.wNsmul
  nsmul_zero := i.wNsmul_wZero
  nsmul_succ := i.wNsmul_succ
  add_comm := i.wAdd_comm
  mul := i.wMul
  left_distrib := i.left_distrib
  right_distrib := i.right_distrib
  zero_mul := i.wZero_mul
  mul_zero := i.mul_wZero
  mul_assoc := i.mul_assoc
  one := i.wOne
  one_mul := i.wOne_mul
  mul_one := i.mul_wOne
  natCast := i.natCast
  natCast_zero := i.natCast_zero
  natCast_succ := i.natCast_succ
  npow := i.wNpow
  npow_zero := i.wNpow_zero
  npow_succ := i.wNpow_succ

def WeightedSemiring.ofSemiring (α : Type) [i : Semiring α] : WeightedSemiring α where
  wAdd := i.add
  wAdd_assoc := i.add_assoc
  wZero := i.zero
  wZero_add := i.zero_add
  add_wZero := i.add_zero
  wNsmul := i.nsmul
  wNsmul_wZero := i.nsmul_zero
  wNsmul_succ := i.nsmul_succ
  wAdd_comm := i.add_comm
  wMul := i.mul
  left_distrib := i.left_distrib
  right_distrib := i.right_distrib
  wZero_mul := i.zero_mul
  mul_wZero := i.mul_zero
  mul_assoc := i.mul_assoc
  wOne := i.one
  wOne_mul := i.one_mul
  mul_wOne := i.mul_one
  natCast := i.natCast
  natCast_zero := i.natCast_zero
  natCast_succ := i.natCast_succ
  wNpow := i.npow
  wNpow_zero := i.npow_zero
  wNpow_succ := i.npow_succ

instance (priority := 100) : WeightedSemiring ℕ := WeightedSemiring.ofSemiring ℕ

class WeightedLE (α : Type) where
  wle : α → α → Prop

/-- Weighted less-than-or-equal defined by the natural order. -/
@[reducible] def wLe {α : Type} [WeightedLE α] (a b : α) := WeightedLE.wle a b
@[inherit_doc] infix:50 " ≼ " => wLe

/-- Weighted greater-than-or-equal defined by the natural order. -/
@[reducible] def wGe {α : Type} [WeightedLE α] (a b : α) := b ≼ a
@[inherit_doc] infix:50 " ≽ " => wGe

instance (priority := 100) : WeightedLE ℕ where
  wle := LE.le

/-- info: 1 ≼ 2 : Prop -/
#guard_msgs in
#check 1 ≼ 2

class WeightedPartialOrder (α) extends WeightedLE α where
  wle_refl (a : α) : a ≼ a
  wle_trans {a b c : α} : a ≼ b → b ≼ c → a ≼ c
  wle_antisymm {a b : α} : a ≼ b → b ≼ a → a = b

attribute [simp] WeightedPartialOrder.wle_refl

theorem WeightedPartialOrder.wle_antisymm_iff [WeightedPartialOrder α] {a b : α} :
    a = b ↔ a ≼ b ∧ b ≼ a := ⟨by simp_all, fun h ↦ wle_antisymm h.left h.right⟩

class WeightedNaturalPartialOrder (α) [WeightedSemiring α] extends WeightedPartialOrder α where
  wle_natural (a b : α) : a ≼ b ↔ ∃ c, a ⨁ c = b

def WeightedMonotone [WeightedLE α] {ι : Type} [WeightedLE ι] (f : ι → α) : Prop :=
  ∀ {s₁ s₂}, s₁ ≼ s₂ → f s₁ ≼ f s₂
def WeightedAntitone [WeightedLE α] {ι : Type} [WeightedLE ι] (f : ι → α) : Prop :=
  ∀ {s₁ s₂}, s₁ ≼ s₂ → f s₂ ≼ f s₁

def WeightedChain (α : Type) [WeightedPartialOrder α] :=
  { f : ℕ → α // WeightedMonotone f }
def WeightedChain' (α : Type) [WeightedPartialOrder α] :=
  { f : ℕ → α // WeightedAntitone f }

instance [WeightedPartialOrder α] : FunLike (WeightedChain α) ℕ α :=
  ⟨(·.val), by intro ⟨a, ha⟩ ⟨b, hb⟩ c; simp_all⟩
instance [WeightedPartialOrder α] : FunLike (WeightedChain' α) ℕ α :=
  ⟨(·.val), by intro ⟨a, ha⟩ ⟨b, hb⟩ c; simp_all⟩

def WeightedChain.map {α β : Type} [WeightedPartialOrder α] [WeightedPartialOrder β]
    (C : WeightedChain α) (f : α → β) (hf : WeightedMonotone f) : WeightedChain β :=
  ⟨fun n ↦ f (C n), fun hab ↦ hf (C.property hab)⟩

class WeightedOmegaCompletePartialOrder (α : Type) extends
    WeightedPartialOrder α where
  wSup : WeightedChain α → α
  /-- wSup is an upper bound of the increasing sequence -/
  le_wSup (c : WeightedChain α) (i : ℕ) : c i ≼ wSup c
  /-- wSup is a lower bound of the set of upper bounds of the increasing sequence -/
  wSup_le (c : WeightedChain α) (x : α) : (∀ (i : ℕ), c i ≼ x) → wSup c ≼ x

open WeightedOmegaCompletePartialOrder in
def WeightedOmegaContinuous {ι : Type} [WeightedOmegaCompletePartialOrder ι]
    [WeightedOmegaCompletePartialOrder α]
    (f : ι → α) (h : WeightedMonotone f) : Prop :=
  ∀ C, f (wSup C) = wSup (C.map f h)

/--
A weighted semiring is _ω-bicontinuous_ iff

1. ≼ is positive, i.e., 𝟘 is the least element.
2. both ⨁ and ⨀ are monotonic in both arguments, i.e. for all s₁,s₂s₃ ∈ α,

  s₂ ≼ s₃ implies s₁ ⨁ s₂ ≼ s₁ ⨁ s₃ and s₁ ⨀ s₂ ≼ s₁ ⨀ s₃ and s₂ ⨀ s₁ ≼ s₃ ⨀ s₁.

3. both ⨁ and ⨀ are ω-continuous in both arguments, i.e. for ∘ ∈ {⨁,⨀}, we have

  ∀ ω-chains C = {s₀ ≼ s₁ ≼ ⋯}, ∀ s ∈ α,
    s ∘ wSup C = wSup (C.map fun s' ↦ s ∘ s')) and wSup C ∘ s = wSup (C.map fun s' ↦ s' ∘ s))
-/
class WeightedOmegaContinuousSemiring (α : Type) [WeightedSemiring α] extends
    WeightedOmegaCompletePartialOrder α where
  /-- 1. ≼ is positive. -/
  wle_positive (a : α) : 𝟘 ≼ a
  /-- 2. both ⨁ and ⨀ are monotonic in both arguments. -/
  wAdd_mono (s₁ : α) : WeightedMonotone (s₁ ⨁ ·)
  wMul_mono_left (s₁ : α) : WeightedMonotone (s₁ ⨀ ·)
  -- wMul_mono_right (s₁ s₂ s₃ : α) (hab : s₂ ≼ s₃) : s₂ ⨀ s₁ ≼ s₃ ⨀ s₁
  wMul_mono_right (s₁ : α) : WeightedMonotone (· ⨀ s₁)
  /-- 3. both ⨁ and ⨀ are ω-continuous in both arguments. -/
  wAdd_wSup (s : α) : WeightedOmegaContinuous (s ⨁ ·) (wAdd_mono s)
  wSup_wAdd (s : α) : WeightedOmegaContinuous (· ⨁ s) (by
    simp only [WeightedSemiring.wAdd_comm]; exact wAdd_mono _)
  wMul_wSup (s : α) : WeightedOmegaContinuous (s ⨀ ·) (wMul_mono_left s)
  wSup_wMul (s : α) : WeightedOmegaContinuous (· ⨀ s) (wMul_mono_right s)

@[simp]
theorem wZero_wLe [WeightedSemiring α] [WeightedOmegaContinuousSemiring α] {x : α} : 𝟘 ≼ x :=
  WeightedOmegaContinuousSemiring.wle_positive x
@[simp]
theorem wLe_wZero_iff [WeightedSemiring α] [WeightedOmegaContinuousSemiring α] {x : α} : x ≼ 𝟘 ↔ x = 𝟘 := by
  constructor
  · intro h
    apply WeightedPartialOrder.wle_antisymm h (WeightedOmegaContinuousSemiring.wle_positive x)
  · rintro ⟨_⟩; simp

def WeightedLE.wle.trans_eq {a b c : α} [WeightedPartialOrder α] (h : a ≼ b) (h' : b = c) :
    a ≼ c := by
  subst_eqs
  assumption

open WeightedPartialOrder WeightedOmegaContinuousSemiring WeightedOmegaCompletePartialOrder in
@[simp]
theorem wSup_eq_zero_iff [WeightedSemiring α] [WeightedOmegaContinuousSemiring α] {C : WeightedChain α} :
    wSup C = 𝟘 ↔ ∀ i, C i = 𝟘 :=
  ⟨fun h i ↦ wLe_wZero_iff.mp <| (le_wSup C i).trans_eq h,
    fun h ↦ wle_antisymm (wSup_le C 𝟘 (wLe_wZero_iff.mpr <| h ·)) (wle_positive (wSup C))⟩

section Pi

variable {X : Type} {𝒮 : Type}

instance WeightedAdd.instPi [WeightedAdd 𝒮] : WeightedAdd (X → 𝒮) where wAdd a b x := a x ⨁ b x
instance WeightedMul.instPi [WeightedMul 𝒮] : WeightedMul (X → 𝒮) where wMul a b x := a x ⨀ b x

attribute [local simp] WeightedAdd.instPi
attribute [local simp] WeightedMul.instPi

instance WeightedSemiring.instPi [WeightedSemiring 𝒮] : WeightedSemiring (X → 𝒮) where
  wZero := fun _ ↦ 𝟘
  wOne := fun _ ↦ 𝟙
  wAdd_assoc := by simp [wAdd_assoc]
  wZero_add := by simp [wZero_add]
  add_wZero := by simp [wZero_add]
  wNsmul n a x := wNsmul n (a x)
  wNsmul_wZero := by simp [wNsmul_wZero]
  wNsmul_succ := by simp [wNsmul_succ]
  wAdd_comm := by simp [wAdd_comm]
  left_distrib := by simp [left_distrib]
  right_distrib := by simp [right_distrib]
  wZero_mul := by simp [wZero_mul]
  mul_wZero := by simp [mul_wZero]
  mul_assoc := by simp [mul_assoc]
  wOne_mul a := by ext x; simp [wOne_mul]
  mul_wOne := by simp [mul_wOne]
  natCast n _ := natCast n
  natCast_zero := by simp [natCast_zero]
  natCast_succ := by simp [natCast_succ]
  wNpow n a b := wNpow n (a b)
  wNpow_zero := by simp [wNpow_zero]
  wNpow_succ := by simp [wNpow_succ]

attribute [local simp] WeightedSemiring.instPi

instance WeightedLE.instPi [WeightedLE 𝒮] : WeightedLE (X → 𝒮) where
  wle a b := ∀ x, a x ≼ b x

open WeightedPartialOrder in
instance WeightedPartialOrder.instPi [WeightedPartialOrder 𝒮] : WeightedPartialOrder (X → 𝒮) where
  wle_refl a x := by simp
  wle_trans {a b c} hab hbc x := wle_trans (hab x) (hbc x)
  wle_antisymm {a b} hab hba := by ext x; exact wle_antisymm (hab x) (hba x)

instance WeightedOmegaCompletePartialOrder.instPi [WeightedOmegaCompletePartialOrder 𝒮] :
    WeightedOmegaCompletePartialOrder (X → 𝒮) where
  wSup C x := wSup ⟨(C · x), (C.prop · x)⟩
  le_wSup C i x := le_wSup ⟨(C · x), (C.prop · x)⟩ i
  wSup_le C _ h x := wSup_le ⟨(C · x), (C.prop · x)⟩ _ (h · x)

open WeightedOmegaContinuousSemiring WeightedOmegaCompletePartialOrder in
instance WeightedOmegaContinuousSemiring.instPi [WeightedSemiring 𝒮]
    [WeightedOmegaContinuousSemiring 𝒮] : WeightedOmegaContinuousSemiring (X → 𝒮) where
  wle_positive _ _ := by simp [wle_positive]
  wAdd_mono s₁ s₂ s₃ h x := wAdd_mono (s₁ x) (h x)
  wMul_mono_left s₁ s₂ s₃ h x := wMul_mono_left (s₁ x) (h x)
  wMul_mono_right s₁ s₂ s₃ h x := wMul_mono_right (s₁ x) (h x)
  wAdd_wSup s C := by ext x; exact wAdd_wSup (s x) (C.map (· x) (· x))
  wSup_wAdd s C := by ext x; exact wSup_wAdd (s x) (C.map (· x) (· x))
  wMul_wSup s C := by ext x; exact wMul_wSup (s x) (C.map (· x) (· x))
  wSup_wMul s C := by ext x; exact wSup_wMul (s x) (C.map (· x) (· x))

end Pi

variable {ι : Type}

/-- `⨁ x ∈ I, f x` is the finite sum over `f`. -/
def WeightedFinsum [WeightedSemiring α] (I : Finset ι) (f : ι → α) : α :=
  I.fold (· ⨁ ·) 𝟘 f
open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousSemiring in
open scoped Classical in
/-- `⨁' x : ι, f x` is the countable sum over `f`. -/
noncomputable def WeightedSum [WeightedSemiring α] [WeightedOmegaContinuousSemiring α]
    [Countable ι] (f : ι → α) : α :=
  if _ : Nonempty ι then
    let e : Encodable ι := Encodable.ofCountable ι
    let f' i := if let some x := e.decode i then f x else 𝟘
    wSup ⟨fun n ↦ n.fold (fun i _ x ↦ f' i ⨁ x) 𝟘, by
      intro a b hab
      obtain ⟨c, _, _⟩ := le_iff_exists_add.mp hab
      induction c with
      | zero => apply wle_refl
      | succ c ih =>
        apply wle_trans (ih (Nat.le_add_right a c)); clear ih hab
        rw [← add_assoc]
        simp only [Nat.fold_succ]
        set q := (a + c).fold (fun i _ x ↦ f' i ⨁ x) 𝟘
        have := wAdd_mono q (wle_positive (f' (a + c)))
        simpa [WeightedSemiring.wAdd_comm]⟩
  else
    𝟘

namespace BigOperators

syntax (name := bigweightedfinsum) "⨁ᶠ " bigOpBinders ("with " term)? ", " term:67 : term

macro_rules (kind := bigweightedfinsum)
  | `(⨁ᶠ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(WeightedFinsum $s (fun $x ↦ $v))

@[inherit_doc WeightedSum]
notation3 "⨁' "(...)", "r:67:(scoped f => WeightedSum f) => r

macro_rules (kind := bigweightedfinsum)
  | `(⨁ᶠ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(WeightedFinsum $s (fun $x ↦ $v))

variable {ι : Type} [WeightedSemiring α]

open Lean Meta
open Elab Term Tactic TryThis

open PrettyPrinter.Delaborator SubExpr
open scoped Batteries.ExtendedBinder

/-- The possibilities we distinguish to delaborate the finset indexing a big operator:
* `finset s` corresponds to `∑ x ∈ s, f x`
* `univ` corresponds to `∑ x, f x`
* `filter s p` corresponds to `∑ x ∈ s with p x, f x`
* `filterUniv p` corresponds to `∑ x with p x, f x`
-/
private inductive FinsetResult where
  | finset (s : Term)
  | univ
  | filter (s : Term) (p : Term)
  | filterUniv (p : Term)

/-- Delaborates a finset indexing a big operator. In case it is a `Finset.filter`, `i` is used for
the binder name. -/
private def delabFinsetArg (i : Ident) : DelabM FinsetResult := do
  let s ← getExpr
  if s.isAppOfArity ``Finset.univ 2 then
    return .univ
  else if s.isAppOfArity ``Finset.filter 4 then
    let #[_, _, _, t] := s.getAppArgs | failure
    let p ←
      withNaryArg 1 do
        if (← getExpr).isLambda then
          withBindingBody i.getId delab
        else
          let p ← delab
          return (← `($p $i))
    if t.isAppOfArity ``Finset.univ 2 then
      return .filterUniv p
    else
      let ss ← withNaryArg 3 delab
      return .filter ss p
  else
    let ss ← delab
    return .finset ss

/-- Delaborator for `WeightedFinsum`. The `pp.funBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[app_delab WeightedFinsum] def delabWeightedFinsum : Delab :=
  whenPPOption getPPNotation <| withOverApp 5 <| do
  let #[_, _, _, _, f] := (← getExpr).getAppArgs | failure
  guard f.isLambda
  let ppDomain ← getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return ((⟨i⟩ : Ident), ← delab)
  let res ← withNaryArg 3 <| delabFinsetArg i
  match res with
  | .finset ss => `(⨁ᶠ $i:ident ∈ $ss, $body)
  | .univ =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(⨁ᶠ $binder:bigOpBinder, $body)
  | .filter ss p =>
    `(⨁ᶠ $i:ident ∈ $ss with $p, $body)
  | .filterUniv p =>
    let binder ←
    if ppDomain then
      let ty ← withNaryArg 0 delab
      `(bigOpBinder| $i:ident : $ty)
    else
      `(bigOpBinder| $i:ident)
    `(⨁ᶠ $binder:bigOpBinder with $p, $body)

/-- info: fun I f ↦ ⨁ᶠ x ∈ I, f x : Finset ι → (ι → α) → α -/
#guard_msgs in
#check fun (I : Finset ι) (f : ι → α) ↦ ⨁ᶠ x ∈ I, f x

variable [Countable ι] [Nonempty ι] [WeightedOmegaContinuousSemiring α]

/-- info: fun f ↦ ⨁' (x : ι), f x : (ι → α) → α -/
#guard_msgs in
#check fun (f : ι → α) ↦ ⨁' x : ι, f x

end BigOperators

section

variable {α : Type}
variable [WeightedSemiring α] [WeightedOmegaContinuousSemiring α]

variable {I : Type} [Countable I]

open WeightedOmegaContinuousSemiring WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedSemiring

@[simp]
theorem wle_wAdd (s s' : α) : s ≼ s ⨁ s' := by
  have := wAdd_mono s (wle_positive s')
  simpa [WeightedSemiring.add_wZero]
theorem WeightedSum_empty [IsEmpty I] (f : I → α) : ⨁' x : I, f x = 𝟘 := by
  simp [WeightedSum]

@[simp]
theorem wAdd_eq_zero_iff {x y : α} : x ⨁ y = 𝟘 ↔ x = 𝟘 ∧ y = 𝟘 := by
  constructor
  · intro h
    constructor
    · apply wle_antisymm (by rw [← h]; apply wle_wAdd) (wle_positive x)
    · apply wle_antisymm (by rw [← h, wAdd_comm]; apply wle_wAdd) (wle_positive y)
  · rintro ⟨⟨_⟩, ⟨_⟩⟩
    exact WeightedSemiring.wZero_add 𝟘
example {x y : α} : x ⨁ y ≠ 𝟘 ↔ x ≠ 𝟘 ∨ y ≠ 𝟘 := by
  simp [wAdd_eq_zero_iff, imp_iff_not_or]

@[simp]
theorem WeightedSum_eq_zero_iff {f : I → α} : ⨁' x, f x = 𝟘 ↔ ∀ x, f x = 𝟘 := by
  constructor
  · intro h a
    simp [WeightedSum, DFunLike.coe] at h
    let e : Encodable I := Encodable.ofCountable I
    replace h := h a (e.encode a + 1)
    simp_all
  · intro hf
    simp [WeightedSum, hf, DFunLike.coe]
    intro a i
    induction i with
    | zero => simp
    | succ i ih =>
      simp only [Nat.fold_succ, wAdd_eq_zero_iff]
      split <;> simp_all

theorem WeightedSum_add {f₁ f₂ : I → α} :
    ⨁' x : I, (f₁ x ⨁ f₂ x) = (⨁' x : I, f₁ x) ⨁ (⨁' x : I, f₂ x) := by
  simp only [WeightedSum, dite_eq_ite]
  by_cases ¬Nonempty I
  · simp_all; simp_all
  simp_all only [not_nonempty_iff, not_isEmpty_iff, ↓reduceIte]
  apply wle_antisymm
  · apply wSup_le
    simp [DFunLike.coe]
    intro n
    sorry
  · sorry

theorem WeightedSum_pair {i₁ i₂ : I} (f : I → α) :
    let X : Set I := {i₁, i₂}
    have : Countable ↑X := by
      simp [X]
      refine countable_iff_exists_surjective.mpr ?_
      exists (if · = 0 then ⟨i₁, by simp⟩ else ⟨i₂, by simp⟩)
      rintro ⟨x, (⟨_, _⟩ | ⟨_, _⟩)⟩
      · exists 0
      · exists 1
    ⨁' i : X, f i = f i₁ ⨁ f i₂ := by
  simp only
  let X : Set I := {i₁, i₂}
  let e : Encodable X := Encodable.ofCountable X
  let n₁ : ℕ := e.encode ⟨i₁, by simp [X]⟩
  let n₂ : ℕ := e.encode ⟨i₂, by simp [X]⟩
  let n_max := n₁ ⊔ n₂
  simp [WeightedSum]
  apply wle_antisymm
  · apply wSup_le
    intro n
    simp [DFunLike.coe]
    sorry
  · apply wle_trans _ (le_wSup _ n_max)
    simp [DFunLike.coe]
    sorry
theorem WeightedSum_mul_left {s : α} (f : I → α) : ⨁' x : I, s ⨀ f x = s ⨀ ⨁' x : I, f x := by
  sorry
theorem WeightedSum_mul_right {s : α} (f : I → α) : ⨁' x : I, f x ⨀ s = (⨁' x : I, f x) ⨀ s := by
  sorry
example {J : Type} [Countable J] (I : J → Set ι) [∀ i, Countable (I i)] (f : (j : J) → I j → α) :
    have : Countable ↑(⋃ j, I j) := sorry
    ⨁' j : J, ⨁' i : I j, f j i = ⨁' i : ↑(⋃ j, I j), f (by sorry) (by sorry) := by
  sorry

end
