module

public meta import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.ENat.Lattice
public import WeightedNetKAT.WeightedSemiring
public import Mathlib.Data.Fintype.Order

/-!

# Weighted semiring instances

We provide a set of proven sound weighted semirings, including instances for Kleene-star and
ω-continuity for these.

Most of the semirings are computable (i.e. have computable instances of `Semiring`), but some,
specifically those that do operations on reals, have noncomputable instances for now.

-/

@[expose] public section

section InstantiationMacros

open Lean Elab PrettyPrinter Delaborator Meta Command Term

-- NOTE: we add instances of `OfNat` to make sure that it behaves "as expected". The default
-- instance after `instantiate_computableSemiring` will map `1` to `𝟙`, which, for example, is `0`
-- for `Arctic`, leading to nonsensical/unexpected results

elab c:declModifiers "instantiate_computableSemiring" b:term " => " a:term : command => do
  elabCommand <|← `($c:declModifiers instance : Semiring $a := WSemiring.toSemiring $b)
  elabCommand <|← `($c:declModifiers instance : KStar $a := WKStar.toKStar $b)
  elabCommand <|← `($c:declModifiers instance : PartialOrder $a := WPartialOrder.toPartialOrder $b)
  elabCommand <|← `($c:declModifiers instance : DecidableLE $a := WPartialOrder.toDecidableLE $b)
  elabCommand <|← `(noncomputable instance : OmegaCompletePartialOrder $a := WOmegaCompletePartialOrder.toOmegaCompletePartialOrder $b)
  elabCommand <|← `(noncomputable instance : OrderBot $a := WOmegaContinuousNonUnitalSemiring.toOrderBot $b)
  elabCommand <|← `(noncomputable instance : IsPositiveOrderedAddMonoid $a := WOmegaContinuousNonUnitalSemiring.toIsPositiveOrderedAddMonoid $b)
  elabCommand <|← `(noncomputable instance : MulLeftMono $a := WOmegaContinuousNonUnitalSemiring.toMulLeftMono $b)
  elabCommand <|← `(noncomputable instance : MulRightMono $a := WOmegaContinuousNonUnitalSemiring.toMulRightMono $b)
  elabCommand <|← `(noncomputable instance : LawfulKStar $a := LawfulWKStar.toLawfulKStar $b)
  elabCommand <|← `(noncomputable instance : OmegaContinuousNonUnitalSemiring $a := WOmegaContinuousNonUnitalSemiring.toOmegaContinuousNonUnitalSemiring $b)
  elabCommand <|← `(instance {n : ℕ} [inst : OfNat $b n] : OfNat $a n := ⟨inst.ofNat⟩)
  elabCommand <|← `(instance [inst : Repr $b] : Repr $a := inst)

end InstantiationMacros

namespace ENat.WithBot

instance : Repr (WithBot ENat) :=
  ⟨fun a n ↦ match a with | ⊥ => "⊥" | some ⊤ => "⊤" | some (some x) => reprPrec x n⟩

theorem cases_on {P : WithBot ENat → Prop} (x : WithBot ENat)
    (bot : P ⊥) (top : P ⊤) (nat : ∀ (a : ℕ), P ↑a) : P x := by
  rcases x with _ | _ | _ <;> apply_assumption

@[simp]
theorem top_add {x : WithBot ENat} (hx : x ≠ ⊥) : (⊤ : WithBot ENat) + x = ⊤ := by
  simp_all [WithBot.ne_bot_iff_exists]
  obtain ⟨x, ⟨_⟩⟩ := hx
  exact (ENat.WithBot.one_add_cancel.mp rfl).symm
@[simp]
theorem add_top {x : WithBot ENat} (hx : x ≠ ⊥) : x + (⊤ : WithBot ENat) = ⊤ := by
  rw [add_comm]; simp [hx]

@[simp]
theorem add_eq_top_iff {x y : WithBot ENat} : x + y = ⊤ ↔ (x = ⊤ ∧ y ≠ ⊥) ∨ (x ≠ ⊥ ∧ y = ⊤) := by
  constructor
  · intro h
    simp_all
    if hx : x = ⊤ then
      subst_eqs
      simp_all
      if y = ⊤ then
        subst_eqs
        simp
      else
        simp_all
        rintro ⟨_⟩
        simp_all
    else
      simp_all
      if hy : y = ⊤ then
        subst_eqs
        simp_all
        rintro ⟨_⟩
        simp_all
      else
        simp_all
        contrapose! h
        if hxy : x = ⊥ ∨ y = ⊥ then
          rcases hxy with (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) <;> simp
        else
          simp_all [WithBot.ne_bot_iff_exists]
          obtain ⟨⟨x, _, _⟩, ⟨y, _, _⟩⟩ := hxy
          simp_all [ENat.ne_top_iff_exists]
          obtain ⟨x, _, _⟩ := hx
          obtain ⟨y, _, _⟩ := hy
          simp_all
          exact ne_of_beq_false rfl
  · rintro (h | h) <;> simp_all

theorem add_top_eq {x : WithBot ENat} : x + ⊤ = if x = ⊥ then ⊥ else ⊤ := by
  induction x using ENat.WithBot.cases_on with
  | bot => simp
  | top => simp
  | nat => simp
theorem iSup_eq_bot {ι : Type*} {f : ι → WithBot ENat} : (⨆ i, f i) = ⊥ ↔ (∀ (i : ι), f i = ⊥) := by
  simp only [_root_.iSup_eq_bot]

theorem iSup_eq_' {ι : Type*} [Nonempty ι] {f : ι →  WithBot ENat} (h : ∃ i, f i ≠ ⊥) :
    (⨆ i, f i) = ⨆ i, (f i).unbotD 0 := by
  rw [WithBot.coe_iSup] <;> simp_all
  apply le_antisymm
  · simp
    intro i
    if hf : f i = ⊥ then
      simp [hf]
    else
      apply le_iSup_of_le i
      simp_all [WithBot.le_coe_unbotD]
  · simp
    intro i
    if hf : f i = ⊥ then
      simp [hf]
      obtain ⟨j, hj⟩ := h
      apply le_iSup_of_le j
      simp [WithBot.ne_bot_iff_exists] at hj
      obtain ⟨x, hx⟩ := hj
      rw [← hx]
      simp
    else
      apply le_iSup_of_le i
      convert_to f i ≤ f i
      · simp [WithBot.ne_bot_iff_exists] at hf
        obtain ⟨x, hx⟩ := hf
        rw [← hx]
        simp
      · rfl

theorem iSup_add {ι : Type*} [Nonempty ι] {f : ι →  WithBot ENat} {a : WithBot ENat} :
    (⨆ i, f i) + a = ⨆ i, f i + a := by
  classical
  induction a using ENat.WithBot.cases_on with
  | bot => simp
  | top =>
    simp [ENat.WithBot.add_top_eq]
    split_ifs with h
    · simp_all
    · symm
      simp_all [iSup_eq_top]
      obtain ⟨e, h⟩ := h
      intro b hb
      use e
      grind
  | nat a =>
    if hf : ∃ (i : ι), f i ≠ ⊥ then
      simp_all [iSup_eq_']
      show some ((⨆ i, (f i).unbotD _) + a) = _
      simp [ENat.iSup_add]
      simp [WithBot.ne_bot_iff_exists] at hf
      obtain ⟨j, hx⟩ := hf
      obtain ⟨x, hx⟩ := hx
      congr! 1
      apply le_antisymm
      · apply iSup_le fun i ↦ ?_
        if hf : f i = ⊥ then
          apply le_iSup_of_le j
          simp [hf, ← hx]
          apply le_trans (self_le_add_left ↑a x) (ENat.forall_natCast_le_iff_le.mp fun _ a ↦ a)
        else
          simp [WithBot.ne_bot_iff_exists] at hf
          apply le_iSup_of_le i
          obtain ⟨k, hk⟩ := hf; simp [← hk]; rfl
      · apply iSup_le fun i ↦ ?_
        if hf : f i = ⊥ then
          simp [hf]
        else
          simp [WithBot.ne_bot_iff_exists] at hf
          apply le_iSup_of_le i
          obtain ⟨k, hk⟩ := hf; simp [← hk]; rfl
    else
      simp_all

theorem add_iSup {ι : Type*} [Nonempty ι] {f : ι →  WithBot ENat} {a : WithBot ENat} :
    a + (⨆ i, f i) = ⨆ i, a + f i := by grind [add_comm, iSup_add]

end ENat.WithBot

namespace Weighted

def Tropical := ENat deriving DecidableEq, Top

namespace Tropical

def min (a b : ENat) : ENat := if a ≤ b then a else b
@[simp] theorem min_eq_sup (a b : ENat) : min a b = a ⊓ b := by
  by_cases a ≤ b <;> simp_all [min, le_of_lt]

local instance : WSemiring ENat where
  wadd := min
  wmul := (· + ·)
  wzero := ⊤
  wone := 0
  wnsmul n x := if n = 0 then ⊤ else x
  wnsmul_succ := by simp; rintro (_ | _) <;> simp
  left_distrib := by simp [add_min]
  right_distrib := by simp [min_add]

local instance : WLE ENat where
  wle := (· ≥ ·)

local instance : WPartialOrder ENat where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₂ h₁
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₂ h₁

noncomputable local instance : WOmegaContinuousNonUnitalSemiring ENat where
  wωSup f h := ⨅ i, f i
  wle_wωSup := by simp [iInf_le]
  wωSup_wle := by simp
  wadd_left_mono := by simp; grind
  wadd_right_mono := by simp; grind
  wmul_left_mono := by simp +contextual [add_le_add_right]
  wmul_right_mono := by simp +contextual [add_le_add_left]
  wωScottContinuous_wadd_left := by simp [inf_iInf]
  wωScottContinuous_wadd_right := by simp [iInf_inf]
  wωScottContinuous_wmul_left := by simp [ENat.add_iInf]
  wωScottContinuous_wmul_right := by simp [ENat.iInf_add]

scoped instance : WKStar ENat where
  wkstar _ := 𝟙

noncomputable scoped instance : LawfulWKStar ENat where
  wkstar_eq_sum m := by
    simp [WOmegaCompletePartialOrder.wωSup]
    rw [← Antitone.iInf_nat_add (k := 3)]
    · simp [wstarn, wone, wkstar]
    · refine antitone_nat_of_succ_le ?_
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        simp_all [wstarn]
        grind only [instWOmegaContinuousNonUnitalSemiringENat._simp_10, = min_def]

instantiate_computableSemiring ENat => Tropical

end Tropical

def Arctic := WithBot ENat deriving DecidableEq, Top

namespace Arctic

def max : WithBot ENat → WithBot ENat → WithBot ENat
  | _, some ⊤ | some ⊤, _ => ⊤
  | some (some a), some (some b) => some (some (a ⊔ b))
  | ⊥, x | x, ⊥ => x

@[simp] theorem max_eq_sup (a b : WithBot ENat) : max a b = a ⊔ b := by
  by_cases ha : a = ⊥ <;> by_cases hb : b = ⊥ <;> subst_eqs <;> (try rfl) <;> simp [WithBot.ne_bot_iff_exists] at *
  all_goals try obtain ⟨a, ⟨_⟩⟩ := ha
  all_goals try obtain ⟨b, ⟨_⟩⟩ := hb
  all_goals try by_cases ha : a = ⊤
  all_goals try by_cases hb : b = ⊤
  all_goals subst_eqs; (try rfl) <;> simp [ENat.ne_top_iff_exists] at *
  all_goals try obtain ⟨a, ⟨_⟩⟩ := ha
  all_goals try obtain ⟨b, ⟨_⟩⟩ := hb
  all_goals rfl

def add : WithBot ENat → WithBot ENat → WithBot ENat
  | ⊥, _ | _, ⊥ => ⊥
  | _, some ⊤ | some ⊤, _ => ⊤
  | some (some a), some (some b) => some (some (a + b))

@[simp] theorem add_eq_hadd (a b : WithBot ENat) : add a b = a + b := by
  by_cases ha : a = ⊥ <;> by_cases hb : b = ⊥ <;> subst_eqs <;> (try rfl) <;> simp [WithBot.ne_bot_iff_exists] at *
  all_goals try obtain ⟨a, ⟨_⟩⟩ := ha
  all_goals try obtain ⟨b, ⟨_⟩⟩ := hb
  all_goals try by_cases ha : a = ⊤
  all_goals try by_cases hb : b = ⊤
  all_goals subst_eqs; (try rfl) <;> simp [ENat.ne_top_iff_exists] at *
  all_goals try obtain ⟨a, ⟨_⟩⟩ := ha
  all_goals try obtain ⟨b, ⟨_⟩⟩ := hb
  all_goals try rfl

scoped instance : WSemiring (WithBot ENat) where
  wadd := max
  wmul := add
  wzero := ⊥
  wone := 0
  wnsmul n x := if n = 0 then ⊥ else x
  wnsmul_succ := by simp; rintro (_ | _) <;> simp
  left_distrib := by simp [add_max]
  right_distrib := by simp [max_add]

scoped instance : WLE (WithBot ENat) := ⟨(· ≤ ·)⟩
scoped instance : WPartialOrder (WithBot ENat) where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₁ h₂
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₁ h₂

noncomputable scoped instance : WOmegaContinuousNonUnitalSemiring (WithBot ENat) where
  wωSup f h := ⨆ i, f i
  wle_wωSup := by simp [le_iSup]
  wωSup_wle := by simp
  wadd_left_mono := by simp; grind
  wadd_right_mono := by simp; grind
  wmul_left_mono := by simp +contextual [add_le_add_right]
  wmul_right_mono := by simp +contextual [add_le_add_left]
  wωScottContinuous_wadd_left := by simp [sup_iSup]
  wωScottContinuous_wadd_right := by simp [iSup_sup]
  wωScottContinuous_wmul_left := by simp [ENat.WithBot.add_iSup]
  wωScottContinuous_wmul_right := by simp [ENat.WithBot.iSup_add]

scoped instance : WKStar (WithBot ENat) where
  wkstar a := if a ≤ 0 then 0 else ⊤

noncomputable scoped instance : LawfulWKStar (WithBot ENat) where
  wkstar_eq_sum a := by
    simp [WOmegaCompletePartialOrder.wωSup]
    have h₀ {a : WithBot ENat} {i} : (wstarn a (i + 1) : WithBot ENat) = if a = ⊥ then 0 else i * a := by
      if ha : a = ⊥ then
        subst_eqs
        rcases i with _ | i
        · simp [wstarn, wone]
        rw [WithBot.mul_bot (Nat.cast_add_one_ne_zero i)]
        simp [wstarn, wone]
      else
        simp_all [WithBot.ne_bot_iff_exists]
        obtain ⟨a, ⟨_⟩⟩ := ha
        induction i with
        | zero => simp [wstarn, wone]
        | succ i ih =>
          simp_all [wstarn, wone, add_mul]
          rw [add_comm]
          if a = 0 then
            bound
          else if 0 ≤ ↑i * a + a then
            simp_all [mul_nonneg, add_nonneg]
          else
            simp_all
    if ha : a = ⊥ then
      subst_eqs
      rw [← sup_iSup_nat_succ]
      simp [wkstar, h₀]
    else
      rw [← sup_iSup_nat_succ]
      simp [wkstar, h₀]
      symm
      split_ifs with h
      · simp_all [WithBot.ne_bot_iff_exists]
        obtain ⟨a, _, _⟩ := ha
        simp_all
      · simp_all [iSup_eq_top]
        intro b hb
        if hb : b = ⊥ then
          use 1
          subst_eqs
          simp_all [WithBot.bot_lt_iff_ne_bot]
        else
          simp_all [WithBot.ne_bot_iff_exists]
          obtain ⟨b, _, _⟩ := hb
          obtain ⟨a, _, _⟩ := ha
          simp_all [lt_top_iff_ne_top, ENat.ne_top_iff_exists]
          obtain ⟨b, _, _⟩ := hb
          use (b + 1)
          simp_all [add_mul, ← ENat.WithBot.add_one_le_iff]
          by_cases ha : a = ⊤ <;> try simp_all [ENat.ne_top_iff_exists]
          · bound
          · obtain ⟨(_ | a), _, _⟩ := ha
            · simp_all
            · simp_all [mul_add]
              bound

instantiate_computableSemiring WithBot ENat => Arctic

-- see note at top of file
/-- info: some (some 1) -/
#guard_msgs in #eval (1 : Arctic)
/-- info: some (some 0) -/
#guard_msgs in #eval ((𝟙 : WithBot ENat) : Arctic)

end Arctic

def Boolean := Bool deriving DecidableEq, Top

namespace Boolean

scoped instance : WSemiring Bool where
  wadd := (· ∨ ·)
  wmul := (· ∧ ·)
  wzero := False
  wone := True
  wnsmul n x := if n = 0 then False else x
  wnsmul_succ := by simp
  left_distrib := by simp
  right_distrib := by simp

scoped instance : WLE Bool := ⟨(· ≤ ·)⟩
scoped instance : WPartialOrder Bool where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₁ h₂
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₁ h₂

noncomputable scoped instance : WOmegaContinuousNonUnitalSemiring Bool where
  wωSup f h := ⨆ i, f i
  wle_wωSup := by simp [le_iSup]
  wωSup_wle := by simp
  wadd_left_mono := by simp
  wadd_right_mono := by simp
  wmul_left_mono := by simp
  wmul_right_mono := by simp
  wωScottContinuous_wadd_left := by simp
  wωScottContinuous_wadd_right := by simp
  wωScottContinuous_wmul_left := by simp
  wωScottContinuous_wmul_right := by simp

scoped instance : WKStar Bool where
  wkstar _ := ⊤

noncomputable scoped instance : LawfulWKStar Bool where
  wkstar_eq_sum a := by
    simp [WOmegaCompletePartialOrder.wωSup]
    rw [← Monotone.iSup_nat_add (k := 1) wstarn_mono]
    simp [wstarn, wkstar, wone]

instantiate_computableSemiring Bool => Boolean

end Boolean

def Bottleneck := WithBot ENat deriving DecidableEq, Top

namespace Bottleneck

def max (a b : WithBot ENat) : WithBot ENat := if a ≤ b then b else a
@[simp] theorem max_eq_sup (a b : WithBot ENat) : max a b = a ⊔ b := by
  by_cases a ≤ b <;> simp_all [max, le_of_lt]

def min (a b : WithBot ENat) : WithBot ENat := if a ≤ b then a else b
@[simp] theorem min_eq_sup (a b : WithBot ENat) : min a b = a ⊓ b := by
  by_cases a ≤ b <;> simp_all [min, le_of_lt]

scoped instance : WSemiring (WithBot ENat) where
  wadd := max
  wmul := min
  wzero := ⊥
  wone := ⊤
  wnsmul n x := if n = 0 then ⊥ else x
  wnsmul_succ := by simp; rintro (_ | _) <;> simp
  left_distrib := by simp [min_max_distrib_left]
  right_distrib := by simp [min_max_distrib_right]

scoped instance : WLE (WithBot ENat) := ⟨(· ≤ ·)⟩
scoped instance : WPartialOrder (WithBot ENat) where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₁ h₂
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₁ h₂

noncomputable scoped instance : WOmegaContinuousNonUnitalSemiring (WithBot ENat) where
  wωSup f h := ⨆ i, f i
  wle_wωSup := by simp [le_iSup]
  wωSup_wle := by simp
  wadd_left_mono := by simp_all [LE.le.ge_or_le]
  wadd_right_mono := by simp_all [or_comm, LE.le.ge_or_le]
  wmul_left_mono := by simp_all
  wmul_right_mono := by simp_all
  wωScottContinuous_wadd_left := by simp [sup_iSup]
  wωScottContinuous_wadd_right := by simp [iSup_sup]
  wωScottContinuous_wmul_left := by simp [inf_iSup_eq]
  wωScottContinuous_wmul_right := by simp [iSup_inf_eq]

scoped instance : WKStar (WithBot ENat) where
  wkstar _ := ⊤

noncomputable scoped instance : LawfulWKStar (WithBot ENat) where
  wkstar_eq_sum a := by
    simp [WOmegaCompletePartialOrder.wωSup]
    rw [← Monotone.iSup_nat_add (k := 1) wstarn_mono]
    simp [wstarn, wkstar, wone]

instantiate_computableSemiring WithBot ENat => Bottleneck

end Bottleneck

def ENNReal' := ENNReal deriving Top

namespace ENNReal

noncomputable scoped instance : WSemiring ENNReal where
  wadd := (· + ·)
  wmul := (· * ·)
  wzero := 0
  wone := 1
  wnsmul n x := n * x
  wnsmul_succ := by simp [add_mul]
  left_distrib := by simp [mul_add]
  right_distrib := by simp [add_mul]

scoped instance : WLE ENNReal := ⟨(· ≤ ·)⟩
noncomputable scoped instance : WPartialOrder ENNReal where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₁ h₂
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₁ h₂
  decidableWLE := Classical.decRel wle

noncomputable scoped instance : WOmegaContinuousNonUnitalSemiring ENNReal where
  wωSup f h := ⨆ i, f i
  wle_wωSup := by simp [le_iSup]
  wωSup_wle := by simp
  wadd_left_mono := by simp_all; intros; gcongr
  wadd_right_mono := by simp_all; intros; gcongr
  wmul_left_mono := by simp_all; intros; gcongr
  wmul_right_mono := by simp_all; intros; gcongr
  wωScottContinuous_wadd_left := by simp [ENNReal.add_iSup]
  wωScottContinuous_wadd_right := by simp [ENNReal.iSup_add]
  wωScottContinuous_wmul_left := by simp [ENNReal.mul_iSup]
  wωScottContinuous_wmul_right := by simp [ENNReal.iSup_mul]

noncomputable scoped instance : WKStar ENNReal where
  wkstar r := (1 - r)⁻¹

noncomputable scoped instance : LawfulWKStar ENNReal where
  wkstar_eq_sum a := by
    simp [WOmegaCompletePartialOrder.wωSup, wkstar]
    rw [← ENNReal.tsum_geometric, ENNReal.tsum_eq_iSup_nat]
    congr with i
    induction i with
      simp_all [Finset.sum_range_succ', wstarn, wone, pow_succ', ← Finset.mul_sum, add_comm]

noncomputable instantiate_computableSemiring ENNReal => ENNReal'

end ENNReal

abbrev Viterbi.PReal : Submonoid ENNReal where
  carrier := {r | r ≤ 1}
  mul_mem' := by simp +contextual [Right.mul_le_one]
  one_mem' := by simp

-- NOTE: We need to put `Type` explicitly here, otherwise `Submonoid ENNReal` leaks through
def Viterbi : Type := Viterbi.PReal

namespace Viterbi

noncomputable instance : MulZeroClass PReal where
  zero := ⟨0, by simp⟩
  zero_mul := by intro; ext; apply zero_mul
  mul_zero := by intro; ext; apply mul_zero

@[simp] theorem PReal.zero_le {p : PReal} : 0 ≤ p := Subtype.coe_le_coe.mp (OrderBot.bot_le _)
@[simp] theorem PReal.zero_le_coe {p : PReal} : 0 ≤ p.val := OrderBot.bot_le _
@[simp] theorem PReal.one_le {p : PReal} : p ≤ 1 := Subtype.coe_le_coe.mp p.prop
@[simp] theorem PReal.one_le_coe {p : PReal} : p.val ≤ 1 := p.prop

noncomputable instance : CompleteLattice PReal where
  sSup S := ⟨sSup (Subtype.val '' S), by simp +contextual⟩
  sInf S := ⟨sInf (Subtype.val '' S) ⊓ 1, by simp +contextual⟩
  top := 1
  bot := 0
  le_top := by simp
  bot_le := by simp
  isLUB_sSup S := by
    have := isLUB_sSup (Subtype.val '' S)
    simp_all [IsLUB, IsLeast, upperBounds, lowerBounds]
  isGLB_sInf S := by
    have := isGLB_sInf (Subtype.val '' S)
    simp_all [IsGLB, IsGreatest, upperBounds, lowerBounds]

noncomputable scoped instance : WSemiring PReal where
  wadd := (· ⊔ ·)
  wmul := (· * ·)
  wzero := 0
  wone := 1
  wnsmul n x := if n = 0 then 0 else ⟨x, by simp⟩
  wnsmul_succ := by simp; rintro (_ | n) a ha <;> simp
  wnsmul_zero := by simp
  left_distrib  := by simp; intro a ha b hb c hc; ext; convert (max_mul_mul_left a b c).symm
  right_distrib := by simp; intro a ha b hb c hc; ext; convert (max_mul_mul_right a b c).symm

scoped instance : WLE PReal := ⟨(· ≤ ·)⟩
noncomputable scoped instance : WPartialOrder PReal where
  wle_trans h₁ h₂ := by simp_all; apply le_trans h₁ h₂
  wle_antisymm a b h₁ h₂ := by simp_all; apply le_antisymm h₁ h₂
  decidableWLE := Classical.decRel wle

@[simp]
theorem PReal.iSup_val {f : ℕ → PReal} : (⨆ i, f i).val = ⨆ i, (f i).val := by
  have {x y : ENNReal} (hx hy) : x ≤ y ↔ (⟨x, hx⟩ : PReal) ≤ (⟨y, hy⟩ : PReal) := ge_iff_le
  apply le_antisymm <;> simp +contextual [this, Subtype.coe_le_coe.mp, le_iSup_iff]

noncomputable scoped instance : WOmegaContinuousNonUnitalSemiring PReal where
  wωSup f h := ⨆ i, f i
  wle_wωSup := by simp [le_iSup]
  wωSup_wle := by simp
  wadd_left_mono := by simp_all [LE.le.ge_or_le]
  wadd_right_mono := by simp_all [or_comm, LE.le.ge_or_le]
  wmul_left_mono := by simp_all; intros; gcongr
  wmul_right_mono := by simp_all; intros; gcongr
  wωScottContinuous_wadd_left := by simp [sup_iSup]
  wωScottContinuous_wadd_right := by simp [iSup_sup]
  wωScottContinuous_wmul_left := by simp; intros; ext; simp [ENNReal.mul_iSup]
  wωScottContinuous_wmul_right := by simp; intros; ext; simp [ENNReal.iSup_mul]

noncomputable scoped instance : WKStar PReal where
  wkstar _ := 1

noncomputable scoped instance : LawfulWKStar PReal where
  wkstar_eq_sum a := by
    simp [WOmegaCompletePartialOrder.wωSup]
    rw [← Monotone.iSup_nat_add (k := 1) wstarn_mono]
    simp [wstarn, wkstar, wone]

noncomputable instantiate_computableSemiring PReal => Viterbi

end Viterbi

end Weighted
