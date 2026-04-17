module

public import WeightedNetKAT.Computation
public import WeightedNetKAT.Star
public import WeightedNetKAT.Instances.ENat
public import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.Tropical.Lattice
public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open OmegaCompletePartialOrder

def Arctic := WithBot ℕ∞ deriving DecidableEq

namespace Arctic

def arc (n : WithBot ℕ∞) : Arctic := n
def unarc (a : Arctic) : WithBot ℕ∞ := a

@[simp] theorem arc_unarc {a} : arc (unarc a) = a := rfl
@[simp] theorem unarc_arc {a} : unarc (arc a) = a := rfl

theorem eq_of_unarc {a b} (h : unarc a = unarc b) : a = b := by convert h
theorem eq_of_arc {a b} (h : arc a = arc b) : a = b := by convert h

def max' : Arctic → Arctic → Arctic
  | some a, some b => if a ≤ b then arc b else arc a
  | _, some b | some b, _ => arc b
  | none, none => arc ⊥
def min' : Arctic → Arctic → Arctic
  | some a, some b => if a ≤ b then arc a else arc b
  | none, _ | _, none => arc ⊥

@[simp]
theorem max'_eq_unarc_sup {a b} : max' a b = unarc a ⊔ unarc b := by
  simp [max']
  rcases a with _ | a <;> rcases b with _ | b
  · simp_all; rfl
  · simp_all; rfl
  · simp_all; rfl
  · simp_all
    split_ifs with h
    · rw [max_eq_right]
      · rfl
      · simp [unarc]
        simp [WithBot.le_def]
        use a, b, h; split_ands <;> rfl
    · rw [max_eq_left]
      · rfl
      · simp [unarc]
        simp [WithBot.le_def]
        simp at h
        use b, a, h.le; split_ands <;> rfl

@[simp]
theorem min'_eq_unarc_inf {a b} : min' a b = unarc a ⊓ unarc b := by
  simp [min']
  rcases a with _ | a <;> rcases b with _ | b
  · simp_all; rfl
  · simp_all; rfl
  · simp_all; rfl
  · simp_all
    split_ifs with h
    · rw [min_eq_left]
      · rfl
      · simp [unarc]
        simp [WithBot.le_def]
        use a, b, h; split_ands <;> rfl
    · rw [min_eq_right]
      · rfl
      · simp [unarc]
        simp [WithBot.le_def]
        simp at h
        use b, a, h.le; split_ands <;> rfl

instance : PartialOrder Arctic where
  le a b := unarc a ≤ unarc b
  le_refl a := le_refl a.unarc
  le_trans a b c h₁ h₂ := Preorder.le_trans a.unarc b.unarc c.unarc h₁ h₂
  le_antisymm a b hab hba := by have := le_antisymm hab hba; exact this

@[simp] theorem le_def {x y : Arctic} : x ≤ y ↔ x.unarc ≤ y.unarc := by rfl

@[simp]
theorem arctic_lt_iff {x y : Arctic} : x < y ↔ x.unarc ≤ y.unarc ∧ ¬y.unarc ≤ x.unarc := by
  simp [le_def, lt_iff_le_and_ne, unarc]
  intro h
  rfl


theorem arc_le {x y} : arc x ≤ arc y ↔ x ≤ y := by simp
theorem unarc_le {x y} : unarc x ≤ unarc y ↔ x ≤ y := by simp
theorem arc_lt {x y} : arc x < arc y ↔ x < y := by simp; exact le_of_lt
theorem unarc_lt {x y} : unarc x < unarc y ↔ x < y := by simp; exact le_of_lt

@[gcongr]
theorem unarc_le_of {x y} (h : x ≤ y) : unarc x ≤ unarc y := by rw [unarc_le]; exact h

instance : Top Arctic := inferInstanceAs (Top (WithBot ℕ∞))
instance : Bot Arctic := inferInstanceAs (Bot (WithBot ℕ∞))
instance : OrderTop Arctic where
  le_top _ := le_top (α:=WithBot ℕ∞)
instance : OrderBot Arctic where
  bot_le _ := bot_le (α:=WithBot ℕ∞)
instance : SemilatticeSup Arctic where
  sup := max'
  le_sup_left a b := by simp; apply le_sup_left
  le_sup_right a b := by simp; apply le_sup_right
  sup_le := by
    simp
    intro a b c hac hbc
    if h : a.unarc ≤ b.unarc then
      simp [h]
      exact hbc
    else
      simp at h
      simp [h.le]
      exact hac
instance : SemilatticeInf Arctic where
  inf := min'
  inf_le_left a b := by simp; apply inf_le_left
  inf_le_right a b := by simp; apply inf_le_right
  le_inf := by
    simp
    intro a b c hab hac
    if h : b.unarc ≤ c.unarc then
      simp [h]
      exact hab
    else
      simp at h
      simp [h.le]
      exact hac
instance : Lattice Arctic where
noncomputable instance : CompleteLattice Arctic where
  sSup c := arc (sSup (unarc '' c))
  sInf c := arc (sInf (unarc '' c))
  isLUB_sSup c := by
    constructor
    · simp [upperBounds]
      intro x h
      have := le_sSup (s:=unarc '' c) (a:=unarc x) ?_
      · have := arc_le.mp this; exact this
      · simp; use x
    · simp [lowerBounds]
      intro x h
      have := sSup_le (s:=unarc '' c) (a:=unarc x) ?_
      · have := arc_le.mp this; simp_all
      · simp; apply h
  isGLB_sInf c := by
    constructor
    · simp [lowerBounds]
      intro x h
      have := sInf_le (s:=unarc '' c) (a:=unarc x) ?_
      · have := arc_le.mp this; exact this
      · simp; use x
    · simp [upperBounds]
      intro x h
      have := le_sInf (s:=unarc '' c) (a:=unarc x) ?_
      · have := arc_le.mp this; simp_all
      · simp; apply h
@[simp] instance : Zero Arctic := ⟨arc ⊥⟩
@[simp] instance : One Arctic := ⟨arc 0⟩
instance : Add Arctic := ⟨fun a b ↦ a ⊔ b⟩
instance : Mul Arctic := ⟨fun a b ↦ arc (unarc a + unarc b)⟩

@[simp] theorem zero_eq_arc_bot : (0 : Arctic) = arc ⊥ := rfl
@[simp] theorem one_eq_arc_0 : (1 : Arctic) = arc 0 := rfl

@[simp] theorem add_eq_sup {a b : Arctic} : a + b = a ⊔ b := by rfl
@[simp] theorem mul_eq_add {a b : Arctic} : a * b = arc (unarc a + unarc b) := by rfl

@[simp] theorem unarc_sup {a b : Arctic} : unarc (a ⊔ b) = unarc a ⊔ unarc b := by
  simp [← max'_eq_unarc_sup]; rfl
@[simp] theorem unarc_inf {a b : Arctic} : unarc (a ⊓ b) = unarc a ⊓ unarc b := by
  simp [← min'_eq_unarc_inf]; rfl
@[simp] theorem arc_sup {a b : WithBot ℕ∞} : arc (a ⊔ b) = arc a ⊔ arc b := max'_eq_unarc_sup.symm
@[simp] theorem arc_inf {a b : WithBot ℕ∞} : arc (a ⊓ b) = arc a ⊓ arc b := min'_eq_unarc_inf.symm

@[simp] theorem unarc_bot : unarc ⊥ = ⊥ := by rfl
@[simp] theorem unarc_top : unarc ⊤ = ⊤ := by rfl

instance : Semiring Arctic where
  add_assoc := sup_assoc
  add_comm := sup_comm
  mul_assoc := by simp [add_assoc]
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  zero_mul := by simp
  mul_zero := by simp
  one_mul := by simp
  mul_one := by simp
  left_distrib := by simp [add_max]
  right_distrib := by simp [max_add]
  nsmul n x := if n = 0 then arc ⊥ else x
  nsmul_succ _ _ := by
    simp
    split_ifs
    · subst_eqs; apply bot_le
    · simp_all
  nsmul_zero _ := by simp

instance : IsPositiveOrderedAddMonoid Arctic where
  add_le_add_right _ _ h _ := by simp [le_sup_of_le_right h]
  add_le_add_left _ _ h _ := by simp [le_sup_of_le_left h]
  bot_eq_zero := rfl

instance : MulLeftMono Arctic := ⟨fun _ _ _ h ↦ add_right_mono (α:=WithBot ℕ∞) h⟩
instance : MulRightMono Arctic := ⟨fun _ _ _ h ↦ add_left_mono (α:=WithBot ℕ∞) h⟩

instance : AddLeftMono (WithBot ℕ∞) := ⟨fun _ _ _ h ↦ add_right_mono (α:=WithBot ℕ∞) h⟩
instance : AddRightMono (WithBot ℕ∞) := ⟨fun _ _ _ h ↦ add_left_mono (α:=WithBot ℕ∞) h⟩

open OmegaCompletePartialOrder

@[simp]
theorem le_iff_le' :
      @LE.le (WithBot ℕ∞) instCompleteLattice.toCompleteSemilatticeInf.toLE
    = @LE.le Arctic instCompleteLattice.toCompleteSemilatticeInf.toLE := by rfl

@[simp]
theorem lt_iff_lt' :
      @LT.lt (WithBot ℕ∞) instCompleteLattice.toCompleteSemilatticeInf.toLT
    = @LT.lt Arctic instCompleteLattice.toCompleteSemilatticeInf.toLT := by rfl

@[simp]
theorem iSup_eq_iSup' {α} :
      @iSup (WithBot ℕ∞) α WithBot.instSupSet
    = @iSup Arctic α instCompleteLattice.toCompleteSemilatticeSup.toSupSet := by
  ext f
  apply le_antisymm
  · simp; apply @le_iSup _ _ instCompleteLattice
  · apply @iSup_le _ _ instCompleteLattice
    simp; intro i
    have : @LE.le (WithBot ℕ∞) instCompleteLattice.toCompleteSemilatticeInf.toLE (f i) (iSup f) :=
      le_iSup_iff.mpr fun b a ↦ a i
    exact this

@[simp]
theorem unarc_iSup {α} {f : α → Arctic} : unarc (⨆ i, f i) = ⨆ i, unarc (f i) := by
  simp [unarc]
@[simp]
theorem arc_iSup {α} {f : α → WithBot ℕ∞} : arc (⨆ i, f i) = ⨆ i, arc (f i) := by
  simp [arc]
  -- apply le_antisymm <;> simp <;> intro i
  -- · have := le_iSup_of_le (f:=f) (a:=f i) i (by rfl)
  --   rw [le_iff_le', iSup_eq_iSup']
  --   exact this
  -- · simp
instance : OmegaContinuousNonUnitalSemiring Arctic where
  ωScottContinuous_add_left a := by
    simp
    refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
    simp [ωSup, sup_iSup]
    intro x y h; simp_all only [sup_le_iff, le_sup_left, le_sup_of_le_right, and_self]
  ωScottContinuous_add_right a := by
    simp
    refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
    simp [ωSup, iSup_sup]
    intro x y h; simp_all only [sup_le_iff, le_sup_right, le_sup_of_le_left, and_self]
  ωScottContinuous_mul_left a := by
    simp
    refine ωScottContinuous_iff_monotone_map_ωSup.mpr ?_
    simp [ωSup]
    constructor
    · intro x y h; simp_all; exact add_le_add_right (α:=WithBot ℕ∞) h a.unarc
    · intro c
      sorry
      -- apply le_antisymm
      -- · simp

      -- · simp
      --   intro i
      --   simp [arc_le]
      --   apply add_le_add (a:=a.unarc) (by rfl)
      --   rw [← arc_le]
      --   simp
      --   rw [arc_iSup (f:=fun i ↦ (c i).unarc)]
      --   -- have := iSup_le (f:=fun i ↦ (c i).unarc) (a:=(c i).unarc) (by intro; simp; rfl)
      --   simp at this

      --   apply le_iSup_of_le i
      --   apply ciSup_le
      --   intro x
      --   apply add_le_add (a:=a.unarc)
      --   · rfl
      --   · simp [unarc]
      --     refine le_ciSup (by simp) x
  ωScottContinuous_mul_right := sorry

@[simp]
instance : WeightedNetKAT.Star Arctic where
  star x := if x ≤ arc 0 then arc 0 else arc ⊤

@[simp]
theorem le_zero_arc {x : Arctic} : x ≤ arc 0 ↔ x = arc ⊥ ∨ x = arc 0 := by
  simp
  constructor
  · intro h
    rcases x with _ | _ | x
    · left; rfl
    · contrapose! h
      sorry
      -- exact compareOfLessAndEq_eq_lt.mp rfl
    · suffices x = 0 by subst_eqs; right; rfl
      contrapose! h
      simp_all
      induction x with
      | zero => simp at h
      | succ x ih =>
        simp_all
        sorry
        -- exact compare_gt_iff_gt.mp rfl
  · rintro (⟨_, _⟩ | ⟨_, _⟩)
    · simp
    · rfl

noncomputable instance : CompleteLinearOrder Arctic where
  himp x y := arc (himp (unarc x) (unarc y))
  compl x := arc (compl (unarc x))
  sdiff x y := arc (sdiff (unarc x) (unarc y))
  hnot x := arc (hnot (unarc x))
  le_himp_iff a b c := by
    have := le_himp_iff (a:=unarc a) (b:=unarc b) (c:=unarc c)
    simp only at this
    nth_rw 1 [← arc_le] at this
    nth_rw 1 [← arc_le] at this
    rw [arc_inf] at this
    convert this
  himp_bot a := by congr; apply himp_bot
  sdiff_le_iff a b c := by
    have := sdiff_le_iff (a:=unarc a) (b:=unarc b) (c:=unarc c)
    simp only at this
    nth_rw 1 [← arc_le] at this
    nth_rw 1 [← arc_le] at this
    rw [arc_sup] at this
    convert this
  top_sdiff a := by congr; apply CompleteLinearOrder.top_sdiff
  le_total a b := le_total a.unarc b.unarc
  toDecidableLE := Classical.decRel LE.le

@[simp]
theorem finset_sum_eq_iSup {ι : Type*} [DecidableEq ι] {S : Finset ι} (f : ι → Arctic) :
    ∑ i ∈ S, f i = ⨆ i ∈ S, f i := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S hx ih =>
    simp_all; clear ih
    exact iSup_insert.symm

@[simp]
theorem pow_eq_mul {n : ℕ} {a : Arctic} : a^n = arc (n * unarc a) := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [pow_succ, right_distrib]

theorem add_top {x : WithBot ℕ∞} (hx : x ≠ ⊥) : ⊤ + x = ⊤ := top_unique (WithBot.le_self_add hx ⊤)
theorem top_add {x : WithBot ℕ∞} (hx : x ≠ ⊥) : x + ⊤ = ⊤ := top_unique (WithBot.le_add_self hx ⊤)

theorem help_me {a b : Arctic}
    (ha₁ : a ≠ ⊥) (ha₂ : a ≠ ⊤)
    (hb₁ : b ≠ ⊥) (hb₂ : b ≠ ⊤)
    (h :  ((unarc a).get (Option.isSome_iff_ne_none.mpr ha₁)).get (by
            rcases a with _ | _ | a <;> (try contradiction); rfl)
        < ((unarc b).get (Option.isSome_iff_ne_none.mpr hb₁)).get (by
            rcases b with _ | _ | b <;> (try contradiction); rfl)) :
    a < b := by
  rcases a with _ | _ | a <;> try contradiction
  rcases b with _ | _ | b <;> try contradiction
  simp_all
  replace h : a < b := by contrapose! h; exact h
  have h' := h.le
  simp_all
  constructor
  · apply unarc_le.mpr
    simp [WithBot.le_def]
    right
    use a, b
    split_ands
    · gcongr
    · rfl
    · rfl
  · rw [lt_iff_le_not_ge]
    constructor
    · apply unarc_le.mpr
      simp [WithBot.le_def]
      right
      use a, b
      split_ands
      · gcongr
      · rfl
      · rfl
    · contrapose h
      simp_all
      sorry

@[simp] theorem unarc_get {x} (h : Option.isSome x.unarc = true) : Option.get (unarc x) h = x.get h := rfl

instance : MulLeftMono (WithBot ℕ∞) where
  elim a b c h := by
    simp_all
    rw [mul_comm]
    have h₁ : ∀ {x : ℕ∞}, x ≠ 0 → @HMul.hMul ℕ∞ ℕ∞ ℕ∞ _ (none : ℕ∞) x = ⊤ := by intro x; apply ENat.top_mul
    have h₂ : @HMul.hMul ℕ∞ ℕ∞ ℕ∞ _ (none : ℕ∞) (none : ℕ∞) = ⊤ := by apply ENat.top_mul; exact Ne.symm (not_eq_of_beq_eq_false rfl)

    have h₃ : ∀ {x : ℕ∞}, x ≠ 0 → @HMul.hMul (WithBot ℕ∞) (WithBot ℕ∞) (WithBot ℕ∞) _ (none : (WithBot ℕ∞)) (some x) = ⊥ := by
      simp
      intro x h
      apply WithBot.bot_mul
      simp
      contrapose! h
      exact WithTop.coe_eq_zero.mp h
    have h₄ : ∀ {x : ℕ∞}, x ≠ 0 → @HMul.hMul (WithBot ℕ∞) (WithBot ℕ∞) (WithBot ℕ∞) _ (some x) (none : (WithBot ℕ∞)) = ⊥ := by
      simp
      intro x h
      apply WithBot.mul_bot
      simp
      contrapose! h
      exact WithTop.coe_eq_zero.mp h
    have h₅ : @HMul.hMul (WithBot ℕ∞) (WithBot ℕ∞) (WithBot ℕ∞) _ (none : WithBot ℕ∞) (none : WithBot ℕ∞) = ⊥ := by rfl
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c
    · simp_all
    · simp_all
    · simp_all
      sorry
    · simp_all
      sorry
    · simp_all
      rw [mul_comm]
    · simp_all
      rw [mul_comm]
      sorry
    · simp_all
      rw [mul_comm]
      sorry
    · simp_all
      sorry

instance : WeightedNetKAT.LawfulStar Arctic where
  star_eq_sum x := by
    sorry
    -- simp; split_ifs with h
    -- · simp [ωSum_nat_eq_ωSup, ωSup]
    --   rcases h with (⟨_, _⟩ | ⟨_, _⟩)
    --   · simp
    --     apply le_antisymm
    --     · simp
    --       apply le_iSup₂_of_le 1 0
    --       simp
    --     · simp
    --       intro i j h
    --       rcases j with _ | j
    --       · simp
    --       · simp [right_distrib]
    --   · simp
    --     apply le_antisymm
    --     · simp
    --       apply le_iSup₂_of_le 1 0
    --       simp
    --     · simp
    -- · apply le_antisymm
    --   · simp_all
    --     simp [ωSum_nat_eq_ωSup, ωSup]
    --     apply (iSup_eq_top _).mpr
    --     intro b hb
    --     simp [lt_iSup_iff]
    --     rcases b with _ | _ | b
    --     · use 1, 0; simp; apply bot_lt_iff_ne_bot.mpr; exact not_eq_of_beq_eq_false rfl
    --     · absurd hb; simp; rfl
    --     · use b + 2, b + 1
    --       simp [right_distrib]
    --       have l₁ : ∀ (a b c : WithBot ℕ∞), a < b → 0 ≤ c → a < b + c := by
    --         simp
    --         intro a b c hab hc
    --         exact lt_add_of_lt_of_nonneg hab hc
    --       have l₂ : ∀ {a b c : Arctic}, a < b → 0 ≤ c.unarc → a < b.unarc + c.unarc := by
    --         intro a b c
    --         simp
    --         intro h₁ h₂ h₃
    --         have h₃ := l₁ a.unarc b.unarc c.unarc (unarc_lt.mpr h₂) h₃
    --         constructor
    --         · exact h₃.le
    --         · exact unarc_lt.mp h₃
    --       apply l₂ <;> clear l₁ l₂
    --       · simp_all
    --         set b' : WithBot ℕ∞ := some (some b)
    --         have : @Nat.cast (WithBot ℕ∞) WithBot.addMonoidWithOne.toNatCast b = b' := by rfl
    --         simp [this]
    --         have : ∀ {a b : WithBot ℕ∞}, unarc (a * b) = unarc a * unarc b := by simp [unarc]
    --         simp [this]
    --         constructor
    --         · nth_rw 1 [← mul_one (a:=unarc b')]
    --           apply mul_le_mul' (α:=WithBot ℕ∞)
    --           · sorry
    --           · sorry
    --         · sorry
    --       ·
    --         sorry
    --       -- if x = ⊤ then
    --       --   subst_eqs
    --       --   simp
    --       --   rw [top_add]
    --       --   · exact hb
    --       --   · simp
    --       --     exact not_eq_of_beq_eq_false rfl
    --       -- else
    --       --   have : x.unarc ≠ ⊤ := by expose_names; exact h_1
    --       --   simp_all
    --       --   apply help_me
    --       --   · simp
    --       --   · simp_all
    --       --   · simp_all
    --       --   · simp_all
    --       --   · simp_all
    --       --     sorry
    --   · apply le_top

instance : Repr Arctic where
  reprPrec a _ :=
    match a with
    | none => "-∞"
    | some none => "∞"
    | some (some b) => reprStr b

end Arctic
