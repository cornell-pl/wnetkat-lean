import Mathlib.Data.Set.Countable
import WeightedNetKAT.Domain

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

abbrev W (X : Type) (𝒮 : Type) := X → 𝒮

def W.supp {X : Type} (m : W X 𝒮) := {x : X | m x ≠ 𝟘}

omit [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem W.supp_mem_iff {X : Type} {x} (m : W X 𝒮) : x ∈ m.supp ↔ m x ≠ 𝟘 := by rfl

noncomputable def W.mass (m : W X 𝒮) [Encodable m.supp] := ⨁' x : m.supp, m x.val

def 𝒲 (𝒮 : Type) [WeightedSemiring 𝒮] (X : Type) := {m : W X 𝒮 // Countable m.supp}

omit [WeightedOmegaContinuousPreSemiring 𝒮] in
@[ext]
theorem 𝒲.ext (C₁ C₂ : 𝒲 𝒮 X)
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

def 𝒲.wNsmul (n : ℕ) (w : 𝒲 𝒮 X) : 𝒲 𝒮 X := match n with
  | 0 => 𝟘
  | n + 1 => wNsmul n w ⨁ w

instance WeightedPreSemiring.instCountablePi : WeightedPreSemiring (𝒲 𝒮 X) where
  wAdd_assoc _ _ _ := by ext x; apply wAdd_assoc
  wZero_add _ := by ext X; apply wZero_add
  add_wZero _ := by ext X; apply add_wZero
  wNsmul := 𝒲.wNsmul
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
  wSup C := ⟨fun i ↦ wSup (C.map (· i) (· i)), by
    simp
    let s : Set _ := ⋃ n : ℕ, (C n).supp
    have s_countable : Countable s := by
      simp only [Set.countable_coe_iff, Set.countable_iUnion_iff, s]
      exact fun n => (C n).prop
    apply Set.Countable.mono _ s_countable
    intro x mem
    simp only [Set.mem_iUnion, W.supp_mem_iff, ne_eq, s]
    simp only [W.supp_mem_iff, ne_eq, wSup_eq_zero_iff, not_forall, s] at mem
    obtain ⟨p, hp⟩ := mem
    exists p⟩
  le_wSup c i p := by
    simp
    apply WeightedPartialOrder.wle_trans _ (le_wSup _ i)
    magic_simp
  wSup_le c w h x := by
    simp
    apply wSup_le
    intro n
    simp only [WeightedChain.map, DFunLike.coe]
    simp
    specialize h n x
    exact h

open WeightedOmegaCompletePartialOrder in
instance WeightedOmegaContinuousPreSemiring.instCountablePi :
    WeightedOmegaContinuousPreSemiring (𝒲 𝒮 X) where
  wle_positive _ _ := by simp
  wAdd_mono _ _ _ _ _ := by apply wAdd_mono; apply_assumption
  wMul_mono_left _ _ _ _ _ := by apply wMul_mono_left; apply_assumption
  wMul_mono_right  _ _ _ _ _ := by apply wMul_mono_right; apply_assumption
  wAdd_wSup _ _ := by ext x; apply wAdd_wSup
  wSup_wAdd _ _ := by ext x; apply wSup_wAdd
  wMul_wSup _ _ := by ext x; apply wMul_wSup
  wSup_wMul _ _ := by ext x; apply wSup_wMul

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
theorem wMul_eq_zero_of {α : Type} [WeightedPreSemiring α] {a b : α} :
    a = 𝟘 ∨ b = 𝟘 → a ⨀ b = 𝟘 := by rintro (h | h) <;> subst_eqs <;> simp
@[simp]
theorem nonzero_wMul_nonzero {α : Type} [WeightedPreSemiring α] {a b : α} :
    ¬a ⨀ b = 𝟘 → ¬a = 𝟘 ∧ ¬b = 𝟘 := by
  contrapose
  exact fun h ↦ not_ne_iff.mpr (wMul_eq_zero_of (or_iff_not_and_not.mpr h))

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
    contrapose! h₂
    replace h₂ : f x y = 𝟘 := h₂
    simp [h₂]⟩

infixr:50 " ≫= " => 𝒲.bind

instance {Y : Type} [Countable X] {m : 𝒲 𝒮 X} (f : X → 𝒲 𝒮 Y) :
    Countable (m ≫= f).val.supp := (m ≫= f).prop
