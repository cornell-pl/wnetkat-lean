import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.OmegaCompletePartialOrder

open OmegaCompletePartialOrder

@[simp]
theorem Chain.mk_apply {β : Type*} [Preorder β] (f : ℕ → β) (hf : Monotone f) (a : ℕ) :
    Chain.instFunLikeNat.coe (⟨f, hf⟩ : Chain β) a = f a := rfl

@[simp]
theorem OmegaCompletePartialOrder.ωSup_const {α : Type*} [OmegaCompletePartialOrder α] (x : α) :
    ωSup ⟨fun _ ↦ x, by intro; simp⟩ = x := by
  apply le_antisymm
  · apply ωSup_le _ _ fun i ↦ ?_; rfl
  · apply le_ωSup_of_le 0; rfl

theorem OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup {α : Type*} [OmegaCompletePartialOrder α] (f : ℕ →o ℕ →o α) :
      ωSup ⟨fun i ↦ ωSup ⟨fun j ↦ f i j, (f i).mono⟩, fun _ _ hij ↦ ωSup_le _ _ fun k ↦ le_ωSup_of_le k (f.mono hij k)⟩
    = ωSup ⟨fun i ↦ f i i, fun i j hij ↦ le_trans (f.mono hij i) ((f j).mono hij)⟩ := by
  apply le_antisymm
  · simp only [ωSup_le_iff, Chain.mk_apply]
    intro i j
    apply le_ωSup_of_le (i ⊔ j)
    simp only [Chain.mk_apply]
    have hi : i ≤ i ⊔ j := by omega
    have hj : j ≤ i ⊔ j := by omega
    exact OrderHom.apply_mono (f.mono hi) hj
  · simp only [ωSup_le_iff]
    intro i
    apply le_ωSup_of_le i
    apply le_ωSup_of_le i
    rfl

theorem OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup' {α : Type*} [OmegaCompletePartialOrder α] (f : ℕ → ℕ → α) (hf : Monotone f) (hf' : ∀ i, Monotone (f i)) :
      ωSup ⟨fun i ↦ ωSup ⟨fun j ↦ f i j, hf' i⟩, fun _ _ hij ↦ ωSup_le _ _ fun k ↦ le_ωSup_of_le k (hf hij k)⟩
    = ωSup ⟨fun i ↦ f i i, fun i j hij ↦ le_trans (hf hij i) (hf' j hij)⟩ :=
  OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup ⟨fun i ↦ ⟨fun j ↦ f i j, hf' i⟩, hf⟩

-- theorem Finset.sum_le_sum_of_inj {α β 𝒮 : Type*} [NonUnitalSemiring 𝒮] [PartialOrder 𝒮] [IsOrderedAddMonoid 𝒮]
--     {f : α → 𝒮} {g : β → 𝒮} (e : (a : α) → f a ≠ 0 → β) (he : ∀ Function.Injective e)
--     (h₀ : ∀ (x : β), 0 ≤ g x)
--     {A : Finset α} {B : Finset β}
--     (he' : ∀ a ∈ A, (h : f a ≠ 0) → e a h ∈ B)
--     (he' : ∀ a ∈ A, (h : f a ≠ 0) → f a = g (e a h))
--     :
--     ∑ a ∈ A, f a ≤ ∑ b ∈ B, g b := by
--   rw [Finset.sum_bij_ne_zero (s:=A) (t:=A.map ⟨e, he⟩) (g:=fun b ↦ g b) (fun x _ _ ↦ e x)]
--   · apply Finset.sum_mono_set_of_nonneg h₀
--     intro
--     simp_all
--     grind
--   · simp_all
--   · simp_all
--     intro a₁ h₁ h₁' a₂ h₂ h₂' h
--     exact he h
--   · simp_all
--     intro a ha ha'
--     use a
--   · simp_all

class IsPositiveOrderedAddMonoid (𝒮 : Type*) [AddCommMonoid 𝒮] [PartialOrder 𝒮] [OrderBot 𝒮]
    extends IsOrderedAddMonoid 𝒮 where
  protected bot_eq_zero : (⊥ : 𝒮) = 0

@[simp]
theorem nonpos_iff_eq_zero' {α : Type*} [AddCommMonoid α] [PartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] {a : α} :
    a ≤ 0 ↔ a = 0 := by
  rw [← IsPositiveOrderedAddMonoid.bot_eq_zero]
  simp

@[simp] lemma zero_le'' {α : Type*} [AddCommMonoid α] [PartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] (a : α) :
    0 ≤ a := by
  rw [← IsPositiveOrderedAddMonoid.bot_eq_zero]
  simp

instance (𝒮 : Type*) [AddCommMonoid 𝒮] [PartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] : Subsingleton (AddUnits 𝒮) where
  allEq := by
    intro ⟨a, a', ha₂, ha₃⟩ ⟨b, b', hb₂, hb₃⟩
    simp_all
    have := add_left_mono (α:=𝒮) (a:=a) (by simp : 0 ≤ a')
    simp [ha₃] at this
    have := add_left_mono (α:=𝒮) (a:=b) (by simp : 0 ≤ b')
    simp [hb₃] at this
    subst_eqs
    simp_all

class OmegaContinuousNonUnitalSemiring (𝒮 : Type*)
    [NonUnitalSemiring 𝒮]
    [OmegaCompletePartialOrder 𝒮]
    [OrderBot 𝒮]
    [MulLeftMono 𝒮]
    [MulRightMono 𝒮]
    [IsPositiveOrderedAddMonoid 𝒮] where
  ωScottContinuous_add_right : ∀ x : 𝒮, ωScottContinuous (· + x)
  ωScottContinuous_add_left : ∀ x : 𝒮, ωScottContinuous (x + ·)
  ωScottContinuous_mul_right : ∀ x : 𝒮, ωScottContinuous (· * x)
  ωScottContinuous_mul_left : ∀ x : 𝒮, ωScottContinuous (x * ·)

section

variable {𝒮 : Type*}
  [NonUnitalSemiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]
  [OmegaContinuousNonUnitalSemiring 𝒮]

open OmegaContinuousNonUnitalSemiring

theorem ωSup_add {f : Chain 𝒮} (a : 𝒮) :
    ωSup f + a = ωSup ⟨fun i ↦ f i + a, fun i j hij ↦ add_le_add (f.mono hij) (by rfl)⟩ :=
  ωScottContinuous_add_right _ |>.map_ωSup _
theorem add_ωSup {f : Chain 𝒮} (a : 𝒮) :
    a + ωSup f = ωSup ⟨fun i ↦ a + f i, fun i j hij ↦ add_le_add (by rfl) (f.mono hij)⟩ :=
  ωScottContinuous_add_left _ |>.map_ωSup _
theorem ωSup_mul {f : Chain 𝒮} (a : 𝒮) :
    ωSup f * a = ωSup ⟨fun i ↦ f i * a, fun i j hij ↦ mul_le_mul' (f.mono hij) (by rfl)⟩ :=
  ωScottContinuous_mul_right _ |>.map_ωSup _
theorem mul_ωSup {f : Chain 𝒮} (a : 𝒮) :
    a * ωSup f = ωSup ⟨fun i ↦ a * f i, fun i j hij ↦ mul_le_mul' (by rfl) (f.mono hij)⟩ :=
  ωScottContinuous_mul_left _ |>.map_ωSup _

theorem ωSup_add_ωSup {f g : Chain 𝒮} :
    ωSup f + ωSup g = ωSup ⟨fun i ↦ f i + g i, fun i j hij ↦ by simp only; gcongr⟩ := by
  simp only [add_ωSup, ωSup_add]
  rw [ωSup_ωSup_eq_ωSup']
  intro _ _ _ _; simp only; gcongr
theorem ωSup_mul_ωSup {f g : Chain 𝒮} :
    ωSup f * ωSup g = ωSup ⟨fun i ↦ f i * g i, fun i j hij ↦ by simp only; gcongr⟩ := by
  simp only [mul_ωSup, ωSup_mul]
  rw [ωSup_ωSup_eq_ωSup']
  intro _ _ _ _; simp only; gcongr

end

-- TODO: this might be interesting to try at some point
-- instance
--     {𝒮 : Type*}
--     [NonUnitalSemiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮]
--     [IsPositiveOrderedAddMonoid 𝒮] : ExistsAddOfLE 𝒮 where
--   exists_add_of_le := sorry

section ωSum

variable {𝒮 : Type*}
  [AddCommMonoid 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]

variable {X : Type*} [Countable X]

instance : IsPositiveOrderedAddMonoid (X → 𝒮) where
  bot_eq_zero := by ext; simp [IsPositiveOrderedAddMonoid.bot_eq_zero]

@[simp]
theorem ωSup_eq_zero_iff (C : Chain 𝒮) : ωSup C = 0 ↔ ∀ i, C i = 0 := by
  constructor
  · intro h i
    exact (nonpos_iff_eq_zero' (α :=𝒮)).mp (ωSup_le_iff.mp (le_antisymm_iff.mp h).left i)
  · intro h
    exact le_antisymm (ωSup_le C 0 (by simp [h])) (zero_le'' (ωSup C))

/-- Sum over countable `X` -/
noncomputable def ωSum (f : X → 𝒮) : 𝒮 :=
  letI e : Encodable X := Encodable.ofCountable X
  ωSup ⟨fun n ↦ ∑ i ∈ Finset.range n, if let some x := e.decode₂ _ i then f x else 0,
    by
      intro n₁ n₂ h
      simp
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp [h])
      simp only [Finset.mem_range, not_lt]
      intro i hi₂ hi₁
      simp⟩

@[inherit_doc ωSum]
notation3 "ω∑ "(...)", "r:67:(scoped f => ωSum f) => r

@[simp, grind]
theorem ωSum_zero : ω∑ (_ : X), (0 : 𝒮) = 0 := by
  simp [ωSum]; grind

@[simp]
theorem ωSum_eq_zero_iff {f : X → 𝒮} : ω∑ (i : X), f i = 0 ↔ ∀ (x : X), f x = 0 := by
  letI e : Encodable X := Encodable.ofCountable X
  constructor
  · simp [ωSum]
    intro h x
    specialize h (Encodable.encode x + 1) (Encodable.encode x)
    simp_all
  · simp +contextual

@[gcongr]
theorem ωSum_mono {f g : X → 𝒮} (h : f ≤ g) : ω∑ n, f n ≤ ω∑ n, g n := by
  simp only [ωSum]
  refine ωSup_le_ωSup_of_le ?_
  intro i
  use i
  simp only [Chain.mk_apply]
  refine Finset.sum_le_sum ?_
  intro j hj
  split
  · apply h
  · rfl

theorem ωSum_le_of_finset
    {f : X → 𝒮} {a : 𝒮} (h : ∀ S : Finset X, ∑ x ∈ S, f x ≤ a) :
    ω∑ x : X, f x ≤ a := by
  letI e : Encodable X := Encodable.ofCountable X
  apply ωSup_le _ _ fun i ↦ ?_
  simp only [Chain.mk_apply]
  apply le_trans _ (h <| (Finset.range i).filterMap e.decode₂ (by simp_all [e.decode₂_eq_some]))
  apply le_of_eq
  symm
  apply Finset.sum_bij_ne_zero (fun x _ _ ↦ e.encode x)
  · simp +contextual [e.decode₂_eq_some]
  · simp
  · intro b hb
    split
    · simp_all [Encodable.decode₂_eq_some]; grind
    · simp
  · simp

theorem le_ωSum_of_finset
    {f : X → 𝒮} (S: Finset X) :
    ∑ x ∈ S, f x ≤ ω∑ x : X, f x := by
  letI e : Encodable X := Encodable.ofCountable X
  apply le_ωSup_of_le (S.sup e.encode + 1)
  simp only [Chain.mk_apply]
  rw [Finset.sum_bij_ne_zero (s:=S) (t:=S.map ⟨e.encode, e.encode_injective⟩) (fun x _ _ ↦ e.encode x) (g:=fun x ↦ match Encodable.decode₂ X x with
    | some x => f x
    | x => 0)]
  · apply Finset.sum_mono_set_of_nonneg
    · simp
    · intro i; simp
      rintro x hxs ⟨_⟩
      refine Nat.lt_add_one_of_le ?_
      exact Finset.le_sup hxs
  all_goals simp +contextual

theorem ωSum_finset {I : Type*} [DecidableEq I] [Countable I] (S : Finset I) (f : I → 𝒮) :
    ω∑ x : S, f x = ∑ x ∈ S, f x := by
  apply le_antisymm
  · apply ωSum_le_of_finset fun S₀ ↦ ?_
    rw [Finset.sum_bij (s:=S₀) (t:=S₀.map ⟨(·.val), ?_⟩) (fun x _ ↦ x) (g:=(f ·))]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro; simp; grind
      · simp
    all_goals simp
  · apply le_trans _ (le_ωSum_of_finset S.attach)
    rw [Finset.sum_attach]

theorem ωSum_fintype {I : Type*} [DecidableEq I] [Countable I] [Fintype I] (f : I → 𝒮) :
    ω∑ x, f x = ∑ x, f x :=
  le_antisymm
    (ωSum_le_of_finset fun _ ↦ Finset.sum_le_univ_sum_of_nonneg fun x ↦ zero_le'' (f x))
    (le_ωSum_of_finset Finset.univ)

omit [AddCommMonoid 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Countable X] in
@[simp]
theorem asdsad {c : Chain (X → 𝒮)} {x} : ωSup c x = ωSup (c.map ⟨(· x), fun ⦃_ _⦄ a ↦ a x⟩) := by
  rfl

@[simp]
theorem ωSum_apply {Y : Type*} {f : X → Y → 𝒮} {y : Y} :
    (ω∑ (x : X), f x) y = ω∑ (x : X), f x y := by
  simp [ωSum, Chain.map]
  congr with n
  simp
  congr with x
  split <;> simp_all

attribute [local simp] Encodable.decode₂_eq_some in
theorem ωSum_nat_eq_ωSup
    {f : ℕ → 𝒮} : ω∑ (x : ℕ), f x = ωSup ⟨fun n ↦ ∑ x ∈ Finset.range n, f x, fun i j h ↦ by apply Finset.sum_mono_set_of_nonneg <;> simp [h]⟩ := by
  let e₀ : Encodable ℕ := Encodable.ofCountable ℕ
  let e₁ : Encodable ℕ := Nat.encodable
  apply le_antisymm
  · apply ωSup_le _ _ fun i ↦ ?_
    simp only [Chain.mk_apply]
    let t := (Finset.range i).filterMap e₀.decode₂ (by intro; simp_all)
    rw [Finset.sum_bij_ne_zero (s:=Finset.range i) (t:=t) (g:=f) (fun x _ h ↦ (e₀.decode₂ _ x).get (by split at h <;> simp_all; subst_eqs; simp))]
    · apply le_ωSup_of_le (t.sup id + 1)
      simp only [Chain.mk_apply]
      apply Finset.sum_mono_set_of_nonneg
      · simp
      · intro a ha
        rcases a with _ | a
        · simp
        · simp_all [t]
          grind
    · simp_all [t]
      intro a hai
      grind
    · clear t
      simp
      intro a hai ha b hbi hb h'
      by_cases hq : ∃ q, e₀.decode₂ ℕ a = some q
      · obtain ⟨q, hq⟩ := hq
        simp [hq] at ha
        simp_all
        subst_eqs
        simp_all
        by_cases hq : ∃ q', e₀.decode₂ ℕ b = some q'
        · obtain ⟨q, hq⟩ := hq
          simp [hq] at ha
          simp_all
        · split at hb
          · simp_all
          · grind
      · split at hb
        · simp_all
          split at ha
          · simp_all
          · grind
        · simp_all
    · simp_all [t]
      intro b hb h'
      use e₀.encode b
      simp [*]
    · simp_all
      intro a hai h
      by_cases hq : ∃ q', e₀.decode₂ ℕ a = some q'
      · obtain ⟨q, hq⟩ := hq
        simp [hq] at h
        simp_all
        subst_eqs
        simp
      · simp_all
        simp_all [Encodable.decode₂]
        grind
  · simp [le_ωSum_of_finset]

attribute [local simp] Encodable.decode₂_eq_some in
theorem ωSum_nat_eq_ωSup_succ
    {f : ℕ → 𝒮} : ω∑ (x : ℕ), f x = ωSup ⟨fun n ↦ ∑ x ∈ Finset.range (n + 1), f x, fun i j h ↦ by apply Finset.sum_mono_set_of_nonneg <;> simp [h]⟩ := by
  rw [ωSum_nat_eq_ωSup]
  apply le_antisymm
  · simp
    rintro (_ | i)
    · simp
    · apply le_ωSup_of_le i; simp
  · simp; intro i; apply le_ωSup_of_le (i + 1); simp

end ωSum

section ωSum

variable {𝒮 : Type*}
  [NonUnitalSemiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [OmegaContinuousNonUnitalSemiring 𝒮]

variable {X : Type*} [Countable X]

omit [Countable X] in
theorem Finset.sum_ωScottContinuous [DecidableEq X] (S : Finset X) :
    ωScottContinuous (fun (f : X → 𝒮) ↦ ∑ i ∈ S, f i) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun a b hab ↦ sum_le_sum fun i a ↦ hab i, ?_⟩
  intro c
  induction S using Finset.induction with
  | empty => simp; symm; simp
  | insert x S hx ih =>
    simp_all; clear ih
    rw [ωSup_add_ωSup]
    congr

theorem ωSum_ωSup (C : Chain (X → 𝒮)) :
    ω∑ n, ωSup C n = ωSup ⟨fun x ↦ ω∑ n, C x n, fun _ _ h ↦ ωSum_mono (C.mono h)⟩ := by
  letI e : Encodable X := Encodable.ofCountable X
  simp only [ωSum]
  apply le_antisymm
  · refine ωSup_le_iff.mpr fun i ↦ ?_
    simp
    have :
      (∑ x ∈ Finset.range i,
        match Encodable.decode₂ X x with
        | some x => ωSup (C.map ⟨(· x), fun ⦃_ _⦄ a ↦ a x⟩)
        | x => 0) ≤
      (∑ x ∈ Finset.range i,
        ωSup (C.map ⟨(fun f ↦ match Encodable.decode₂ X x with
        | some x => f x
        | x => 0), fun ⦃_ _⦄ a ↦ by split <;> simp [a _]⟩)) := by
      gcongr with j hji
      by_cases hq : ∃ q : X, Encodable.decode₂ _ j = some q
      · obtain ⟨q, hq⟩ := hq
        simp_all
      · simp_all
    apply le_trans this; clear this
    have :
      (∑ x ∈ Finset.range i,
        ωSup
          (C.map
            ⟨fun f ↦
                match Encodable.decode₂ X x with
                | some x => f x
                | x => 0, by intro a b h; split <;> simp [h _]⟩)) ≤
      ωSup (C.map ⟨fun f ↦ (∑ x ∈ Finset.range i,
                match Encodable.decode₂ X x with
                | some x => f x
                | x => 0), by intro a b h; simp; gcongr; split <;> simp [h _]⟩) := by
      induction i with
      | zero => simp
      | succ i ih =>
        simp [Finset.sum_range_add]
        have :
          (ωSup (C.map ⟨fun f ↦
            (∑ x ∈ Finset.range i,
                match Encodable.decode₂ X x with
                | some x => f x
                | x => 0), fun a b h ↦ by simp; gcongr; split <;> simp [h _]⟩) +
          (ωSup (C.map ⟨fun f ↦
                match Encodable.decode₂ X i with
                | some x => f x
                | x => 0, fun a b h ↦ by simp; split <;> simp [h _]⟩))) ≤
          (ωSup (C.map
            ⟨fun f ↦
                (∑ x ∈ Finset.range i,
                    match Encodable.decode₂ X x with
                    | some x => f x
                    | x => 0) +
                  match Encodable.decode₂ X i with
                  | some x => f x
                  | x => 0, fun a b h ↦ by simp; gcongr <;> split <;> simp [h _]⟩)) := by
          clear ih
          rw [ωSup_add_ωSup]
          apply ωSup_le_ωSup_of_le
          intro k; use k
          simp [Chain.map, OrderHom.comp]
        apply le_trans _ this; clear this
        gcongr
    apply le_trans this; clear this
    simp
    intro j
    apply le_ωSup_of_le j
    apply le_ωSup_of_le i
    rfl
  · refine ωSup_le _ _ fun i ↦ ωSup_le _ _ fun j ↦ ?_
    apply le_ωSup_of_le j
    simp
    gcongr
    split
    · apply le_ωSup_of_le i
      simp
    · rfl

theorem ωSum_ωSup' (C : X → Chain 𝒮) :
    ω∑ n, ωSup (C n) = ωSup ⟨fun x ↦ ω∑ n, C n x, fun _ _ h ↦ ωSum_mono fun n ↦ (C n).mono h⟩ :=
  ωSum_ωSup ⟨fun x i ↦ C i x, fun _ _ h i ↦ (C i).mono h⟩

omit [Countable X] in
theorem sum_ωSup [DecidableEq X] (S : Finset X) (C : Chain (X → 𝒮)) :
    ∑ n ∈ S, ωSup C n = ωSup ⟨fun x ↦ ∑ n ∈ S, C x n, fun _ _ h ↦ by simp only; gcongr; apply C.mono h⟩ := by
  induction S using Finset.induction with
  | empty => simp
  | insert n S hn ih =>
    simp_all; clear ih
    rw [ωSup_add_ωSup]
    congr

omit [Countable X] in
theorem sum_ωSup' [DecidableEq X] (S : Finset X) (C : X → Chain 𝒮) :
    ∑ n ∈ S, ωSup (C n) = ωSup ⟨fun x ↦ ∑ n ∈ S, C n x, fun _ _ h ↦ by simp only; gcongr⟩ :=
  sum_ωSup S ⟨fun x i ↦ C i x, fun _ _ h i ↦ (C i).mono h⟩

theorem ωSum_nat_eq_succ
    {f : ℕ → 𝒮} : ω∑ (x : ℕ), f x = f 0 + ω∑ (x : ℕ), f (x + 1) := by
  simp [ωSum_nat_eq_ωSup]
  rw [add_ωSup]
  apply le_antisymm
  · apply ωSup_le _ _ fun i ↦ ?_
    rcases i with _ | i
    · simp
    · apply le_ωSup_of_le i
      simp [Finset.sum_range_succ', add_comm]
  · apply ωSup_le _ _ fun i ↦ le_ωSup_of_le (i + 1) ?_
    simp [Finset.sum_range_succ', add_comm]

attribute [local simp] Encodable.decode₂_eq_some in
theorem ωSum_add {f g : X → 𝒮} :
    ω∑ (x : X), (f x + g x) = ω∑ (x : X), f x + ω∑ x, g x := by
  simp [ωSum]
  simp [ωSup_add_ωSup, ← Finset.sum_add_distrib]
  congr with n
  congr! with i hi
  split <;> simp

theorem ωSum_mul_left {f : X → 𝒮} {a : 𝒮} :
    ω∑ (x : X), a * f x = a * ω∑ (x : X), f x := by
  simp [ωSum, mul_ωSup, Finset.mul_sum]
  congr; congr!; split <;> simp

theorem ωSum_mul_right {f : X → 𝒮} {a : 𝒮} :
    ω∑ (x : X), f x * a = (ω∑ (x : X), f x) * a := by
  simp [ωSum, ωSup_mul, Finset.sum_mul]
  congr; congr!; split <;> simp

theorem ωSum_sum_comm {Y : Type*} (S : Finset Y) {f : X → Y → 𝒮} :
    ω∑ (x : X), ∑ y ∈ S, f x y = ∑ y ∈ S, ω∑ (x : X), f x y := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert y S hy ih =>
    simp_all [ωSum_add]

theorem ωSum_comm_le {Y : Type*} [Countable Y] {f : X → Y → 𝒮} :
    ω∑ (x : X) (y : Y), f x y ≤ ω∑ (y : Y) (x : X), f x y := by
  apply ωSum_le_of_finset fun S ↦ ?_
  simp [← ωSum_sum_comm]
  apply ωSum_mono fun n ↦ ?_
  exact le_ωSum_of_finset S

theorem ωSum_comm {Y : Type*} [DecidableEq Y] [Countable Y] {f : X → Y → 𝒮} :
    ω∑ (x : X) (y : Y), f x y = ω∑ (y : Y) (x : X), f x y := le_antisymm ωSum_comm_le ωSum_comm_le

open scoped Classical in
theorem Function.Injective.ωSum_eq {α ι γ : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [Countable ι] [Countable γ]
    {g : γ → ι} (hg : Injective g) {f : ι → α}
    (hf : f.support ⊆ Set.range g) : ω∑ c, f (g c) = ω∑ b, f b := by
  have : f.support = g '' (f ∘ g).support := by
    rw [support_comp_eq_preimage, Set.image_preimage_eq_of_subset hf]
  rw [← Function.comp_def]
  apply le_antisymm
  · apply ωSum_le_of_finset
    intro S
    let S' : Finset ι := S.map ⟨g, hg⟩
    apply le_trans _ (le_ωSum_of_finset S')
    apply le_of_eq
    apply Finset.sum_bij_ne_zero fun x _ _ ↦ g x
    · simp_all [S']
    · simp_all only [Set.image_subset_iff, Set.preimage_range, Set.subset_univ, comp_apply, ne_eq]
      intro a₁ ha₁ ha₁' a₂ ha₂ ha₂' h
      exact hg h
    · simp_all [S']
      intro a haS hfga
      use a
    · simp_all
  · apply ωSum_le_of_finset
    intro S
    let S' : Finset γ := S.preimage g (by intro _ _ _ _; apply hg)
    apply le_trans _ (le_ωSum_of_finset S')
    apply le_of_eq
    symm
    apply Finset.sum_bij_ne_zero fun x _ _ ↦ g x
    · simp_all [S']
    · simp_all [S']
      intro a₁ ha₁ ha₁' a₂ ha₂ ha₂' h
      exact hg h
    · simp_all [S']
      intro a haS hfga
      suffices ∃ x, g x = a by obtain ⟨x, ⟨_⟩⟩ := this; use x
      have hs : a ∈ f.support := hfga
      simp only [this, Set.mem_image] at hs
      obtain ⟨x, hx, hx'⟩ := hs
      use x
    · simp_all

theorem ωSum_subtype_eq_of_supp_subset {α ι : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [Countable ι]
    {f : ι → α} {s : Set ι} (hs : f.support ⊆ s) :
    ω∑ x : s, f x = ω∑ x, f x :=
  Subtype.val_injective.ωSum_eq <| by simpa

theorem ωSum_substype_supp {α ι : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [Countable ι]
    (f : ι → α) :
    ω∑ x : f.support, f x = ω∑ x, f x :=
  ωSum_subtype_eq_of_supp_subset Set.Subset.rfl

theorem ωSum_eq_ωSum_of_ne_one_bij {α ι γ : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [Countable ι] [Countable γ]
    {f : ι → α} {g : γ → α} (i : g.support → ι) (hi : Function.Injective i)
    (hf : f.support ⊆ Set.range i) (hfg : ∀ x, f (i x) = g x) : ω∑ x, f x = ω∑ y, g y := by
  rw [← ωSum_substype_supp g, ← hi.ωSum_eq hf]
  simp only [hfg]

theorem ωSum_eq_single {α ι : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [Countable ι]
    {f : ι → α}  (x : ι) (hf : ∀ (x' : ι), x' ≠ x → f x' = 0) : ω∑ x, f x = f x := by
  letI : Encodable ({x} : Set ι) := Encodable.ofCountable _
  rw [ωSum_eq_ωSum_of_ne_one_bij (f:=f) (γ:=({x} : Set ι)) (g:=(f ·)) (fun ⟨x, _⟩ ↦ x)]
  · rw [ωSum_fintype]
    simp only [Finset.univ_unique, Set.default_coe_singleton, Finset.sum_singleton]
  · rintro ⟨⟨x, _, _⟩, h₁⟩; grind
  · intro x'
    simp_all only [ne_eq, Function.mem_support, Set.mem_range, Subtype.exists, exists_prop,
      Set.mem_singleton_iff, existsAndEq, true_and]
    grind
  · simp

theorem ωSum_prod {α β γ : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [MulLeftMono α] [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
    [Countable β] [Countable γ]
    {f : β × γ → α} :
    ω∑ (p : β × γ), f p = ω∑ (b : β) (c : γ), f (b, c) := by
  classical
  apply le_antisymm
  · refine ωSum_le_of_finset fun S ↦ ?_
    apply le_trans _ (le_ωSum_of_finset  (S.image (·.fst)))
    suffices ∑ x ∈ S.image (·.fst), ∑ c ∈ S.image (·.snd), f (x, c) ≤ ∑ x ∈ S.image (·.fst), ω∑ (c : γ), f (x, c) by
      apply le_trans _ this; clear this
      rw [← Finset.sum_product]
      gcongr
      · simp
      · intro; simp; grind
    gcongr
    apply le_ωSum_of_finset (S.image (·.snd))
  · refine ωSum_le_of_finset fun S ↦ ?_
    rw [← ωSum_sum_comm]
    refine ωSum_le_of_finset fun S' ↦ ?_
    apply le_trans _ (le_ωSum_of_finset (S ×ˢ S'))
    rw [Finset.sum_comm, Finset.sum_product]

theorem ωSum_prod' {α β γ : Type*}
    [NonUnitalSemiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α]
    [MulLeftMono α] [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α]
    [Countable β] [Countable γ]
    {f : β → γ → α} :
    ω∑ (p : β × γ), f p.fst p.snd = ω∑ (b : β) (c : γ), f b c := ωSum_prod

-- theorem its_summable {X : Type*} [Countable X] [TopologicalSpace 𝒮] [OrderClosedTopology 𝒮] (f : X → 𝒮) : Summable f := by
--   exists ωSum f
--   simp [ωSum]
--   apply?
--   simp [HasSum]
--   sorry


-- theorem ωSum_eq_tsum {X : Type*} [Countable X] [TopologicalSpace 𝒮] [OrderClosedTopology 𝒮] (f : X → 𝒮) : ωSum f = ∑' x, f x := by
--   letI e : Encodable X := Encodable.ofCountable X
--   simp [ωSum]
--   apply le_antisymm
--   · simp
--     intro i
--     simp?
--     let S : Finset X := (Finset.range i).filterMap e.decode₂ (by simp [Encodable.decode₂_eq_some, eq_comm]; grind)
--     rw [← Finset.sum_bij_ne_zero (s:=S) (f:=f) (fun x _ _ ↦ e.encode x)]
--     · refine Summable.sum_le_tsum S ?_ ?_
--       · simp
--       · sorry
--     · simp [S, Encodable.decode₂_eq_some]
--       grind
--     · simp [S, Encodable.decode₂_eq_some]
--     · simp [S, Encodable.decode₂_eq_some]
--       intro j hji
--       split
--       · simp_all [Encodable.decode₂_eq_some]
--         grind
--       · grind
--     · simp
--   · refine tsum_le_of_sum_le' ?_ ?_; · simp
--     intro S
--     let S' := S.map ⟨e.encode, Encodable.encode_injective⟩
--     apply le_ωSup_of_le ((S'.sup id) + 1)
--     simp?
--     have : S ⊆ (Finset.range ((S'.sup id) + 1)).filterMap e.decode₂ (by simp [Encodable.decode₂_eq_some, eq_comm]; grind) := by
--       intro x hx
--       simp
--       use e.encode x
--       simp [S']
--       refine Order.lt_add_one_iff.mpr ?_
--       exact Finset.le_sup hx
--     · apply le_trans (Finset.sum_le_sum_of_subset this); clear this
--       apply le_of_eq
--       apply Finset.sum_bij_ne_zero (fun x _ _ ↦ e.encode x)
--       · simp [Encodable.decode₂_eq_some]
--         grind
--       · simp
--       · simp [Encodable.decode₂_eq_some, Order.lt_add_one_iff.mpr]
--         intro i hjS' h
--         grind [Encodable.decode₂_eq_some]
--       · simp

end ωSum
