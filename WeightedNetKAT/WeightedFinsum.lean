import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import WeightedNetKAT.Domain
import Mathlib.Data.Finset.Preimage

section

variable {X : Type} {𝒮 : Type} [WeightedPreSemiring 𝒮]

abbrev W (X : Type) (𝒮 : Type) := X → 𝒮

def W.supp {X : Type} (m : W X 𝒮) := {x : X | m x ≠ 𝟘}

@[simp] theorem W.supp_mem_iff {X : Type} {x} (m : W X 𝒮) : x ∈ m.supp ↔ m x ≠ 𝟘 := by rfl

end

variable {X : Type} {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

section

variable {α : Type}

variable [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]

open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring

omit [WeightedOmegaContinuousPreSemiring 𝒮] [WeightedSemiring 𝒮] in
@[simp]
theorem wSup_apply {ι : Type} (C : WeightedChain (ι → 𝒮)) (a : ι) :
    wSup C a = wSup (C.map (· a) (· a)) := by
  simp [wSup]
  rfl

theorem WeightedFinsum_mono {α : Type} [WeightedPartialOrder α] [WeightedPreSemiring α] [WeightedMonotonePreSemiring α] [DecidableEq X] (S : Finset X) : WeightedMonotone (fun (f : X → α) ↦ ⨁ᶠ i ∈ S, f i) := by
  intro f g hfg
  simp only
  induction S using Finset.induction with
  | empty => simp
  | insert x S hxS ih =>
    simp_all [WeightedFinsum_insert]
    gcongr
    exact hfg x
open WeightedOmegaCompletePartialOrder in
theorem WeightedSum_mono [Encodable X] : WeightedMonotone (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) := by
  intro f₁ f₂ h₁₂
  apply wSup_le fun i ↦ ?_
  apply le_wSup_of_le i
  magic_simp [WeightedSum_chain]
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [WeightedFinsum_range_succ]
    gcongr
    split
    · apply h₁₂
    · simp

open WeightedPartialOrder WeightedOmegaCompletePartialOrder in
theorem WeightedFinsum_cont [DecidableEq X] (S : Finset X) :
    WeightedOmegaContinuous (fun (f : X → α) ↦ ⨁ᶠ i ∈ S, f i) (WeightedFinsum_mono S) := by
  intro C
  simp only [wSup_apply]
  induction S using Finset.induction with
  | empty =>
    simp
    simp [WeightedChain.map]
    apply wle_antisymm <;> simp
    intro; magic_simp
  | insert x S hxS ih =>
    simp_all
    simp [WeightedOmegaContinuousAddLeft, WeightedOmegaContinuousAddRight, WeightedChain.map]
    magic_simp
    simp only [WeightedChain.val_apply]
    apply wle_antisymm
    · refine wSup_le fun i ↦ ?_
      simp [WeightedOmegaCompletePartialOrder.instPi]
      magic_simp
      simp [WeightedOmegaContinuousAddLeft, WeightedOmegaContinuousAddRight, WeightedChain.map]
      apply wSup_le fun j ↦ ?_
      apply le_wSup_of_le (i ⊔ j)
      magic_simp
      simp only [WeightedChain.val_apply]
      gcongr
      · apply C.prop; simp
      · apply WeightedFinsum_mono; apply C.prop; simp
    · apply wSup_le fun i ↦ ?_
      magic_simp
      simp only [WeightedChain.val_apply]
      apply le_wSup_of_le i
      simp [WeightedOmegaCompletePartialOrder.instPi]
      magic_simp
      simp [WeightedOmegaContinuousAddLeft, WeightedOmegaContinuousAddRight, WeightedChain.map]
      apply le_wSup_of_le i
      magic_simp

open WeightedPartialOrder WeightedOmegaCompletePartialOrder in
theorem WeightedSum_cont [Encodable X] :
    WeightedOmegaContinuous (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) WeightedSum_mono := by
  intro C
  apply wle_antisymm
  · simp [WeightedSum, WeightedSum_chain]
    apply wSup_le fun i ↦ ?_
    have :
        (⨁ᶠ i ∈ Finset.range i,
          match Encodable.decode₂ _ i with | some x => wSup (C.map (· x) (· x)) | x => 𝟘)
      ≼ (⨁ᶠ i ∈ Finset.range i,
          wSup (C.map (fun f ↦ match Encodable.decode₂ _ i with | some x => f x | x => 𝟘)
                      (fun hfg ↦ by simp only; split <;> simp_all [hfg _]))) := by
      apply WeightedFinsum_mono _ fun j ↦ ?_
      by_cases hq : ∃ q : X, Encodable.decode₂ _ j = some q
      · obtain ⟨q, hq⟩ := hq; simp_all
      · simp_all
    apply wle_trans this; clear this
    have := WeightedFinsum_cont (Finset.range i) (C.map (fun f i ↦ match Encodable.decode₂ _ i with | some x => f x | x => 𝟘) ?_)
    · simp [WeightedChain.map] at this ⊢
      simp only [DFunLike.coe] at this ⊢
      simp only [WeightedChain.val_apply] at this ⊢
      simp [this]; clear this
      gcongr
      intro j
      magic_simp
      apply le_wSup_of_le i
      apply wle_refl _
    · intro f g hfg n; simp only; split <;> simp_all [hfg _]
  · exact wSup_le fun i ↦ WeightedSum_mono (le_wSup_of_le i (wle_refl _))

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_eq_finset_sum {α I : Type}
    [WeightedPreSemiring α]
    [DecidableEq I] (S : Finset I) (f : I → α) :
    letI : AddCommMonoid α := WeightedPreSemiring.toAddCommMonoid α
    ⨁ᶠ x ∈ S, f x = ∑ x ∈ S, f x := by
  letI : AddCommMonoid α := WeightedPreSemiring.toAddCommMonoid α
  induction S using Finset.induction with
  | empty => simp_all; rfl
  | insert x S hxS ih =>
    simp_all
    rfl

omit [WeightedOmegaCompletePartialOrder α] [WeightedOmegaContinuousPreSemiring α] [WeightedPreSemiring α] in
theorem Finset.fold_list_toFinset {I : Type} [DecidableEq I] (S : List I) (hS : S.Nodup) (op : α → α → α) [Std.Commutative op] [Std.Associative op] (init : α) (f : I → α) :
    S.toFinset.fold op init f = S.foldr (fun a b ↦ op (f a) b) init := by
  induction S with
  | nil => simp
  | cons x S ih => simp_all

omit [WeightedOmegaCompletePartialOrder α] [WeightedOmegaContinuousPreSemiring α] in
@[simp]
theorem WeightedFinsum_union_singleton {I : Type} [DecidableEq I] (S : Finset I) (x : I) (h : x ∉ S) (f : I → α) :
    ⨁ᶠ x ∈ S ∪ {x}, f x = (⨁ᶠ x ∈ S, f x) ⨁ f x := by
  have : S ∪ {x} = insert x S := by ext; simp_all [or_comm]
  simp [this]; clear this
  simp [WeightedFinsum]
  rw [Finset.fold_insert h]
  simp [WeightedPreSemiring.wAdd_comm]

theorem wle_of_eq {α : Type} [WeightedPartialOrder α] {a b : α} (h : a = b) : a ≼ b := by simp_all

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_bij {α ι γ : Type}
    [WeightedPreSemiring α]
    [DecidableEq ι] [DecidableEq γ]
    {Sι : Finset ι} {Sγ : Finset γ} {fι : ι → α} {fγ : γ → α}
    (i : ∀ a ∈ Sι, γ) (hi : ∀ a ha, i a ha ∈ Sγ)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ Sγ, ∃ a ha, i a ha = b) (h : ∀ a ha, fι a = fγ (i a ha))
    :
    ⨁ᶠ a ∈ Sι, fι a = ⨁ᶠ b ∈ Sγ, fγ b := by
  simp [WeightedFinsum_eq_finset_sum]
  letI := WeightedPreSemiring.toAddCommMonoid α
  apply Finset.sum_bij i <;> assumption

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_bij_ne_zero {α ι γ : Type}
    [WeightedPreSemiring α]
    [DecidableEq ι] [DecidableEq γ]
    {Sι : Finset ι} {Sγ : Finset γ} {fι : ι → α} {fγ : γ → α}
    (i : ∀ a ∈ Sι, fι a ≠ 𝟘 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ Sγ)
    (i_inj : ∀ a₁ ha₁₁ ha₁₂ a₂ ha₂₁ ha₂₂, i a₁ ha₁₁ ha₁₂ = i a₂ ha₂₁ ha₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ Sγ, fγ b ≠ 𝟘 → ∃ a h₁ h₂, i a h₁ h₂ = b) (h : ∀ a h₁ h₂, fι a = fγ (i a h₁ h₂))
    :
    ⨁ᶠ a ∈ Sι, fι a = ⨁ᶠ b ∈ Sγ, fγ b := by
  simp [WeightedFinsum_eq_finset_sum]
  letI := WeightedPreSemiring.toAddCommMonoid α
  apply Finset.sum_bij_ne_zero i <;> assumption

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_single {α I : Type}
    [WeightedPreSemiring α]
    [DecidableEq I] {S : Finset I} {f : I → α} (x : I)
    (h₀ : ∀ y ∈ S, y ≠ x → f y = 𝟘)
    (h₁ : x ∉ S → f x = 𝟘) :
    ⨁ᶠ i ∈ S, f i = f x := by
  simp [WeightedFinsum_eq_finset_sum]
  letI := WeightedPreSemiring.toAddCommMonoid α
  rw [Finset.sum_eq_single x h₀ h₁]

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_union {α I : Type}
    [WeightedPreSemiring α]
    [DecidableEq I] {S₁ S₂ : Finset I} {f : I → α}
    (h : Disjoint S₁ S₂) : ⨁ᶠ i ∈ (S₁ ∪ S₂), f i = (⨁ᶠ i ∈ S₁, f i) ⨁ ⨁ᶠ i ∈ S₂, f i := by
  simp [WeightedFinsum_eq_finset_sum]
  letI := WeightedPreSemiring.toAddCommMonoid α
  rw [Finset.sum_union h]
  rfl

theorem WeightedFinsum_le_of_subset {α I : Type} [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α]
    [WeightedOmegaContinuousPreSemiring α] [DecidableEq I] {S₁ S₂ : Finset I} {f : I → α}
    (h : S₁ ⊆ S₂) : ⨁ᶠ i ∈ S₁, f i ≼ ⨁ᶠ i ∈ S₂, f i := by
  set S₃ := S₂ \  S₁
  have : S₂ = S₁ ∪ S₃ := by simp [S₃, h]
  simp_all
  rw [WeightedFinsum_union]
  · exact wle_wAdd (⨁ᶠ i ∈ S₁, f i) (⨁ᶠ i ∈ S₃, f i)
  · simp [S₃]; exact Finset.disjoint_sdiff

theorem WeightedFinsum_add {ι 𝒮 : Type} [DecidableEq ι] [WeightedPreSemiring 𝒮]
    (I : Finset ι)
    (f g : ι → 𝒮) :
    ⨁ᶠ i ∈ I, (f i ⨁ g i) = (⨁ᶠ i ∈ I, f i) ⨁ ⨁ᶠ i ∈ I, g i := by
  induction I using Finset.induction with
  | empty => simp
  | insert x I hx ih =>
    simp_all only [not_false_eq_true, WeightedFinsum_insert]
    grind only [WeightedPreSemiring.wAdd_comm, WeightedPreSemiring.wAdd_assoc]

theorem WeightedFinsum_comm {α ι 𝒮 : Type} [DecidableEq α] [DecidableEq ι]
  [WeightedPreSemiring 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮]
    (A : Finset α) (I : Finset ι)
    (f : α → ι → 𝒮) :
    ⨁ᶠ x ∈ A, ⨁ᶠ i ∈ I, f x i = ⨁ᶠ i ∈ I, ⨁ᶠ x ∈  A, f x i := by
  induction A using Finset.induction with
  | empty =>
    symm
    simp only [WeightedFinsum_empty, WeightedFinsum_eq_zero_iff, implies_true]
  | insert x I hx ih =>
    simp_all
    simp [WeightedFinsum_add]

theorem WeightedFinsum_prod_comm {α ι 𝒮 : Type} [Encodable α] [DecidableEq α] [Encodable ι] [DecidableEq ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (A : Finset α) (I : Finset ι)
    (f : α → ι → 𝒮) :
    ⨁ᶠ (x ∈ A) (i ∈ I), f x i = ⨁ᶠ (i ∈ I) (x ∈ A), f x i := by
  apply WeightedFinsum_bij (fun (a, b) _  ↦ (b, a))
  all_goals (try simp) <;> grind

-- TODO: move this as early as possible
attribute [local simp] Encodable.decode₂_eq_some in
theorem WeightedSum_le_of_finset {α 𝒮 : Type} [Encodable α] [DecidableEq α]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : α → 𝒮} {a : 𝒮} (h : ∀ S : Finset α, ⨁ᶠ x ∈ S, f x ≼ a) :
    ⨁' x : α, f x ≼ a := by
  apply wSup_le fun i ↦ ?_
  magic_simp [WeightedSum_chain]
  let S := Finset.range i |>.filterMap (Encodable.decode₂ α) (by simp_all)
  apply wle_trans _ (h S); clear h
  apply wle_of_eq
  symm
  apply WeightedFinsum_bij_ne_zero (fun x _ _ ↦ Encodable.encode x)
  · simp_all [S]
  · simp_all [S]
  · simp_all [S]
    intro b hb hb'
    split at hb'
    · simp_all; subst_eqs
      simp_all
    · contradiction
  · simp_all [S]

-- TODO: move this as early as possible
attribute [local simp] Encodable.decode₂_eq_some in
theorem WeightedSum_finset_le {α 𝒮 : Type} [Encodable α] [DecidableEq α]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : α → 𝒮} (S : Finset α) :
    ⨁ᶠ x ∈ S, f x ≼ ⨁' x : α, f x := by
  let actual := S.image Encodable.encode
  if h_nonempty : actual = {} then simp_all [actual] else
  let top := (actual.max' (Finset.nonempty_iff_ne_empty.mpr h_nonempty) + 1)
  apply le_wSup_of_le top
  magic_simp
  simp [WeightedSum_chain]
  magic_simp
  let S' : Finset ℕ := Finset.range top |>.filter (Encodable.decode₂ α · |>.isSome)
  rw [WeightedFinsum_bij_ne_zero (Sι:=Finset.range top) (Sγ:=S')
      (fγ:=(fun x ↦ match Encodable.decode₂ _ x with | some x => f x | none => 𝟘))
      (fun q h₁ h₂ ↦ q)]
  · rw [WeightedFinsum_bij_ne_zero (Sι:=S) (Sγ:=actual) (fγ:=(fun x ↦ match Encodable.decode₂ _ x with | some x => f x | none => 𝟘)) (fun q _ _ ↦ Encodable.encode q)]
    · refine WeightedFinsum_le_of_subset ?_
      intro
      simp_all [S', actual, top]
      intro a ha ha'
      subst_eqs
      simp_all
      refine Nat.lt_add_one_of_le ?_
      apply Finset.le_max'
      simp [ha]
    · simp_all [S', actual, top]
    · simp_all
    · simp_all; intro a ha; split
      · simp_all; subst_eqs; simp_all [S', actual, top]
      · simp
    · simp_all
  · simp_all [top, actual]
    intro a ha
    split
    · simp_all; subst_eqs
      simp_all [S', top, actual]
    · simp
  · simp
  · simp_all
    intro a ha
    split
    · simp_all; subst_eqs; simp_all [S']
    · simp
  · simp_all
    intro a ha
    split
    · simp_all; subst_eqs; simp
    · simp_all

theorem WeightedSum_with_encoding_wle {I : Type} [DecidableEq I] (e₀ e₁ : Encodable I) (f : I → α) :
    @WeightedSum I α _ _ _ e₀ f ≼ @WeightedSum I α _ _ _ e₁ f :=
  letI := e₀; WeightedSum_le_of_finset fun _ ↦ letI := e₁; WeightedSum_finset_le _

theorem WeightedSum_with_encoding {I : Type} [DecidableEq I] (e₀ e₁ : Encodable I) (f : I → α) :
    @WeightedSum I α _ _ _ e₀ f = @WeightedSum I α _ _ _ e₁ f :=
  wle_antisymm (WeightedSum_with_encoding_wle e₀ e₁ f) (WeightedSum_with_encoding_wle e₁ e₀ f)

theorem WeightedSum_finset {I : Type} [DecidableEq I] [Encodable I] (S : Finset I) (f : I → α) :
    ⨁' x : S, f x = ⨁ᶠ x ∈ S, f x := by
  apply wle_antisymm
  · apply WeightedSum_le_of_finset fun S₀ ↦ ?_
    rw [WeightedFinsum_bij  (Sγ:=S₀.map ⟨(·.val), ?_⟩) (fun x _ ↦ x.val) (fγ:=(f ·))]
    · apply WeightedFinsum_le_of_subset; intro; simp_all
    all_goals simp
  · apply wle_trans _ (WeightedSum_finset_le S.attach)
    nth_rw 2 [WeightedFinsum_bij  (Sγ:=S.attach.map ⟨(·.val), ?_⟩) (fun x _ ↦ x.val) (fγ:=(f ·))]
    · apply WeightedFinsum_le_of_subset; intro; simp
    all_goals simp

theorem WeightedSum_finite {I : Type} [DecidableEq I] [Encodable I] [hfin : Finite I] (f : I → α) :
    ⨁' x : I, f x = ⨁ᶠ x ∈ Set.finite_univ.toFinset, f x :=
  wle_antisymm
    (WeightedSum_le_of_finset fun S₀ ↦ WeightedFinsum_le_of_subset (by simp))
    (WeightedSum_finset_le _)

variable [WeightedSemiring α] [WeightedOmegaContinuousPreSemiring α] in
example : ⨁' _ : Fin 4, (𝟙 : α) = 𝟙 ⨁ 𝟙 ⨁ 𝟙 ⨁ 𝟙 := by
  have : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := rfl
  simp_all [WeightedSum_finite, WeightedPreSemiring.wAdd_comm]

-- TODO: move this as early as possible
@[reducible]
instance : Trans (· ≼ · : 𝒮 → 𝒮 → Prop) (· ≼ · : 𝒮 → 𝒮 → Prop) (· ≼ · : 𝒮 → 𝒮 → Prop) where
  trans := wle_trans

theorem wSup_skip {α : Type} [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]
    {C : WeightedChain α} (n : ℕ) :
    wSup C = wSup ⟨fun i ↦ C (i + n), fun hab ↦ by simp; apply C.prop; simp_all⟩ := by
  apply wle_antisymm
  · apply wSup_le fun i ↦ le_wSup_of_le i ?_
    exact C.prop (by simp)
  · exact wSup_le fun i ↦ le_wSup_of_le (i + n) (by magic_simp)

theorem wSup_skip' {C : WeightedChain α} (n : ℕ) :
    wSup C = wSup ⟨fun i ↦ C (n + i), fun hab ↦ by simp; apply C.prop; simp_all⟩ := by
  rw [wSup_skip n]
  simp [add_comm]


theorem WeightedSum_subtype_le {ι : Type} [Encodable ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (f : ι → 𝒮) :
    ⨁' (x : {x // P x}), f x.val ≼ ⨁' x, f x := by
  apply WeightedSum_le_of_finset
  intro S
  rw [WeightedFinsum_bij (Sγ:=S.map ⟨(·.val), by simp⟩) (fγ:=f) (fun x _ ↦ x.val)] <;> try simp
  apply WeightedSum_finset_le

open WeightedOmegaCompletePartialOrder
-- omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder in
theorem wSup_wSup {α : Type} [WeightedOmegaCompletePartialOrder α] (f : ℕ → ℕ → α) (h₁ : WeightedMonotone f) (h₂ : WeightedMonotone (fun x y ↦ f y x)) :
      wSup ⟨fun n ↦ wSup ⟨fun m ↦ f n m, fun a ↦ h₂ a n⟩, by
        intro s₁ s₂ h₁₂; simp only; gcongr; exact h₁ h₁₂⟩
    = wSup ⟨fun n ↦ f n n, by
        intro s₁ s₂ h₁₂; simp; exact wle_trans (h₁ h₁₂ s₁) (h₂ h₁₂ s₂)⟩ := by
  apply wle_antisymm _ (wSup_le fun n ↦ le_wSup_of_le n (le_wSup_of_le n (by magic_simp)))
  apply wSup_le fun n ↦ ?_
  apply wSup_le fun m ↦ ?_
  apply le_wSup_of_le (max n m) <| wle_trans (h₁ (by simp) m) (h₂ (by simp) (max n m))

theorem W.supp_comp_eq_preimage {α ι γ : Type}
    [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] [Encodable ι] [Encodable γ]
    (f : ι → α) (g : γ → ι) :
    W.supp (f ∘ g) = g ⁻¹' W.supp f :=
  rfl

open scoped Classical in
theorem Function.Injective.WeightedSum_eq {α ι γ : Type}
    [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] [Encodable ι] [Encodable γ]
    {g : γ → ι} (hg : Injective g) {f : ι → α}
    (hf : W.supp f ⊆ Set.range g) : ⨁' c, f (g c) = ⨁' b, f b := by
  have : W.supp f = g '' W.supp (f ∘ g) := by
    rw [W.supp_comp_eq_preimage, Set.image_preimage_eq_of_subset hf]
  rw [← Function.comp_def]
  apply WeightedPartialOrder.wle_antisymm
  · apply WeightedSum_le_of_finset
    intro S
    let S' : Finset ι := S.map ⟨g, hg⟩
    apply WeightedPartialOrder.wle_trans _ (WeightedSum_finset_le S')
    apply wle_of_eq
    apply WeightedFinsum_bij_ne_zero fun x _ _ ↦ g x
    · simp_all [S']
    · simp_all [S']
      intro a₁ ha₁ ha₁' a₂ ha₂ ha₂' h
      exact hg h
    · simp_all [S']
      intro a haS hfga
      use a
    · simp_all
  · apply WeightedSum_le_of_finset
    intro S
    let S' : Finset γ := S.preimage g (by intro _ _ _ _; apply hg)
    apply WeightedPartialOrder.wle_trans _ (WeightedSum_finset_le S')
    apply wle_of_eq
    symm
    apply WeightedFinsum_bij_ne_zero fun x _ _ ↦ g x
    · simp_all [S']
    · simp_all [S']
      intro a₁ ha₁ ha₁' a₂ ha₂ ha₂' h
      exact hg h
    · simp_all [S']
      intro a haS hfga
      suffices ∃ x, g x = a by obtain ⟨x, ⟨_⟩⟩ := this; use x
      have hs : a ∈ W.supp f := hfga
      simp only [this, Set.mem_image, W.supp_mem_iff, Function.comp_apply, ne_eq, S'] at hs
      obtain ⟨x, hx, hx'⟩ := hs
      use x
    · simp_all

theorem WeightedSum_subtype_eq_of_supp_subset {α ι : Type}
    [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] [Encodable ι]
    {f : ι → α} {s : Set ι} (hs : W.supp f ⊆ s) :
    letI : Encodable s := Encodable.ofCountable ↑s
    ⨁' x : s, f x = ⨁' x, f x :=
  letI : Encodable { x // x ∈ s } := Encodable.ofCountable { x // x ∈ s }
  Subtype.val_injective.WeightedSum_eq <| by simpa

theorem WeightedSum_substype_supp {α ι : Type}
    [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] [Encodable ι]
    (f : ι → α) :
    letI : Encodable ↑(W.supp f) := Encodable.ofCountable ↑(W.supp f)
    ⨁' x : W.supp f, f x = ⨁' x, f x :=
  WeightedSum_subtype_eq_of_supp_subset Set.Subset.rfl

theorem WeightedSum_eq_WeightedSum_of_ne_one_bij {α ι γ : Type}
    [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] [Encodable ι] [Encodable γ]
    {f : ι → α} {g : γ → α} (i : W.supp g → ι) (hi : Function.Injective i)
    (hf : W.supp f ⊆ Set.range i) (hfg : ∀ x, f (i x) = g x) : ⨁' x, f x = ⨁' y, g y := by
  letI : Encodable ↑(W.supp g) := Encodable.ofCountable ↑(W.supp g)
  rw [← WeightedSum_substype_supp g, ← hi.WeightedSum_eq hf]
  simp only [hfg]

omit [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem WeightedFinsum_apply {α ι 𝒮 : Type} [DecidableEq α] [WeightedPreSemiring 𝒮] (S : Finset α) (f : α → ι → 𝒮) (i : ι) :
    (⨁ᶠ x ∈ S, f x) i = ⨁ᶠ x ∈ S, f x i := by
  simp [WeightedFinsum]
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S hx ih =>
    simp_all [WeightedAdd.wAdd]

omit [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem WeightedSum_apply {α ι : Type} [Encodable α] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) (i : ι) :
    (⨁' (x : α), f x) i = ⨁' (x : α), f x i := by
  simp [WeightedSum]
  congr
  ext n
  simp [WeightedChain.map, WeightedSum_chain]
  magic_simp
  simp
  congr with x
  split
  · simp_all
  · rfl

theorem WeightedSum_comm_le {α ι 𝒮 : Type} [Encodable α] [DecidableEq α] [Encodable ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) :
    ⨁' (x : α) (i : ι), f x i ≼ ⨁' (i : ι) (x : α), f x i := by
  apply WeightedSum_le_of_finset
  intro S
  calc
    _ = ⨁' (i : ι), ⨁ᶠ x ∈ S, f x i := by
      induction S using Finset.induction with
      | empty => simp
      | insert x S hx ih =>
        simp_all
        rw [WeightedSum_add]
    _ ≼ ⨁' (i : ι) (x : α), f x i := by
      apply WeightedSum_mono fun i ↦ WeightedSum_finset_le _
theorem WeightedSum_comm {α ι 𝒮 : Type} [Encodable α] [Encodable ι] [DecidableEq α] [DecidableEq ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) :
    ⨁' (x : α) (i : ι), f x i = ⨁' (i : ι) (x : α), f x i :=
  wle_antisymm (WeightedSum_comm_le _) (WeightedSum_comm_le _)

theorem WeightedSum_WeightedFinset_comm {α ι 𝒮 : Type} [Encodable α] [DecidableEq α] [Encodable ι] [DecidableEq ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) (S : Finset ι) :
    ⨁' (x : α), ⨁ᶠ i ∈ S, f x i = ⨁ᶠ i ∈ S, ⨁' (x : α), f x i := by
  simp [← WeightedSum_finset]
  rw [WeightedSum_comm]

theorem WeightedSum_nat_le {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : ℕ → 𝒮} (a : 𝒮) (h : ∀ n, ⨁ᶠ x ∈ Finset.range n, f x ≼ a) :
    ⨁' (x : ℕ), f x ≼ a := by
  apply WeightedSum_le_of_finset
  intro S
  if hS : ¬S.Nonempty then simp_all else
  apply Decidable.not_not.mp at hS
  apply wle_trans (WeightedFinsum_le_of_subset ?_) (h (S.max' hS + 1))
  exact fun x hx ↦ Finset.mem_range.mpr <| Nat.lt_add_one_of_le <| Finset.le_max' _ _ hx
theorem WeightedSum_le_nat {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : ℕ → 𝒮} (a : 𝒮) (n : ℕ) (h : a ≼ ⨁ᶠ x ∈ Finset.range n, f x) :
    a ≼ ⨁' (x : ℕ), f x :=
  wle_trans h <| WeightedSum_finset_le (Finset.range n)
attribute [local simp] Encodable.decode₂_eq_some in
theorem WeightedSum_nat_eq_succ {f : ℕ → 𝒮} : ⨁' (x : ℕ), f x = f 0 ⨁ ⨁' (x : ℕ), f (x + 1) := by
  apply wle_antisymm
  · apply WeightedSum_nat_le
    intro n
    rcases n with _ | n
    · simp
    · rw [add_comm]
      simp
      apply wAdd_mono_left
      simp [add_comm]
      apply WeightedSum_finset_le
  · simp [WeightedSum]
    rw [WeightedOmegaContinuousAddRight]
    apply wSup_le fun i ↦ ?_
    apply le_wSup_of_le (1 + i)
    magic_simp [WeightedSum_chain]
    simp
    split
    · simp_all [Encodable.decode₂_eq_some]; subst_eqs
      apply wAdd_mono_left
      apply WeightedFinsum_mono
      intro i
      simp
      split <;> split <;> simp_all
      rw [add_comm]
      simp
    · simp_all [Encodable.decode₂_eq_some]

end
