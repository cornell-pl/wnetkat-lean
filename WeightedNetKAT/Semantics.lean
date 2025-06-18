import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.Equiv.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax

variable {X : Type} {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]

noncomputable instance : DecidableEq (𝒲 𝒮 H[F]) := Classical.typeDecidableEq (𝒲 𝒮 H)

noncomputable def Predicate.sem (p : Predicate[F]) : H[F] → 𝒲 𝒮 H[F] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => if π f = n then η (π::h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.sem h ≫= fun h ↦ η h ⨁ ((if t.sem h = 𝟘 then η h else 𝟘) ≫= u.sem))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ t.sem h ≫= u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 𝟘 then η h else 𝟘

instance : Subst Pk[F] F ℕ where
  subst pk f n := fun f' ↦ if f = f' then n else pk f'

@[simp]
def Policy.iter (p : Policy[F,X]) : ℕ → Policy[F,X]
  | 0 => wnk_policy { skip }
  | n+1 => wnk_policy {~p ; ~(p.iter n)}

@[simp, reducible] instance Policy.instHPow : HPow Policy[F,X] ℕ Policy[F,X] where hPow p n := p.iter n

@[simp]
def Policy.iterDepth : Policy[F,X] → ℕ
| .Filter _ | wnk_policy {~_ ← ~_} | wnk_policy {dup} => 0
| wnk_policy {~p ⨁ ~q} | wnk_policy {~p ; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_policy {~_ ⨀ ~q} => q.iterDepth
| wnk_policy {~p *} => p.iterDepth + 1

omit [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype F] [DecidableEq F] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,X]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

open WeightedOmegaCompletePartialOrder in
noncomputable def Policy.sem (p : Policy[F,𝒮]) : H[F] → 𝒲 𝒮 H[F] := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π[f ↦ n]::h)
  | wnk_policy {dup} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π::π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem h ≫= q.sem)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ ⟨fun h' ↦ w ⨀ p.sem h h', SetCoe.countable (W.supp (w ⨀ sem p h ·))⟩
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem h ⨁ q.sem h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁' n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Predicate[F]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Predicate.sem]

noncomputable def Φ (p : Policy[F,𝒮]) (d : H[F] → 𝒲 𝒮 H[F]) : H[F] → 𝒲 𝒮 H[F] :=
  fun h ↦ η h ⨁ (p.sem h ≫= d)

example {p : Policy[F,𝒮]} : Φ p (wnk_policy {~p*}.sem) = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  ext
  unfold Φ
  simp [WeightedAdd.wAdd, Policy.sem, Predicate.sem]

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

-- TODO: move this as early as possible
@[reducible]
instance : Trans (· ≼ · : 𝒮 → 𝒮 → Prop) (· ≼ · : 𝒮 → 𝒮 → Prop) (· ≼ · : 𝒮 → 𝒮 → Prop) where
  trans := wle_trans
@[reducible]
instance : Trans (· ≼ · : 𝒲 𝒮 H[F] → 𝒲 𝒮 H[F] → Prop) (· ≼ · : 𝒲 𝒮 H[F] → 𝒲 𝒮 H[F] → Prop) (· ≼ · : 𝒲 𝒮 H[F] → 𝒲 𝒮 H[F] → Prop) where
  trans := wle_trans

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

end

omit [Fintype F] [DecidableEq F] in
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono (f : 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=H[F] → 𝒲 𝒮 H[F]) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
omit [Fintype F] [DecidableEq F] in
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono_right (f : 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=H[F] → 𝒲 𝒮 H[F]) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
omit [Fintype F] [DecidableEq F] in
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono_left (g : H[F] → 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=𝒲 𝒮 H[F]) (· ≫= g) := by
  intro a b hab h
  simp
  have : DecidableEq H[F] := Classical.typeDecidableEq _
  apply WeightedSum_le_of_finset fun Sa ↦ ?_
  have : ∀ x, ¬a.val x = 𝟘 → ¬b.val x = 𝟘 := by
    intro x hx
    contrapose! hx
    have := hab x
    simp_all
  let S : Finset H[F] := Sa.map ⟨(·.val), by simp⟩
  let Sb : Finset ↑b.supp := Sa.map ⟨(fun ⟨x, h⟩ ↦ ⟨x, this x h⟩), by intro; simp [Subtype.val_inj]⟩
  apply WeightedPartialOrder.wle_trans _ (WeightedSum_finset_le Sb)
  rw [WeightedFinsum_bij (Sι:=Sa) (Sγ:=S) (fγ:=fun x ↦ a x ⨀ g x h) (fun x _ ↦ x.val)]
  · rw [WeightedFinsum_bij (Sι:=Sb) (Sγ:=S) (fγ:=fun x ↦ b x ⨀ g x h) (fun x _ ↦ x.val)]
    · apply WeightedFinsum_mono
      intro x
      simp
      apply wMul_mono_right _ (hab x)
    · simp_all [Sb, S]
      rintro x hbx y hax hy' ⟨_⟩
      simp_all
    · simp_all [Sb, S]
    · simp_all [Sb, S]
    · simp_all [Sb, S]
  · simp_all [Sb, S]
  · simp_all [Sb]
  · simp_all [Sb, S]
  · simp_all [Sb, S]

open WeightedOmegaCompletePartialOrder in
omit [Fintype F] [DecidableEq F] in
theorem 𝒲.bind_continuous (f : 𝒲 𝒮 H[F]) : WeightedOmegaContinuous (f ≫= ·) f.bind_mono := by
  intro C
  ext h
  simp only
  simp [bind, DFunLike.coe]
  simp [wSup]
  simp only [WeightedChain.map, DFunLike.coe]
  simp [WeightedOmegaContinuousMulRight]
  simp only [WeightedChain.map, DFunLike.coe]
  simp
  have :=  @WeightedSum_cont f.supp 𝒮 _ _ _
  unfold WeightedOmegaContinuous at this
  simp only [WeightedChain.map, DFunLike.coe] at this
  simp [wSup] at this
  simp only [WeightedChain.map, DFunLike.coe] at this
  simp at this
  convert this _
  rotate_right
  . exact ⟨fun n x ↦ f x ⨀ (C n x) h, by
      intro j k le point
      simp
      apply wMul_gconr
      . simp
      . exact C.prop le point h
      ⟩
  . simp only [WeightedChain.map, DFunLike.coe]
  . simp only [WeightedChain.map, DFunLike.coe]

theorem WeightedSum_subtype_le {ι : Type} [Encodable ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (f : ι → 𝒮) :
    ⨁' (x : {x // P x}), f x.val ≼ ⨁' x, f x := by
  apply WeightedSum_le_of_finset
  intro S
  rw [WeightedFinsum_bij (Sγ:=S.map ⟨(·.val), by simp⟩) (fγ:=f) (fun x _ ↦ x.val)] <;> try simp
  apply WeightedSum_finset_le

open WeightedOmegaCompletePartialOrder
-- omit [Fintype F] [DecidableEq F] in

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
      simp only [this, Set.mem_image, W.supp_mem_iff, comp_apply, ne_eq, S'] at hs
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

open WeightedOmegaContinuousPreSemiring in
omit [DecidableEq F] in
theorem 𝒲.bind_continuous'' (g : H[F] → 𝒮) (C : WeightedChain (𝒲 𝒮 H[F])) :
      wSup ⟨fun n ↦ ⨁' (i : (wSup C).supp), C n i ⨀ g i, by
        intro a b hab; apply WeightedSum_mono
        apply wMul_mono_right
        intro i
        apply C.prop hab⟩
    = wSup ⟨fun n ↦ ⨁' (x : (C n).supp), C n x ⨀ g x, by
      intro a b hab
      simp only
      letI : Encodable H[F] := Encodable.ofCountable H
      have q := fun a ↦
        WeightedSum_eq_WeightedSum_of_ne_one_bij
          (ι:=(C a).supp) (γ:=H[F]) (f:=fun x ↦ C a x ⨀ g x) (g:=fun x ↦ C a x ⨀ g x)
          (fun ⟨x, hx⟩ ↦ ⟨x, by contrapose hx; simp at hx; replace hx : C a x = 𝟘 := hx; simp [hx]⟩)
      rw [q a, q b]
      · apply WeightedSum_mono
        apply wMul_mono_right
        exact C.prop hab
      all_goals intro ⟨_, _⟩; simp_all⟩ := by
  congr with n
  have : (C n).supp ⊆ (wSup C).supp := by
    intro x
    simp only [W.supp_mem_iff, ne_eq, WeightedOmegaCompletePartialOrder.instCountablePi,
      wSup_eq_zero_iff, not_forall]
    magic_simp
    intro h'
    use n
  apply WeightedSum_eq_WeightedSum_of_ne_one_bij (fun ⟨x, hx⟩ ↦ ⟨x.val, this x.prop⟩)
  · intro ⟨⟨a, _⟩, ha⟩ ⟨b, hb⟩; simp_all
  · intro ⟨a, ha⟩
    simp_all
    simp_all
    contrapose!
    intro h
    have : C n a = 𝟘 := h
    simp [this]
  · simp

omit [DecidableEq F] in
theorem 𝒲.bind_continuous' (g : H[F] → 𝒲 𝒮 H[F]) :
    WeightedOmegaContinuous (· ≫= g) (𝒲.bind_mono_left g) := by
  intro C
  ext h
  simp only
  magic_simp [bind]
  letI : Encodable (wSup C).supp := instEncodableElemSuppValWCountable
  simp
  have : ∀ (x : (wSup C).supp), (wSup C).val ↑x = wSup ⟨(C · x), (C.prop · x)⟩ := by
    simp [WeightedOmegaCompletePartialOrder.instCountablePi]
    magic_simp
    simp
  simp [this]; clear this
  simp [WeightedOmegaContinuousMulLeft]
  magic_simp
  simp
  have := WeightedSum_cont (X:=(wSup C).supp) (𝒮:=𝒮) ⟨fun n x ↦ (C n) ↑x ⨀ (g x) h, by
    intro a b hab i
    apply wMul_mono_right
    apply C.prop hab⟩
  simp only [wSup_apply, WeightedChain.map, DFunLike.coe] at this
  simp only [WeightedChain.val_apply] at this
  simp [this]; clear this
  conv =>
    right
    simp [instCountablePi]
  magic_simp
  simp
  apply 𝒲.bind_continuous'' (g · h)

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder

theorem Φ_mono (p : Policy[F,𝒮]) : WeightedMonotone (Φ p) :=
  fun hab h ↦ wAdd_mono_left (η h) (𝒲.bind_mono _ hab)
theorem Φ_continuous (p : Policy[F,𝒮]) : WeightedOmegaContinuous (Φ p) (Φ_mono p) := by
  intro C
  ext h
  unfold Φ
  set f := p.sem h
  have := f.bind_continuous C
  have := wAdd_wSup (η h) (C.map (f ≫= ·) f.bind_mono)
  simp_all only
  rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem 𝒲.wZero_le (p : 𝒲 𝒮 H[F]) : 𝟘 ≼ p := by intro; simp
omit [Fintype F] [DecidableEq F] in
@[simp] theorem 𝒲.Pi_wZero_le {X : Type} (p : X → 𝒲 𝒮 H[F]) : 𝟘 ≼ p := fun _ ↦ 𝒲.wZero_le _

noncomputable def Φ_chain (p : Policy[F,𝒮]) : WeightedChain (H[F] → 𝒲 𝒮 H[F]) :=
  ⟨fun n ↦ (Φ p)^[n] 𝟘, by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ c hac ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      apply wle_trans ih; clear! a
      induction c with
      | zero => simp
      | succ c ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        apply Φ_mono _ ih⟩
noncomputable def Φ_wSup (p : Policy[F,𝒮]) := wSup (Φ_chain p)

def IsLfp {α : Type} [WeightedOmegaCompletePartialOrder α]
    (f : α → α) (p : α) : Prop :=
  f p = p ∧ ∀ p', f p' = p' → p ≼ p'

theorem IsLfp_unique {α : Type} [WeightedOmegaCompletePartialOrder α] {f : α → α} {p₁ p₂ : α}
    (h₁ : IsLfp f p₁) (h₂ : IsLfp f p₂) : p₁ = p₂ :=
  wle_antisymm (h₁.right _ h₂.left) (h₂.right _ h₁.left)

theorem Policy.Φ_wSup_isLfp (p : Policy[F,𝒮]) : IsLfp (Φ p) (Φ_wSup p) := by
  constructor
  · simp only [Φ_wSup]
    apply wle_antisymm
    · rw [Φ_continuous]
      apply wSup_le
      intro i
      apply le_wSup_of_le (i + 1)
      simp only [DFunLike.coe, WeightedChain.map, Φ_chain, Function.iterate_succ',
        Function.comp_apply, wle_refl]
    · apply wSup_le
      intro i
      simp only [DFunLike.coe]
      rcases i with _ | i
      · simp [Φ_chain, DFunLike.coe]
      · simp only [Φ_chain, Function.iterate_succ', Function.comp_apply]
        apply Φ_mono _ (le_wSup_of_le i (by simp [DFunLike.coe]))
  · intro x hx
    refine wSup_le fun i ↦ ?_
    induction i with
    | zero => simp [Φ_chain, DFunLike.coe]
    | succ i ih =>
      simp only [DFunLike.coe, Φ_chain, Function.iterate_succ', Function.comp_apply]
      rw [← hx]
      apply Φ_mono p ih

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

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem WeightedFinsum_apply' {α : Type} [DecidableEq α] (S : Finset α) (f : α → 𝒲 𝒮 H[F]) (i : H[F]) :
    (⨁ᶠ x ∈ S, f x) i = ⨁ᶠ x ∈ S, f x i := by
  simp [WeightedFinsum]
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S hx ih =>
    simp_all [WeightedAdd.wAdd]
    magic_simp
    congr

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem WeightedFinsum_apply'' {α : Type} [DecidableEq α] (S : Finset α) (f : α → 𝒲 𝒮 H[F]) (i : H[F]) :
    (⨁ᶠ x ∈ S, f x).val i = ⨁ᶠ x ∈ S, f x i := by
  simp [WeightedFinsum]
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert x S hx ih =>
    simp_all [WeightedAdd.wAdd]
    magic_simp

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem WeightedSum_apply' {α : Type} [Encodable α]
    (f : α → 𝒲 𝒮 H[F]) (i : H[F]) :
    (⨁' (x : α), f x) i = ⨁' (x : α), f x i := by
  simp [WeightedSum]
  unfold WeightedOmegaContinuousPreSemiring.instCountablePi
  unfold WeightedOmegaCompletePartialOrder.instCountablePi
  simp
  simp [instFunLike𝒲]
  simp [WeightedChain.map, WeightedSum_chain]
  magic_simp
  congr
  ext n
  simp [DFunLike.coe]
  congr! with x
  split
  · simp
  · rfl

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem WeightedSum_apply'' {α : Type} [Encodable α]
    (f : α → 𝒲 𝒮 H[F]) (i : H[F]) :
    (⨁' (x : α), f x).val i = ⨁' (x : α), f x i := by
  rw [← WeightedSum_apply']
  rfl

omit [Fintype F] [DecidableEq F] in
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
omit [Fintype F] [DecidableEq F] in
theorem WeightedSum_comm {α ι 𝒮 : Type} [Encodable α] [Encodable ι] [DecidableEq α] [DecidableEq ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) :
    ⨁' (x : α) (i : ι), f x i = ⨁' (i : ι) (x : α), f x i :=
  wle_antisymm (WeightedSum_comm_le _) (WeightedSum_comm_le _)

omit [Fintype F] [DecidableEq F] in
theorem WeightedSum_WeightedFinset_comm {α ι 𝒮 : Type} [Encodable α] [DecidableEq α] [Encodable ι] [DecidableEq ι]
  [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) (S : Finset ι) :
    ⨁' (x : α), ⨁ᶠ i ∈ S, f x i = ⨁ᶠ i ∈ S, ⨁' (x : α), f x i := by
  simp [← WeightedSum_finset]
  rw [WeightedSum_comm]

omit [DecidableEq F] in
theorem 𝒲.bind_sum {f : 𝒲 𝒮 H[F]} {g : ℕ → H[F] → 𝒲 𝒮 H[F]} :
    (f ≫= ⨁' (x : ℕ), g x) = (⨁' (x : ℕ), (f ≫= g x)) := by
  simp [bind]
  ext h
  simp
  magic_simp
  simp [← WeightedSum_mul_left]
  rw [WeightedSum_comm]

omit [DecidableEq F] in
theorem 𝒲.bind_sum_apply {f : 𝒲 𝒮 H[F]} {g : ℕ → H[F] → 𝒲 𝒮 H[F]} :
    (f ≫= fun i ↦ ⨁' (x : ℕ), g x i) = (⨁' (x : ℕ), (f ≫= g x)) := by
  simp [bind]
  magic_simp
  simp [← WeightedSum_mul_left]
  apply Subtype.eq_iff.mpr
  ext h
  simp
  rw [WeightedSum_comm]
  congr

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

theorem Policy.iter_sem_isLfp (p : Policy[F,𝒮]) : IsLfp (Φ p) (wnk_policy {~p*}.sem) := by
  constructor
  · ext h h'
    simp [sem, Φ]
    suffices
          (p.sem h ≫= fun h ↦ ⨁' (n : ℕ), (p.iter n).sem h)
        = ⨁' (n : ℕ), (p.sem h ≫= fun h ↦ (p.iter n).sem h) by
      simp [this]; clear this
      rw [WeightedSum_nat_eq_succ]
      simp [Policy.sem, Predicate.sem, WeightedAdd.wAdd]
      congr
    ext
    simp [𝒲.bind]
    magic_simp
    simp [← WeightedSum_mul_left]
    rw [WeightedSum_comm]
  · intro f hf h
    simp [sem, Φ, 𝒲.bind, WeightedAdd.wAdd]
    apply WeightedSum_nat_le (𝒮:=𝒲 𝒮 H[F]) (f:=(fun n ↦ (p.iter n).sem h))
    intro n
    induction n generalizing h with
    | zero => simp
    | succ n ih =>
      rw [add_comm]
      simp [sem, Predicate.sem]
      rw [← hf]
      simp only [WeightedAdd.wAdd, Φ]
      apply wAdd_mono_left
      simp [add_comm]
      simp [sem]
      calc
        ⨁ᶠ i ∈ Finset.range n, (p.sem h ≫= (p.iter i).sem)
          = (p.sem h ≫= ⨁ᶠ i ∈ Finset.range n, (p.iter i).sem) := by
          simp [𝒲.bind]
          magic_simp
          ext h'
          simp only
          simp
          magic_simp
          simp [← WeightedFinsum_mul_left]
          rw [WeightedSum_WeightedFinset_comm]
        _ ≼ (p.sem h ≫= f) := by
          apply 𝒲.bind_mono
          intro h₁
          convert ih h₁
          simp [WeightedPreSemiring.instPi]

theorem Policy.iter_sem_eq_lfp (p : Policy[F,𝒮]) : wnk_policy {~p*}.sem = Φ_wSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_wSup_isLfp

example {p : Policy[F,𝒮]} : wnk_policy {~p*}.sem = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  have := Policy.iter_sem_isLfp p |>.left
  rw [← this]
  ext
  unfold Φ
  simp [WeightedAdd.wAdd, Policy.sem, Predicate.sem]

@[simp]
instance : Zero Policy[F,𝒮] where
  zero := wnk_policy {drop}
@[simp]
instance : HAdd Policy[F,𝒮] Policy[F,𝒮] Policy[F,𝒮] where
  hAdd p q := p.Add q
@[simp]
instance : Add Policy[F,𝒮] where
  add p q := p.Add q

open WeightedOmegaCompletePartialOrder in
noncomputable def Policy.approx_n (p : Policy[F,𝒮]) (n : ℕ) : Policy[F,𝒮] := match p with
  | .Filter t => .Filter t
  | wnk_policy {~f ← ~n} => wnk_policy {~f ← ~n}
  | wnk_policy {dup} => wnk_policy {dup}
  -- TODO: this should use the syntax
  | .Seq p q => (p.approx_n n).Seq (q.approx_n n)
  -- TODO: this should use the syntax
  | .Weight w p => .Weight w (p.approx_n n)
  -- TODO: this should use the syntax
  | .Add p q => .Add (p.approx_n n) (q.approx_n n)
  -- TODO: this should use the syntax
  | .Iter p => List.range n |>.map ((p.approx_n n) ^ ·) |>.sum

open WeightedOmegaCompletePartialOrder in
noncomputable def Policy.sem_n (p : Policy[F,𝒮]) (n : ℕ) : H[F] → 𝒲 𝒮 H[F] := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π[f ↦ n]::h)
  | wnk_policy {dup} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π::π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem_n n h ≫= q.sem_n n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ ⟨fun h' ↦ w ⨀ p.sem_n n h h', SetCoe.countable (W.supp (w ⨀ p.sem_n n h ·))⟩
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem_n n h ⨁ q.sem_n n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁ᶠ i ∈ Finset.range n, (p ^ i).sem_n n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

theorem List.succ_range_map {α : Type} (f : ℕ → α) {n : Nat} :
    (range (n + 1)).map f = (range n).map f ++ [f n] := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp_all
    simp [List.getElem_append]
    simp_all
    intro h
    congr
    omega

attribute [local simp] Policy.approx_n Policy.sem Policy.sem_n Predicate.sem in
theorem Policy.approx_n_sem (p : Policy[F,𝒮]) (n : ℕ) : (p.approx_n n).sem = p.sem_n n := by
  induction p with simp_all
  | Iter p ih =>
    funext h
    suffices ∀ m (ih' : (p.approx_n m).sem = p.sem_n m),
          ((List.range n).map (p.approx_n m).iter).sum.sem h
        = ⨁ᶠ i ∈ Finset.range n, (p.iter i).sem_n m h by
      exact this n ih
    clear ih
    intro m ih
    induction n with
    | zero => unfold sem; rfl
    | succ n ihn =>
      simp_all
      rw [List.succ_range_map]
      rw [← ihn]; clear ihn
      generalize (List.range n).map (p.approx_n m).iter = l
      induction l with
      | nil =>
        simp [HAdd.hAdd, WeightedPreSemiring.wAdd_comm]
        congr
        induction n generalizing h with
        | zero => simp
        | succ n ih =>
          simp_all
          congr
          funext h'
          apply ih h'
      | cons q l ih' =>
        simp [HAdd.hAdd, WeightedPreSemiring.wAdd_comm]
        rw [ih']; clear ih'
        simp [← WeightedPreSemiring.wAdd_assoc]
        rw [WeightedPreSemiring.wAdd_comm]
        simp [← WeightedPreSemiring.wAdd_assoc]

omit [DecidableEq F] in
@[simp] theorem η_apply {x y : H[F]} : η x y = if x = y then (𝟙 : 𝒮) else 𝟘 := by rfl
omit [DecidableEq F] in
@[simp] theorem η_subtype_apply {x y : H[F]} : (η x).val y = if x = y then (𝟙 : 𝒮) else 𝟘 := by rfl

theorem Policy.sem_n_mono (p : Policy[F,𝒮]) : WeightedMonotone p.sem_n := by
  induction p with
  | Filter => intro; simp [sem_n]
  | Mod => intro; simp [sem_n]
  | Dup => intro; simp [sem_n]
  | Seq p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp only [sem_n]
    exact wle_trans (𝒲.bind_mono_right (p₁.sem_n n₁ h) (ih₂ h₁₂)) (𝒲.bind_mono_left _ (ih₁ h₁₂ h))
  | Weight w p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply fun h' ↦ wMul_mono_left _ (ih h₁₂ h h')
  | Add p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    gcongr
    · exact ih₁ h₁₂ h
    · exact ih₂ h₁₂ h
  | Iter p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply wle_trans (WeightedFinsum_le_of_subset (GCongr.finset_range_subset_of_le h₁₂))
    apply WeightedFinsum_mono
    intro i
    simp
    induction i generalizing h with
    | zero => simp [sem_n]
    | succ i ih' =>
      simp_all [sem_n]
      apply wle_trans (𝒲.bind_mono_left ((p.iter i).sem_n n₁) (ih h₁₂ h)) (𝒲.bind_mono_right _ ih')

@[simp]
theorem 𝒲.apply_subtype {α β : Type} [WeightedOmegaCompletePartialOrder α] [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α] (m : 𝒲 α β) (x : β) : m.val x = m x := by
  rfl

@[simp]
theorem wSup_const {α : Type} [WeightedOmegaCompletePartialOrder α] (x : α) :
    wSup ⟨fun _ ↦ x, by intro; simp⟩ = x := by
  apply wle_antisymm
  · apply wSup_le; magic_simp [implies_true]
  · apply le_wSup_of_le 0; magic_simp

@[simp]
theorem wSup_of_const {α : Type} [WeightedOmegaCompletePartialOrder α] (C : WeightedChain α)
    (h : ∀ n, C n = C 0) : wSup C = C 0 := by
  apply wle_antisymm
  · apply wSup_le; magic_simp [implies_true]; simp_all
  · apply le_wSup_of_le 0; magic_simp

omit [Fintype F] [DecidableEq F] in
theorem 𝒲.bind_apply (f : 𝒲 𝒮 H[F]) (g : H[F] → 𝒲 𝒮 H[F]) (x : H[F]) :
    (f ≫= g) x = ⨁' (i : f.supp), f i ⨀ g i x := by
  simp [bind]
  magic_simp

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.iter_m_sem_eq_wSup_sem_n {p : Policy[F,𝒮]} (h : p.sem = wSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
    (p.iter m).sem = wSup ⟨fun n ↦ (p.iter m).sem_n n, (p.iter m).sem_n_mono⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp
    funext h₀
    simp_all; clear h ih
    simp [WeightedOmegaCompletePartialOrder.instPi]
    magic_simp
    have := @𝒲.bind_continuous (f:=wSup ⟨(p.sem_n · h₀), (p.sem_n_mono · h₀)⟩) _ _ _ _
    simp [WeightedOmegaContinuous] at this
    specialize this ⟨(p.iter m).sem_n, (p.iter m).sem_n_mono⟩
    simp [WeightedChain.map, WeightedOmegaCompletePartialOrder.instPi] at this
    simp [DFunLike.coe] at this
    simp [this]; clear this
    have : ∀ n,
          (wSup ⟨(p.sem_n · h₀), (p.sem_n_mono · h₀)⟩ ≫= (p.iter m).sem_n n)
        = (wSup ⟨fun x ↦ p.sem_n x h₀ ≫= (p.iter m).sem_n n, by
        intro a b hab; apply 𝒲.bind_mono_left _ <| p.sem_n_mono hab h₀⟩) := by
      intro n
      have := @𝒲.bind_continuous' (g:=(p.iter m).sem_n n) _ _ _
      simp [WeightedOmegaContinuous] at this
      rw [this]; clear this
      magic_simp [WeightedChain.map]
    simp [this]
    rw [wSup_wSup]
    intro a b hab n
    simp
    apply 𝒲.bind_mono_right
    apply Policy.sem_n_mono _ hab

-- NOTE: This is lemma 36, but above we show a variant of this so this might not be needed
-- attribute [local simp] Policy.sem Policy.sem_n in
-- theorem Policy.iter_m_sem_eq_wSup_sem_n' {p : Policy[F,𝒮]} (h : p.sem = wSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
--     (p.iter m).sem = wSup ⟨fun n ↦ (p.approx_n n)^m |>.sem, ⋯⟩ := ⋯

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.sem_n_approx (p : Policy[F,𝒮]) : p.sem = wSup ⟨p.sem_n, sem_n_mono p⟩ := by
  induction p with
  | Filter t =>
    ext h h'
    simp_all [WeightedOmegaCompletePartialOrder.instPi, WeightedOmegaCompletePartialOrder.instCountablePi]
    magic_simp
    simp
  | Mod f i => rw [wSup_of_const] <;> (magic_simp; simp)
  | Dup => rw [wSup_of_const] <;> (magic_simp; simp)
  | Seq p₁ p₂ ih₁ ih₂ =>
    funext h
    simp only [sem, ih₁, WeightedOmegaCompletePartialOrder.instPi, ih₂]
    magic_simp
    simp only [sem_n]
    have := @𝒲.bind_continuous (f:=wSup ⟨fun x ↦ p₁.sem_n x h, (p₁.sem_n_mono · h)⟩) _ _ _ _
    simp [WeightedOmegaContinuous] at this
    specialize this ⟨fun x_1 x ↦ p₂.sem_n x_1 x, p₂.sem_n_mono⟩
    simp only [WeightedOmegaCompletePartialOrder.instPi, DFunLike.coe] at this
    simp [this]; clear this
    magic_simp [WeightedChain.map]
    have : ∀ n,
          (wSup ⟨fun x ↦ p₁.sem_n x h, (p₁.sem_n_mono · h)⟩ ≫= (fun x ↦ p₂.sem_n n x))
        = wSup ⟨fun x ↦ p₁.sem_n x h ≫= fun x ↦ p₂.sem_n n x, by
            intro a b hab; apply 𝒲.bind_mono_left _ <| p₁.sem_n_mono hab h⟩ := by
      intro n
      have := @𝒲.bind_continuous' (g:=p₂.sem_n n) _ _ _
      simp [WeightedOmegaContinuous] at this
      rw [this]; clear this
      magic_simp [WeightedChain.map]
    simp [this]
    rw [wSup_wSup]
    intro a b hab i
    apply 𝒲.bind_mono_right _ fun h ↦ p₂.sem_n_mono hab _
  | Weight w p ih =>
    ext h h'
    simp
    magic_simp
    rw [ih]
    simp [WeightedOmegaCompletePartialOrder.instPi, WeightedOmegaCompletePartialOrder.instCountablePi]
    magic_simp
    simp
    rw [WeightedOmegaContinuousMulRight]
    congr
  | Add p₁ p₂ ih₁ ih₂ =>
    funext h
    simp only [sem, ih₁, ih₂]
    simp only [WeightedOmegaCompletePartialOrder.instPi, WeightedOmegaContinuousAddRight,
      WeightedOmegaContinuousAddLeft]
    magic_simp
    rw [wSup_wSup]
    · simp
    · intro s₁ s₂ h₁₂ n
      apply wAdd_mono_left _ (sem_n_mono p₂ h₁₂)
    · intro s₁ s₂ h₁₂ n
      apply wAdd_mono_right _ (sem_n_mono p₁ h₁₂)
  | Iter p ih =>
    funext h
    simp only [sem, Policy.instHPow, iter_m_sem_eq_wSup_sem_n ih]; clear ih
    simp only [sem, Policy.instHPow, WeightedOmegaCompletePartialOrder.instPi]
    magic_simp
    apply wle_antisymm
    · apply WeightedSum_nat_le _ fun n ↦ ?_
      have := WeightedFinsum_cont (S:=Finset.range n)
          ⟨fun n m ↦ (p.iter m).sem_n n h, fun hab m ↦ (p.iter m).sem_n_mono hab h⟩
      simp only [WeightedOmegaCompletePartialOrder.instPi, DFunLike.coe] at this
      simp only [this, sem_n, Policy.instHPow]; clear this
      magic_simp [WeightedChain.map]
      apply wSup_le fun m ↦ ?_
      apply le_wSup_of_le (max n m)
      magic_simp
      apply wle_trans (WeightedFinsum_le_of_subset (S₂:=Finset.range (max n m)) (by simp))
      apply WeightedFinsum_mono
      intro i
      apply fun _ ↦ sem_n_mono _ (by simp)
    · apply wSup_le fun n ↦ ?_
      apply WeightedSum_le_nat _ n
      magic_simp [sem_n, Policy.instHPow]
      apply WeightedFinsum_mono
      intro i
      apply le_wSup_of_le n
      magic_simp

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.sem_n_lowerBounds (p : Policy[F,𝒮]) (n : ℕ) : p.sem_n n ≼ p.sem := by
  rw [sem_n_approx]
  apply le_wSup_of_le n
  magic_simp
