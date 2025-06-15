import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax
import Mathlib.Logic.Equiv.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

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
def Policy.iter (p : Policy[F,𝒮]) : ℕ → Policy[F,𝒮]
  | 0 => wnk_policy { skip }
  | n+1 => wnk_policy {~p ; ~(p.iter n)}

@[simp, reducible] instance : HPow Policy[F,𝒮] ℕ Policy[F,𝒮] where hPow p n := p.iter n

@[simp]
def Policy.iterDepth : Policy[F,𝒮] → ℕ
| .Filter _ | wnk_policy {~_ ← ~_} | wnk_policy {dup} => 0
| wnk_policy {~p ⨁ ~q} | wnk_policy {~p ; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_policy {~_ ⨀ ~q} => q.iterDepth
| wnk_policy {~p *} => p.iterDepth + 1

omit [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype F] [DecidableEq F] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,𝒮]} {n : ℕ} :
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
  | .Weight w p => fun h ↦ w ⨀ p.sem h
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

variable [WeightedSemiring α] [WeightedOmegaContinuousPreSemiring α]

open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring

open WeightedOmegaCompletePartialOrder in
@[simp]
theorem wSup_apply {ι : Type} (C : WeightedChain (ι → 𝒮)) (a : ι) :
    wSup C a = wSup (C.map (· a) (· a)) := by
  simp [wSup]
  rfl

open WeightedOmegaCompletePartialOrder in
theorem WeightedFinsum_mono [DecidableEq X] (S : Finset X) : WeightedMonotone (fun (f : X → 𝒮) ↦ ⨁ᶠ i ∈ S, f i) := by
  intro f g hfg
  simp only
  induction S using Finset.induction with
  | empty => simp
  | insert x S hxS ih =>
    simp_all [WeightedFinsup_insert]
    gcongr
    exact hfg x
open WeightedOmegaCompletePartialOrder in
theorem WeightedSum_mono [Encodable X] : WeightedMonotone (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) := by
  intro f₁ f₂ h₁₂
  apply wSup_le _ _ fun i ↦ ?_
  apply le_wSup_of_le i
  magic_simp [WeightedSum_chain]
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [WeightedFinsup_range_succ]
    gcongr
    split
    · apply h₁₂
    · simp

open WeightedPartialOrder WeightedOmegaCompletePartialOrder in
theorem WeightedFinsum_cont [DecidableEq X] (S : Finset X) :
    WeightedOmegaContinuous (fun (f : X → 𝒮) ↦ ⨁ᶠ i ∈ S, f i) (WeightedFinsum_mono S) := by
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
    · refine wSup_le _ _ fun i ↦ wSup_le _ _ fun j ↦ ?_
      apply le_wSup_of_le (i ⊔ j)
      magic_simp
      simp only [WeightedChain.val_apply]
      gcongr
      · apply C.prop; simp
      · apply WeightedFinsum_mono; apply C.prop; simp
    · apply wSup_le _ _ fun i ↦ ?_
      magic_simp
      simp only [WeightedChain.val_apply]
      apply le_wSup_of_le i
      apply le_wSup_of_le i
      magic_simp

open WeightedPartialOrder WeightedOmegaCompletePartialOrder in
theorem WeightedSum_cont [Encodable X] :
    WeightedOmegaContinuous (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) WeightedSum_mono := by
  intro C
  apply wle_antisymm
  · simp [WeightedSum, WeightedSum_chain]
    apply wSup_le _ _ fun i ↦ ?_
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
  · exact wSup_le _ _ fun i ↦ WeightedSum_mono (le_wSup_of_le i (wle_refl _))

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

omit [WeightedSemiring α] [WeightedOmegaContinuousPreSemiring α] in
theorem Finset.fold_list_toFinset {I : Type} [DecidableEq I] (S : List I) (hS : S.Nodup) (op : α → α → α) [Std.Commutative op] [Std.Associative op] (init : α) (f : I → α) :
    S.toFinset.fold op init f = S.foldr (fun a b ↦ op (f a) b) init := by
  induction S with
  | nil => simp
  | cons x S ih => simp_all

omit [WeightedOmegaContinuousPreSemiring α] in
@[simp]
theorem WeightedFinsup_union_singleton {I : Type} [DecidableEq I] (S : Finset I) (x : I) (h : x ∉ S) (f : I → α) :
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

theorem WeightedFinsum_le_of_subset {α I : Type} [WeightedPreSemiring α]
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
  [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : α → 𝒮} {a : 𝒮} (h : ∀ S : Finset α, ⨁ᶠ x ∈ S, f x ≼ a) :
    ⨁' x : α, f x ≼ a := by
  apply wSup_le _ _ fun i ↦ ?_
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
  [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
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
    @WeightedSum I α _ _ e₀ f ≼ @WeightedSum I α _ _ e₁ f :=
  letI := e₀; WeightedSum_le_of_finset fun _ ↦ letI := e₁; WeightedSum_finset_le _

theorem WeightedSum_with_encoding {I : Type} [DecidableEq I] (e₀ e₁ : Encodable I) (f : I → α) :
    @WeightedSum I α _ _ e₀ f = @WeightedSum I α _ _ e₁ f :=
  wle_antisymm (WeightedSum_with_encoding_wle e₀ e₁ f) (WeightedSum_with_encoding_wle e₁ e₀ f)

theorem wSup_skip {α : Type} [WeightedPreSemiring α] [WeightedOmegaContinuousPreSemiring α]
    {C : WeightedChain α} (n : ℕ) :
    wSup C = wSup ⟨fun i ↦ C (i + n), fun hab ↦ by simp; apply C.prop; simp_all⟩ := by
  apply wle_antisymm
  · apply wSup_le _ _ fun i ↦ le_wSup_of_le i ?_
    exact C.prop (by simp)
  · exact wSup_le _ _ fun i ↦ le_wSup_of_le (i + n) (by magic_simp)

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

example : ⨁' _ : Fin 4, (𝟙 : α) = 𝟙 ⨁ 𝟙 ⨁ 𝟙 ⨁ 𝟙 := by
  have : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := rfl
  simp_all [WeightedSum_finite, WeightedPreSemiring.wAdd_comm]

end

omit [Fintype F] [DecidableEq F] in
open WeightedOmegaContinuousPreSemiring in
theorem 𝒲.bind_mono (f : 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=H[F] → 𝒲 𝒮 H[F]) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
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
    refine wSup_le (Φ_chain p) x fun i ↦ ?_
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
  [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
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
  [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    (f : α → ι → 𝒮) :
    ⨁' (x : α) (i : ι), f x i = ⨁' (i : ι) (x : α), f x i :=
  wle_antisymm (WeightedSum_comm_le _) (WeightedSum_comm_le _)

omit [Fintype F] [DecidableEq F] in
theorem WeightedSum_WeightedFinset_comm {α ι 𝒮 : Type} [Encodable α] [DecidableEq α] [Encodable ι] [DecidableEq ι]
  [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
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

theorem WeightedSum_nat_le (𝒮 : Type) [WeightedPreSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
    {f : ℕ → 𝒮} (a : 𝒮) (h : ∀ n, ⨁ᶠ x ∈ Finset.range n, f x ≼ a) :
    ⨁' (x : ℕ), f x ≼ a := by
  apply WeightedSum_le_of_finset
  intro S
  if hS : ¬S.Nonempty then simp_all else
  apply Decidable.not_not.mp at hS
  apply wle_trans (WeightedFinsum_le_of_subset ?_) (h (S.max' hS + 1))
  exact fun x hx ↦ Finset.mem_range.mpr <| Nat.lt_add_one_of_le <| Finset.le_max' _ _ hx
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
    apply wSup_le _ _ fun i ↦ ?_
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
    apply WeightedSum_nat_le
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
