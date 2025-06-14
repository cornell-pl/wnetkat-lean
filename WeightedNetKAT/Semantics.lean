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

section

variable {α : Type}

variable [WeightedSemiring α] [WeightedOmegaContinuousPreSemiring α]

open WeightedPartialOrder WeightedOmegaCompletePartialOrder WeightedOmegaContinuousPreSemiring

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_eq_finset_sum {I : Type} [DecidableEq I] (S : Finset I) (f : I → α) :
    letI := WeightedSemiring.toSemiring
    ⨁ᶠ x ∈ S, f x = ∑ x ∈ S, f x := by
  letI := WeightedSemiring.toSemiring
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
theorem WeightedFinsum_bij {ι γ : Type} [DecidableEq ι] [DecidableEq γ]
    {Sι : Finset ι} {Sγ : Finset γ} {fι : ι → α} {fγ : γ → α}
    (i : ∀ a ∈ Sι, γ) (hi : ∀ a ha, i a ha ∈ Sγ)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ Sγ, ∃ a ha, i a ha = b) (h : ∀ a ha, fι a = fγ (i a ha))
    :
    ⨁ᶠ a ∈ Sι, fι a = ⨁ᶠ b ∈ Sγ, fγ b := by
  simp [WeightedFinsum_eq_finset_sum]
  letI : Semiring α := WeightedSemiring.toSemiring α
  apply Finset.sum_bij i <;> assumption

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_bij_ne_zero {ι γ : Type} [DecidableEq ι] [DecidableEq γ]
    {Sι : Finset ι} {Sγ : Finset γ} {fι : ι → α} {fγ : γ → α}
    (i : ∀ a ∈ Sι, fι a ≠ 𝟘 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ Sγ)
    (i_inj : ∀ a₁ ha₁₁ ha₁₂ a₂ ha₂₁ ha₂₂, i a₁ ha₁₁ ha₁₂ = i a₂ ha₂₁ ha₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ Sγ, fγ b ≠ 𝟘 → ∃ a h₁ h₂, i a h₁ h₂ = b) (h : ∀ a h₁ h₂, fι a = fγ (i a h₁ h₂))
    :
    ⨁ᶠ a ∈ Sι, fι a = ⨁ᶠ b ∈ Sγ, fγ b := by
  simp [WeightedFinsum_eq_finset_sum]
  letI : Semiring α := WeightedSemiring.toSemiring α
  apply Finset.sum_bij_ne_zero i <;> assumption

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_single {I : Type} [DecidableEq I] {S : Finset I} {f : I → α} (x : I)
    (h₀ : ∀ y ∈ S, y ≠ x → f y = 𝟘)
    (h₁ : x ∉ S → f x = 𝟘) :
    ⨁ᶠ i ∈ S, f i = f x := by
  simp [WeightedFinsum_eq_finset_sum]
  letI : Semiring α := WeightedSemiring.toSemiring α
  rw [Finset.sum_eq_single x h₀ h₁]

omit [WeightedOmegaContinuousPreSemiring α] in
theorem WeightedFinsum_union {I : Type} [DecidableEq I] {S₁ S₂ : Finset I} {f : I → α}
    (h : Disjoint S₁ S₂) : ⨁ᶠ i ∈ (S₁ ∪ S₂), f i = (⨁ᶠ i ∈ S₁, f i) ⨁ ⨁ᶠ i ∈ S₂, f i := by
  simp [WeightedFinsum_eq_finset_sum]
  letI : Semiring α := WeightedSemiring.toSemiring α
  rw [Finset.sum_union h]
  rfl

theorem WeightedFinsum_le_of_subset {I : Type} [DecidableEq I] {S₁ S₂ : Finset I} {f : I → α}
    (h : S₁ ⊆ S₂) : ⨁ᶠ i ∈ S₁, f i ≼ ⨁ᶠ i ∈ S₂, f i := by
  set S₃ := S₂ \  S₁
  have : S₂ = S₁ ∪ S₃ := by simp [S₃, h]
  simp_all
  rw [WeightedFinsum_union]
  · exact wle_wAdd (⨁ᶠ i ∈ S₁, f i) (⨁ᶠ i ∈ S₃, f i)
  · simp [S₃]; exact Finset.disjoint_sdiff

def List.max {α : Type} [Max α] (l : List α) (h : ¬l = []) : α :=
  match l with
  | x::[] => x
  | x::y::rest => x ⊔ (y::rest).max (by simp)

theorem List.le_max_cons_iff {α : Type} [LinearOrder α] (x y : α) (l : List α) :
    x ≤ (y :: l).max (by simp) ↔ x ≤ y ∨ (∃ h : _, x ≤ l.max h) := by
  rcases l <;> simp_all [max]

@[simp]
theorem List.le_max_cons {α : Type} [LinearOrder α] (x : α) (l : List α) :
    x ≤ (x :: l).max (by simp) := by
  simp [le_max_cons_iff]

@[simp]
theorem List.le_max_of_mem {α : Type} [LinearOrder α] (x : α) (l : List α) (h : x ∈ l) :
    x ≤ l.max (ne_nil_of_mem h) := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp_all [le_max_cons_iff]
    rcases h with h | h
    · simp
    · have hxl : x ∈ l := by assumption
      right
      use (ne_nil_of_mem hxl)
      apply ih hxl

theorem List.subset_finset_range_max (l : List ℕ) (h : ¬l = []) :
    l.toFinset ⊆ Finset.range (l.max h + 1) := by
  induction l, h using List.max.induct with
  | case1 => simp_all [max]
  | case2 x y rest h ih =>
    intro z hz
    simp_all
    refine Nat.lt_add_one_iff.mpr ?_
    simp_all [le_max_cons_iff]

theorem wSup_WeightedSum_chain_wle {I : Type} (e₀ e₁ : Encodable I) (f : I → α) :
    wSup (@WeightedSum_chain _ _ _ _ e₀ f) ≼ wSup (@WeightedSum_chain _ _ _ _ e₁ f) := by
  apply wSup_le _ _ fun i ↦ ?_
  magic_simp [WeightedSum_chain]
  let actual := (List.range (i )).filterMap (e₀.decode₂ _) |>.map e₁.encode
  have : actual.Nodup := by
    refine (List.nodup_map_iff_inj_on (List.Nodup.filterMap ?_ List.nodup_range)).mpr (by simp)
    simp_all [Encodable.decode₂_eq_some]
  rw [← WeightedFinsum_bij_ne_zero (Sι:=actual.toFinset) (fι:=(match e₁.decode₂ _ · with | some x => f x | none => 𝟘))]
  · if h_empty : actual = [] then simp_all else
    apply le_wSup_of_le (actual.max (by assumption) + 1)
    magic_simp
    have : actual.toFinset ⊆ Finset.range (actual.max (by assumption) + 1) := by
      apply List.subset_finset_range_max actual
    have := WeightedFinsum_le_of_subset this (f:=(match e₁.decode₂ _ · with | some x => f x | none => 𝟘))
    apply wle_trans this
    apply WeightedFinsum_mono
    intro i
    simp
    split <;> split <;> simp_all
  · exact fun x hx _ ↦ (e₁.decode₂ _ x).get (by
      simp_all [actual]
      refine Option.isSome_iff_exists.mpr ?_
      simp_all [Encodable.decode₂_eq_some]
      obtain ⟨q, hx, hx'⟩ := hx
      use q
    ) |> e₀.encode
  · simp_all [actual, Encodable.decode₂_eq_some]
    intro x hx
    intro ⟨h₁, h₂⟩
    subst_eqs
    simp_all
  · simp_all [actual, Encodable.decode₂_eq_some]
    rintro a₁ x₁ ⟨h₁, _, _⟩ q₁ a₂ x₂ ⟨h₂, _, _⟩ q₂ h
    simp_all
  · simp_all [actual, Encodable.decode₂_eq_some]
    intro b hbi
    split
    · rename_i x' x hx
      intro h₂
      simp_all [Encodable.decode₂_eq_some]; subst_eqs
      simp_all
      use e₁.encode x
      simp_all
    · simp
  · simp_all [actual, Encodable.decode₂_eq_some]

theorem WeightedSum_with_encoding {I : Type} (e₀ e₁ : Encodable I) (f : I → α) :
    @WeightedSum I α _ _ e₀ f = @WeightedSum I α _ _ e₁ f :=
  wle_antisymm (wSup_WeightedSum_chain_wle e₀ e₁ f) (wSup_WeightedSum_chain_wle e₁ e₀ f)

def Encodable.ofList {I : Type} [DecidableEq I] (S : List I) (hS : S.Nodup) :
    Encodable {x // x ∈ S} := {
  encode := fun ⟨s, hs⟩ ↦ S.findIdx? (· = s) |>.get (by simp [hs])
  decode n := if _ : n < S.length then some ⟨S[n], by simp⟩ else none
  encodek := by
    simp only [Option.dite_none_right_eq_some, Option.some.injEq, Subtype.forall,
      Subtype.mk.injEq]
    intro s hs
    obtain ⟨i, hi, _, _⟩ := List.mem_iff_getElem.mp hs
    suffices List.findIdx? (fun x ↦ decide (x = S[i])) S = some i by simp_all
    refine List.findIdx?_eq_some_iff_getElem.mpr ?_
    simp_all
    intro j hj q
    have h₁ := List.nodup_iff_injective_getElem.mp hS
    have : (⟨j, by omega⟩: Fin S.length) ≠ ⟨i, by omega⟩ := by simp; omega
    have := h₁.ne this
    contradiction
}

theorem wSup_skip {C : WeightedChain α} (n : ℕ) :
    wSup C = wSup ⟨fun i ↦ C (i + n), fun hab ↦ by simp; apply C.prop; simp_all⟩ := by
  apply wle_antisymm
  · apply wSup_le _ _ fun i ↦ ?_
    apply le_wSup_of_le i
    magic_simp
    apply C.prop
    simp
  · apply wSup_le _ _ fun i ↦ ?_
    apply le_wSup_of_le (i + n)
    magic_simp

theorem wSup_skip' {C : WeightedChain α} (n : ℕ) :
    wSup C = wSup ⟨fun i ↦ C (n + i), fun hab ↦ by simp; apply C.prop; simp_all⟩ := by
  rw [wSup_skip n]
  simp [add_comm]

attribute [local simp] Encodable.decode₂_eq_some in
theorem WeightedSum_list {I : Type} [DecidableEq I] [e₀ : Encodable I] (S : List I) (hS : S.Nodup) (f : I → α) :
    ⨁' x : {x // x ∈ S}, f x = ⨁ᶠ x ∈ S.toFinset, f x := by
  rw [WeightedSum_with_encoding _ (Encodable.ofList S hS)]
  simp_all [WeightedSum, WeightedSum_chain]
  apply wle_antisymm
  · apply wSup_le _ _ fun i ↦ ?_
    magic_simp
    let S' := Finset.range i |>.filterMap ((Encodable.ofList S hS).decode₂ _) (by simp_all [Encodable.decode₂_eq_some]) |>.image Subtype.val
    have : S' ⊆ S.toFinset := by intro; simp_all [S']
    apply wle_trans _ (WeightedFinsum_le_of_subset this)
    apply wle_of_eq
    symm
    apply WeightedFinsum_bij_ne_zero (fun x h₁ h₂ ↦ (Encodable.ofList S hS).encode ⟨x, List.mem_dedup.mp (this h₁)⟩)
    · simp_all only [Finset.mem_image, Finset.mem_filterMap, Finset.mem_range,
      Encodable.decode₂_eq_some, exists_eq_right', Subtype.exists, exists_and_right,
      exists_eq_right, ne_eq, forall_exists_index, implies_true, S']
    · simp_all only [Finset.mem_image, Finset.mem_filterMap, Finset.mem_range,
      Encodable.decode₂_eq_some, exists_eq_right', Subtype.exists, exists_and_right,
      exists_eq_right, ne_eq, Encodable.encode_inj, Subtype.mk.injEq, implies_true, S']
    · simp_all
      intro b hb; split
      · simp_all; subst_eqs; simp_all
        intro h
        rename_i x
        obtain ⟨x, hx⟩ := x
        use x
        simp_all [S']
      · simp
    · simp
  · let actual := S.attach.map (Encodable.ofList S hS).encode
    if h_nonempty : actual = [] then simp_all [actual] else
    apply le_wSup_of_le (actual.max (by assumption) + 1)
    magic_simp
    let S' := Finset.range (actual.max h_nonempty + 1) |>.filter ((Encodable.ofList S hS).decode₂ _ · |>.isSome)
    rw [WeightedFinsum_bij_ne_zero (Sι:=Finset.range (actual.max h_nonempty + 1)) (Sγ:=S')
        (fγ:=(fun x ↦ match (Encodable.ofList S hS).decode₂ _ x with | some x => f x | none => 𝟘))
        (fun q h₁ h₂ ↦ q)]
    · apply wle_of_eq
      apply WeightedFinsum_bij_ne_zero (fun x h₁ h₂ ↦ (Encodable.ofList S hS).encode ⟨x, List.mem_dedup.mp h₁⟩)
      · simp_all [S', actual]
        intro a ha ha0
        refine Nat.lt_add_one_of_le ?_
        apply List.le_max_of_mem
        simp
      · simp
      · intro b hb
        split
        · simp_all; subst_eqs; simp
        · simp
      · simp
    · simp_all;
      intro a ha
      split
      · simp_all; subst_eqs; simp_all [actual]
        simp_all [S', actual]
      · simp_all
    · simp_all
    · simp_all
      intro b hb
      split
      · simp_all; subst_eqs
        simp_all
        intro _
        refine Nat.lt_add_one_of_le ?_
        apply List.le_max_of_mem
        simp [actual]
      · simp_all
    · simp_all
      intro a ha
      split
      · simp_all; subst_eqs
        simp
      · simp

theorem WeightedSum_finset {I : Type} [DecidableEq I] [Encodable I] (S : Finset I) (f : I → α) :
    ⨁' x : S, f x = ⨁ᶠ x ∈ S, f x := by
  have : S.toList.toFinset = S := by simp
  rw [← this]
  rw [← WeightedSum_list _ (Finset.nodup_toList S)]
  have : {x // x ∈ S.toList.toFinset} = {x // x ∈ S} := by simp
  congr! 1
  · simp
  · congr!
    simp_all
    ext
    simp
  · simp_all
    refine Function.hfunext ?_ ?_
    · simp
    · simp_all [Subtype.heq_iff_coe_eq]

attribute [local simp] Encodable.decode₂_eq_some in
theorem WeightedSum_finite {I : Type} [DecidableEq I] [e : Encodable I] [hfin : Finite I] (f : I → α) :
    ⨁' x : I, f x = ⨁ᶠ x ∈ Set.finite_univ.toFinset, f x := by
  rw [← WeightedSum_finset]
  have : ⨁' (x : { x // x ∈ Set.finite_univ.toFinset }), f x.val = ⨁' (x : { x : I // True }), f x.val := by
    congr
    · simp
    · simp
    · refine Function.hfunext rfl ?_
      · intro a
        simp_all [Subtype.heq_iff_coe_eq]
        refine Subsingleton.helim ?_ _ _
        simp
    · refine Function.hfunext ?_ ?_
      · simp_all [Subtype.heq_iff_coe_eq]
      · simp_all [Subtype.heq_iff_coe_eq]
  simp [this]
  let e' : Encodable { a : I // True } := {
    encode x := e.encode x
    decode n := (e.decode n).map (⟨·, by trivial⟩)
    encodek := by simp
  }
  rw [WeightedSum_with_encoding Subtype.encodable e']
  simp [WeightedSum]
  congr!
  ext i
  magic_simp [WeightedSum_chain]
  apply WeightedFinsum_bij (fun x _ ↦ x)
  · simp
  · simp
  · simp
  · simp_all
    intro a ha
    split <;> split
    · simp_all [e']; subst_eqs
      rename_i heq
      have := Encodable.encode_inj.mp heq
      simp_all
    · simp_all [e']
    · simp_all [e']
    · simp_all [e']

example : ⨁' _ : Fin 4, (𝟙 : α) = 𝟙 ⨁ 𝟙 ⨁ 𝟙 ⨁ 𝟙 := by
  rw [WeightedSum_finite]
  simp
  simp [WeightedFinsum]
  have : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := rfl
  simp_all [WeightedPreSemiring.wAdd_comm]

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

omit [Fintype F] [DecidableEq F] in
theorem 𝒲.wAdd_bind {a : 𝒲 𝒮 X} {f} {g : X → 𝒲 𝒮 X}
    (hf : (⨁' (x : f.val.supp), f.val x.val) = 𝟙) : a ⨁ (f ≫= g) = (f ≫= (a ⨁ g ·)) := by
  simp [bind]
  ext h
  magic_simp
  simp only [WeightedAdd.wAdd, WeightedPreSemiring.left_distrib, WeightedSum_add,
    WeightedSum_mul_right, hf, WeightedSemiring.wOne_mul]

omit [Fintype F] [DecidableEq F] in
theorem 𝒲.wAdd_bind' {a : 𝒲 𝒮 H[F]} {f : 𝒲 𝒮 H[F]} {g : H[F] → 𝒲 𝒮 H[F]}
    (hf : ⨁' (x : f.val.supp), f.val x.val = 𝟙) : a.val ⨁ (f ≫= g).val = (f ≫= (a ⨁ g ·)).val := by
  ext h
  have := congrFun (congrArg Subtype.val (𝒲.wAdd_bind (a:=a) (f:=f) (g:=g) hf)) h
  simpa [WeightedAdd.wAdd]

theorem WeightedSum_succ {f : ℕ → 𝒮} (h : f 0 = 𝟘) : ⨁' (n : ℕ), f (n + 1) = ⨁' (n : ℕ), f n := by
  apply wle_antisymm
  · apply wSup_le _ _ fun i ↦ le_wSup_of_le (i + 1) ?_
    induction i with
    | zero => simp [WeightedSum_chain, DFunLike.coe]
    | succ i ih =>
      sorry
      -- apply wAdd_gconr (by simp)
      -- apply wle_trans ih; clear ih
      -- simp only [DFunLike.coe, WeightedSum_chain, WeightedChain.val_apply, Nat.fold_succ, wle_refl]
  · apply wSup_le _ _ fun i ↦ ?_
    rcases i with _ | i
    · simp [WeightedSum_chain, DFunLike.coe]
    · apply le_wSup_of_le i ?_
      simp [DFunLike.coe, WeightedSum_chain]
      induction i with
      | zero =>
        simp [DFunLike.coe]
        sorry
        -- simp [DFunLike.coe, h]
      | succ i ih =>
        sorry
        -- simp only [DFunLike.coe, Nat.fold_succ]
        -- apply wAdd_gconr (by simp)
        -- apply wle_trans ih; clear ih
        -- simp only [DFunLike.coe, Nat.fold_succ, wle_refl]

theorem Policy.iter_k {h h'} (p : Policy[F,𝒮]) (hhh' : h ≠ h') :
    (wnk_policy {~p;~p*}.sem h).val h' = (wnk_policy {~p*}.sem h).val h' := by
  simp [sem]
  simp [𝒲.bind]
  sorry
  -- rw [← WeightedSum_succ]
  -- · simp [sem, 𝒲.bind]
  --   sorry
  -- · simp [sem, Predicate.sem]
  --   sorry

theorem Policy.iter_sem_isLfp (p : Policy[F,𝒮]) : IsLfp (Φ p) (wnk_policy {~p*}.sem) := by
  constructor
  · ext h h'
    if hhh' : h = h' then
      subst_eqs
      sorry
    else
      simp [← p.iter_k hhh']
      simp [sem, Φ]
      simp [WeightedAdd.wAdd]
      suffices (η h).val h' = (𝟘 : 𝒮) by simp [this]
      sorry
  · intro f hf
    rw [← hf]
    simp [Φ, sem]
    intro h h'
    simp
    rw [𝒲.wAdd_bind']
    · simp [𝒲.bind]
      apply wSup_le
      intro i
      simp only [DFunLike.coe, WeightedSum_chain]
      simp [WeightedAdd.wAdd]
      induction i with
      | zero => simp [WeightedChain.map, DFunLike.coe, WeightedZero.wZero]
      | succ i ih =>
        apply wle_trans _ ih; clear ih
        simp only [DFunLike.coe]
        simp
        sorry
    · sorry

theorem Policy.iter_sem_eq_lfp (p : Policy[F,𝒮]) : wnk_policy {~p*}.sem = Φ_wSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_wSup_isLfp
