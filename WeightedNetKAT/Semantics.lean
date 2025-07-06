import WeightedNetKAT.Countsupp
import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax

open OmegaCompletePartialOrder

@[simp]
theorem OmegaCompletePartialOrder.ωSup_const {α : Type} [OmegaCompletePartialOrder α] (x : α) :
    ωSup ⟨fun _ ↦ x, by intro; simp⟩ = x := by
  apply le_antisymm
  · apply ωSup_le _ _ fun i ↦ ?_; rfl
  · apply le_ωSup_of_le 0; rfl

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

namespace WeightedNetKAT

abbrev η {ι : Type} {α : Type} [DecidableEq ι] [Zero α] [One α] (i : ι): ι →c α :=
  ⟨Pi.single i 1, Set.Countable.mono Pi.support_single_subset (Set.countable_singleton i)⟩

@[simp] theorem η_apply {ι : Type} {α : Type} [DecidableEq ι] [Zero α] [One α] {x y : ι} :
    η x y = if x = y then (1 : α) else 0 := by
  simp [η, DFunLike.coe, Pi.single, Function.update]; grind

-- @[simp] theorem η_subtype_apply {x y : H[F,N]} : η x y = if x = y then (1 : 𝒮) else 0 := by rfl

variable {X : Type} {𝒮 : Type}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [CanonicallyOrderedAdd 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [DecidableEq N]

noncomputable instance : DecidableEq (X →c 𝒮) := Classical.typeDecidableEq _
-- noncomputable instance : DecidableEq (H[F,N] →c 𝒮) := Classical.typeDecidableEq (𝒲 𝒮 H)

noncomputable def Pred.sem (p : Pred[F,N]) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | wnk_pred {false} => fun _ ↦ 0
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun (π, h) ↦ if π f = n then η (π, h) else 0
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.sem h).bind fun h ↦ η h + ((if t.sem h = 0 then η h else 0).bind u.sem)
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ (t.sem h).bind u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 0 then η h else 0

instance : Subst Pk[F,N] F N where
  subst pk f n := fun f' ↦ if f = f' then n else pk f'

@[simp]
def Policy.iter (p : Policy[F,N,X]) : ℕ → Policy[F,N,X]
  | 0 => wnk_policy { skip }
  | n+1 => wnk_policy {~p ; ~(p.iter n)}

@[simp, reducible] instance Policy.instHPow : HPow Policy[F,N,X] ℕ Policy[F,N,X] where hPow p n := p.iter n

@[simp]
def Policy.iterDepth : Policy[F,N,X] → ℕ
| .Filter _ | wnk_policy {~_ ← ~_} | wnk_policy {dup} => 0
| wnk_policy {~p ⨁ ~q} | wnk_policy {~p ; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_policy {~_ ⨀ ~q} => q.iterDepth
| wnk_policy {~p *} => p.iterDepth + 1

omit [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,N,X]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

open OmegaCompletePartialOrder in
noncomputable def Policy.sem (p : Policy[F,N,𝒮]) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η (π, π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem h).bind q.sem
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w * p.sem h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem h + q.sem h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ω∑ n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Pred[F,N]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Pred.sem]

noncomputable def Φ (p : Policy[F,N,𝒮]) (d : H[F,N] → H[F,N] →c 𝒮) : H[F,N] → H[F,N] →c 𝒮 :=
  fun h ↦ η h + (p.sem h).bind d

example {p : Policy[F,N,𝒮]} : Φ p (wnk_policy {~p*}.sem) = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  ext
  unfold Φ
  simp [Policy.sem, Pred.sem]

open OmegaCompletePartialOrder OmegaContinuousNonUnitalSemiring

omit [MulRightMono 𝒮] in
theorem Φ_mono (p : Policy[F,N,𝒮]) : Monotone (Φ p) := by
  intro a b hab h
  simp [Φ]
  gcongr
  exact Countsupp.bind_mono_right (p.sem h) _ _ hab
theorem Φ_continuous [OmegaContinuousNonUnitalSemiring 𝒮] (p : Policy[F,N,𝒮]) : ωScottContinuous (Φ p) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨Φ_mono p, ?_⟩
  intro C
  ext h
  unfold Φ
  simp [(p.sem h).bind_continuous_right.map_ωSup, ωSup_add_left _ |>.map_ωSup]
  congr! 1

omit [OrderBot 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.wZero_le (p : H[F,N] →c 𝒮) : 0 ≤ p := by intro; simp
omit [OrderBot 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.Pi_wZero_le {X : Type} (p : X → H[F,N] →c 𝒮) : 0 ≤ p := fun _ ↦ 𝒲.wZero_le _

noncomputable def Φ_chain (p : Policy[F,N,𝒮]) : Chain (H[F,N] → H[F,N] →c 𝒮) :=
  ⟨fun n ↦ (Φ p)^[n] 0, by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ c hac ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      apply le_trans ih; clear! a
      induction c with
      | zero => intro; simp
      | succ c ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        apply Φ_mono _ ih⟩
noncomputable def Φ_ωSup (p : Policy[F,N,𝒮]) := ωSup (Φ_chain p)

def IsLfp {α : Type} [OmegaCompletePartialOrder α]
    (f : α → α) (p : α) : Prop :=
  f p = p ∧ ∀ p', f p' = p' → p ≤ p'

theorem IsLfp_unique {α : Type} [OmegaCompletePartialOrder α] {f : α → α} {p₁ p₂ : α}
    (h₁ : IsLfp f p₁) (h₂ : IsLfp f p₂) : p₁ = p₂ :=
  le_antisymm (h₁.right _ h₂.left) (h₂.right _ h₁.left)

variable [OmegaContinuousNonUnitalSemiring 𝒮]

theorem Policy.Φ_ωSup_isLfp (p : Policy[F,N,𝒮]) : IsLfp (Φ p) (Φ_ωSup p) := by
  constructor
  · simp only [Φ_ωSup]
    apply le_antisymm
    · rw [Φ_continuous p |>.map_ωSup]
      apply ωSup_le _ _ fun i ↦ ?_
      apply le_ωSup_of_le (i + 1)
      simp only [DFunLike.coe, Chain.map, Φ_chain, OrderHom.mk_comp_mk, OrderHom.toFun_eq_coe,
        Function.comp_apply, Function.iterate_succ', le_refl]
    · apply ωSup_le
      intro i
      simp only [DFunLike.coe]
      rcases i with _ | i
      · simp [Φ_chain, DFunLike.coe]
      · simp only [Φ_chain, Function.iterate_succ', Function.comp_apply]
        apply Φ_mono _ (le_ωSup_of_le i (by simp [DFunLike.coe]))
  · intro x hx
    refine ωSup_le _ _ fun i ↦ ?_
    induction i with
    | zero => simp [Φ_chain, DFunLike.coe]
    | succ i ih =>
      simp only [DFunLike.coe, Φ_chain, Function.iterate_succ', Function.comp_apply]
      rw [← hx]
      apply Φ_mono p ih

theorem Policy.iter_sem_isLfp (p : Policy[F,N,𝒮]) : IsLfp (Φ p) (wnk_policy {~p*}.sem) := by
  constructor
  · ext h h'
    simp only [Φ, sem, instHPow, Countsupp.add_apply, η_apply, Countsupp.ωSum_apply]
    suffices
          ((p.sem h).bind fun h ↦ ω∑ (n : ℕ), (p.iter n).sem h)
        = ω∑ (n : ℕ), (p.sem h).bind fun h ↦ (p.iter n).sem h by
      simp [this]; clear this
      nth_rw 2 [ωSum_nat_eq_succ]
      simp [Policy.sem, Pred.sem]
    ext

    simp [Countsupp.bind]
    simp [DFunLike.coe]
    simp [← ωSum_mul_left]
    rw [ωSum_comm]
  · intro f hf h
    simp [sem, Φ]
    simp [ωSum_nat_eq_ωSup]
    intro n
    -- apply WeightedSum_nat_le (𝒮:=H[F,N] →c 𝒮) (f:=(fun n ↦ (p.iter n).sem h))
    -- intro n
    induction n generalizing h with
    | zero => simp [DFunLike.coe]
    | succ n ih =>
      rw [add_comm]
      simp [sem, Pred.sem, Finset.sum_range_add, DFunLike.coe]
      rw [← hf]
      simp only [Φ]
      gcongr
      simp [add_comm]
      simp [sem]
      calc
        ∑ i ∈ Finset.range n, (p.sem h).bind (p.iter i).sem
          = (p.sem h).bind (∑ i ∈ Finset.range n, (p.iter i).sem) := by
          simp [Countsupp.bind]
          ext h'
          simp [Finset.mul_sum]
          rw [ωSum_sum_comm]
        _ ≤ (p.sem h).bind f := by
          apply Countsupp.bind_mono_right
          intro h₁
          convert ih h₁
          simp [DFunLike.coe]

theorem Policy.iter_sem_eq_lfp (p : Policy[F,N,𝒮]) : wnk_policy {~p*}.sem = Φ_ωSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_ωSup_isLfp

example {p : Policy[F,N,𝒮]} : wnk_policy {~p*}.sem = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  have := Policy.iter_sem_isLfp p |>.left
  rw [← this]
  ext
  unfold Φ
  simp [Policy.sem, Pred.sem]

@[simp]
instance : Zero Policy[F,N,𝒮] where
  zero := wnk_policy {drop}
@[simp]
instance : HAdd Policy[F,N,𝒮] Policy[F,N,𝒮] Policy[F,N,𝒮] where
  hAdd p q := p.Add q
@[simp]
instance : Add Policy[F,N,𝒮] where
  add p q := p.Add q

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Policy.instAdd_sem (p q : Policy[F,N,𝒮]) : (p + q).sem = p.sem + q.sem := by
  ext; simp [sem]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Policy.instZero_sem : Policy.sem (F:=F) (N:=N) (𝒮:=𝒮) 0 = 0 := by
  unfold sem Pred.sem; rfl

open OmegaCompletePartialOrder in
noncomputable def Policy.approx_n (p : Policy[F,N,𝒮]) (n : ℕ) : Policy[F,N,𝒮] := match p with
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

open OmegaCompletePartialOrder in
noncomputable def Policy.sem_n (p : Policy[F,N,𝒮]) (n : ℕ) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η (π, π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem_n n h).bind (q.sem_n n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w * p.sem_n n h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem_n n h + q.sem_n n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ∑ i ∈ Finset.range n, (p ^ i).sem_n n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
attribute [local simp] Policy.approx_n Policy.sem Policy.sem_n Pred.sem in
theorem Policy.approx_n_sem (p : Policy[F,N,𝒮]) (n : ℕ) : (p.approx_n n).sem = p.sem_n n := by
  induction p with simp_all
  | Iter p ih =>
    funext h
    suffices ∀ m (ih' : (p.approx_n m).sem = p.sem_n m),
          ((List.range n).map (p.approx_n m).iter).sum.sem h
        = ∑ i ∈ Finset.range n, (p.iter i).sem_n m h by
      exact this n ih
    clear ih
    intro m ih
    induction n with
    | zero => unfold sem; rfl
    | succ n ihn =>
      simp_all [Finset.sum_range_add]
      rw [List.succ_range_map]
      rw [← ihn]; clear ihn
      generalize (List.range n).map (p.approx_n m).iter = l
      induction l with
      | nil =>
        simp
        induction n generalizing h with
        | zero => simp
        | succ n ih =>
          simp_all
          congr
          funext h'
          apply ih h'
      | cons q l ih' => ext; simp [ih', add_assoc]

omit [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem Policy.sem_n_mono (p : Policy[F,N,𝒮]) : Monotone p.sem_n := by
  induction p with
  | Filter => intro; simp [sem_n]
  | Mod => intro; simp [sem_n]
  | Dup => intro; simp [sem_n]
  | Seq p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp only [sem_n]
    exact le_trans (Countsupp.bind_mono_right (p₁.sem_n n₁ h) _ _ (ih₂ h₁₂)) (Countsupp.bind_mono_left _ (ih₁ h₁₂ h))
  | Weight w p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply fun h' ↦ mul_left_mono (ih h₁₂ h h')
  | Add p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    gcongr
    · exact ih₁ h₁₂ h
    · exact ih₂ h₁₂ h
  | Iter p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply le_trans (Finset.sum_mono_set_of_nonneg (by simp) (GCongr.finset_range_subset_of_le h₁₂))
    simp
    apply Finset.sum_le_sum fun i hi ↦ ?_
    induction i generalizing h with
    | zero => simp [sem_n]
    | succ i ih' =>
      simp [sem_n]
      simp at hi
      apply le_trans (Countsupp.bind_mono_left (𝒮:=𝒮) ((p.iter i).sem_n n₁) (ih h₁₂ h))
      apply Countsupp.bind_mono_right _ _ _
      exact fun h ↦ ih' h (by simp; omega)

attribute [local simp] Policy.sem Policy.sem_n Pred.sem in
theorem Policy.iter_m_sem_eq_ωSup_sem_n [Fintype N] {p : Policy[F,N,𝒮]} (h : p.sem = ωSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
    (p.iter m).sem = ωSup ⟨fun n ↦ (p.iter m).sem_n n, (p.iter m).sem_n_mono⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp
    funext h₀
    simp_all; clear h ih
    simp [Countsupp.bind_continuous_left _ |>.map_ωSup, Chain.map]
    unfold Function.comp
    simp
    simp [Countsupp.bind_continuous_right _ |>.map_ωSup]
    simp [Chain.map]
    unfold Function.comp
    simp
    rw [OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup']
    intro i j hij n
    apply Countsupp.bind_mono_left _ (p.sem_n_mono hij h₀)

-- NOTE: This is lemma 36, but above we show a variant of this so this might not be needed
-- attribute [local simp] Policy.sem Policy.sem_n in
-- theorem Policy.iter_m_sem_eq_ωSup_sem_n' {p : Policy[F,N,𝒮]} (h : p.sem = ωSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
--     (p.iter m).sem = ωSup ⟨fun n ↦ (p.approx_n n)^m |>.sem, ⋯⟩ := ⋯

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.sem_n_approx [Fintype N] (p : Policy[F,N,𝒮]) : p.sem = ωSup ⟨p.sem_n, sem_n_mono p⟩ := by
  induction p with
  | Filter t =>
    ext h h'
    simp_all [Chain.map]
    unfold Function.comp
    simp
  | Mod f i => funext; simp only [sem, asdsad, Chain.map, OrderHom.mk_comp_mk]; unfold Function.comp; simp
  | Dup => funext; simp only [sem, asdsad, Chain.map, OrderHom.mk_comp_mk]; unfold Function.comp; simp
  | Seq p₁ p₂ ih₁ ih₂ =>
    funext h
    simp only [sem, ih₁, asdsad, Chain.map, OrderHom.mk_comp_mk, ih₂]
    unfold Function.comp; simp only [sem_n]
    simp [Countsupp.bind_continuous_left _ |>.map_ωSup, Chain.map]
    unfold Function.comp; simp only
    simp [Countsupp.bind_continuous_right _ |>.map_ωSup, Chain.map]
    unfold Function.comp
    rw [OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup']
    intro i j hij n
    simp
    apply Countsupp.bind_mono_left _ (p₁.sem_n_mono hij h)
  | Weight w p ih =>
    ext h h'
    simp
    rw [ih]
    simp [ωSup_mul_left _ |>.map_ωSup, Chain.map]
    unfold Function.comp; simp only [sem_n, Countsupp.hMul_apply_left]
  | Add p₁ p₂ ih₁ ih₂ =>
    funext h
    simp only [sem, ih₁, ih₂]
    simp [ωSup_add_left _ |>.map_ωSup, ωSup_add_right _ |>.map_ωSup]
    simp [Chain.map]
    unfold Function.comp; simp only [sem_n]
    rw [OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup']
    intro i j hij n
    simp only
    gcongr
    apply p₂.sem_n_mono hij
  | Iter p ih =>
    funext h
    simp only [sem, Policy.instHPow, iter_m_sem_eq_ωSup_sem_n ih]; clear ih
    simp [ωSum_ωSup']
    simp [Chain.map]
    simp [DFunLike.coe]
    unfold Function.comp
    simp
    simp [ωSum_nat_eq_ωSup]
    rw [OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup']
    intro i j hij n
    simp
    gcongr
    apply (p.iter _).sem_n_mono hij

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.sem_n_lowerBounds [Fintype N] (p : Policy[F,N,𝒮]) (n : ℕ) : p.sem_n n ≤ p.sem := by
  rw [sem_n_approx]
  apply le_ωSup_of_le n
  rfl

end WeightedNetKAT
