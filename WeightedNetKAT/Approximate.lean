module

public import WeightedNetKAT.Semantics

@[expose] public section

open OmegaCompletePartialOrder OmegaContinuousNonUnitalSemiring

namespace WeightedNetKAT

variable {X : Type*} {𝒮 : Type*}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]
  [OmegaContinuousNonUnitalSemiring 𝒮]

variable {F : Type*} [Listed F] [DecidableEq F]
variable {N : Type*} [DecidableEq N]

instance : Zero Pol[F,N,𝒮] where
  zero := wnk_pol {drop}
instance : Add Pol[F,N,𝒮] where
  add p q := p.Add q
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Listed F] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem Pol.zero_def : (0 : Pol[F,N,𝒮]) = wnk_pol {drop} := rfl
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Listed F] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem Pol.add_def (p q : Pol[F,N,𝒮]) : p + q = p.Add q := rfl

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Pol.instAdd_sem (p q : Pol[F,N,𝒮]) : (p + q).sem = p.sem + q.sem := by
  ext; simp [sem]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Pol.instZero_sem : Pol.sem (F:=F) (N:=N) (𝒮:=𝒮) 0 = 0 := by
  unfold sem Pred.sem; rfl

open OmegaCompletePartialOrder in
noncomputable def Pol.approx_n (p : Pol[F,N,𝒮]) (n : ℕ) : Pol[F,N,𝒮] := match p with
  | .Filter t => .Filter t
  | wnk_pol {~f ← ~n} => wnk_pol {~f ← ~n}
  | wnk_pol {dup} => wnk_pol {dup}
  | wnk_pol {~p; ~q} => (p.approx_n n).Seq (q.approx_n n)
  | wnk_pol {~w ⨀ ~p}=> .Weight w (p.approx_n n)
  | wnk_pol {~p ⨁ ~q} => .Add (p.approx_n n) (q.approx_n n)
  | wnk_pol {~p*} => List.range n |>.map ((p.approx_n n) ^ ·) |>.sum

open OmegaCompletePartialOrder in
noncomputable def Pol.sem_n (p : Pol[F,N,𝒮]) (n : ℕ) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | .Filter t => t.sem
  | wnk_pol {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_pol {dup} => fun (π, h) ↦ η (π, π::h)
  | wnk_pol {~p; ~q} =>
    fun h ↦ (p.sem_n n h).bind (q.sem_n n)
  | wnk_pol {~w ⨀ ~p}=> fun h ↦ w * p.sem_n n h
  | wnk_pol {~p ⨁ ~q} => fun h ↦ p.sem_n n h + q.sem_n n h
  | wnk_pol {~p*} => fun h ↦ ∑ i ∈ Finset.range n, (p ^ i).sem_n n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
attribute [local simp] Pol.approx_n Pol.sem Pol.sem_n Pred.sem in
theorem Pol.approx_n_sem (p : Pol[F,N,𝒮]) (n : ℕ) : (p.approx_n n).sem = p.sem_n n := by
  induction p with simp_all <;> try rfl
  | Iter p ih =>
    funext h
    suffices ∀ m (ih' : (p.approx_n m).sem = p.sem_n m),
          ((List.range n).map (p.approx_n m).iter).sum.sem h
        = ∑ i ∈ Finset.range n, (p.iter i).sem_n m h by
      exact this n ih
    clear ih
    intro m ih
    induction n with
    | zero => unfold sem; simp [Pred.test]
    | succ n ihn =>
      simp_all [Finset.sum_range_add]
      rw [List.succ_range_map]
      rw [← ihn]; clear ihn
      generalize (List.range n).map (p.approx_n m).iter = l
      induction l with
      | nil =>
        simp
        induction n generalizing h with
        | zero => simp [Pred.test]
        | succ n ih =>
          simp_all [Pred.test]
          congr
          funext ⟨α, h'⟩
          apply ih α h'
      | cons q l ih' => ext; simp [ih', add_assoc]

omit [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem Pol.sem_n_mono (p : Pol[F,N,𝒮]) : Monotone p.sem_n := by
  induction p with
  | Filter => intro; simp [sem_n]
  | Mod => intro; simp [sem_n]
  | Dup => intro; simp [sem_n]
  | Seq p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp only [sem_n]
    exact le_trans (Countsupp.bind_mono_right (p₁.sem_n n₁ h) _ _ (ih₂ h₁₂)) (Countsupp.bind_mono_left _ (ih₁ h₁₂ h))
  | Weight w p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply fun h' ↦ mul_right_mono (ih h₁₂ h h')
  | Add p₁ p₂ ih₁ ih₂ =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    gcongr
    · exact ih₁ h₁₂ h
    · exact ih₂ h₁₂ h
  | Iter p ih =>
    intro n₁ n₂ h₁₂ h; simp [sem_n]
    apply le_trans (Finset.sum_mono_set_of_nonneg (by simp) ?_)
    · simp
      apply Finset.sum_le_sum fun i hi ↦ ?_
      induction i generalizing h with
      | zero => simp [sem_n]
      | succ i ih' =>
        simp [sem_n]
        simp at hi
        apply le_trans (Countsupp.bind_mono_left (𝒮:=𝒮) ((p.iter i).sem_n n₁) (ih h₁₂ h))
        apply Countsupp.bind_mono_right _ _ _
        exact fun h ↦ ih' h (by simp; omega)
    · simp [h₁₂]

attribute [local simp] Pol.sem Pol.sem_n Pred.sem in
theorem Pol.iter_m_sem_eq_ωSup_sem_n [Fintype N] {p : Pol[F,N,𝒮]} (h : p.sem = ωSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
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
-- attribute [local simp] Pol.sem Pol.sem_n in
-- theorem Pol.iter_m_sem_eq_ωSup_sem_n' {p : Pol[F,N,𝒮]} (h : p.sem = ωSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
--     (p.iter m).sem = ωSup ⟨fun n ↦ (p.approx_n n)^m |>.sem, ⋯⟩ := ⋯

attribute [local simp] Pol.sem Pol.sem_n in
theorem Pol.sem_n_approx [Fintype N] (p : Pol[F,N,𝒮]) : p.sem = ωSup ⟨p.sem_n, sem_n_mono p⟩ := by
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
    simp [mul_ωSup, Chain.map, Function.comp_def]
  | Add p₁ p₂ ih₁ ih₂ =>
    funext h
    simp only [sem, ih₁, ih₂]
    simp [ωSup_add_ωSup]
    simp [Chain.map, Function.comp_def]
  | Iter p ih =>
    funext h
    simp only [sem, pow_eq_iter, iter_m_sem_eq_ωSup_sem_n ih, asdsad]; clear ih
    simp [ωSum_ωSup']
    simp [Chain.map, Function.comp_def]
    simp [ωSum_nat_eq_ωSup]
    rw [OmegaCompletePartialOrder.ωSup_ωSup_eq_ωSup']
    intro i j hij n
    simp
    gcongr
    apply (p.iter _).sem_n_mono hij

attribute [local simp] Pol.sem Pol.sem_n in
theorem Pol.sem_n_lowerBounds [Fintype N] (p : Pol[F,N,𝒮]) (n : ℕ) : p.sem_n n ≤ p.sem := by
  rw [sem_n_approx]
  apply le_ωSup_of_le n
  rfl

end WeightedNetKAT
