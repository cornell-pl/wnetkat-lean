import WeightedNetKAT.Syntax

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]

instance : WeightedZero (𝒲 𝒮 X) := sorry
instance : WeightedAdd (𝒲 𝒮 X) := sorry
instance : WeightedMul (𝒲 𝒮 X) := sorry
instance : WeightedOmegaCompletePartialOrder (𝒲 𝒮 X) := sorry

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
  | .Con t u => fun h ↦
    t.sem h ≫= u.sem
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

omit [WeightedOmegaContinuousSemiring 𝒮] [Fintype F] [DecidableEq F] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,𝒮]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

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
  | .Iter p => fun h ↦ ⟨fun h' ↦ ⨁' n : ℕ, (((p ^ n).sem h).val h'), by sorry⟩
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Predicate[F]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Predicate.sem]

noncomputable def Φ (p : Policy[F,𝒮]) (d : H[F] → 𝒲 𝒮 H[F]) : H[F] → 𝒲 𝒮 H[F] :=
  fun h ↦ η h ⨁ (p.sem h ≫= d)

theorem 𝒲.bind_mono (f : 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=H[F] → 𝒲 𝒮 H[F]) (f ≫= ·) := by
  intro a b hab
  sorry
theorem 𝒲.bind_continuous (f : 𝒲 𝒮 H[F]) : WeightedOmegaContinuous (f ≫= ·) f.bind_mono := by
  sorry

open WeightedPartialOrder WeightedOmegaContinuousSemiring WeightedOmegaCompletePartialOrder

theorem 𝒲.add_mono_left (f : 𝒲 𝒮 H[F]) : WeightedMonotone (f ⨁ ·) := sorry
theorem 𝒲.add_mono_right (f : 𝒲 𝒮 H[F]) : WeightedMonotone (· ⨁ f) := sorry
theorem 𝒲.add_cont_left (f : 𝒲 𝒮 H[F]) : WeightedOmegaContinuous (f ⨁ ·) (add_mono_left f) := by
  sorry
theorem 𝒲.add_cont_right (f : 𝒲 𝒮 H[F]) : WeightedOmegaContinuous (· ⨁ f) (add_mono_right f) := by
  sorry

theorem Φ_mono (p : Policy[F,𝒮]) : WeightedMonotone (Φ p) :=
  fun hab h ↦ 𝒲.add_mono_left (η h) (𝒲.bind_mono _ hab)
theorem Φ_continuous (p : Policy[F,𝒮]) : WeightedOmegaContinuous (Φ p) (Φ_mono p) := by
  intro C
  ext h
  unfold Φ
  set f := p.sem h
  have := f.bind_continuous C
  have := 𝒲.add_cont_left (η h) (C.map (f ≫= ·) f.bind_mono)
  simp_all only
  rfl

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

theorem le_wSup_of_le {α : Type} [WeightedOmegaCompletePartialOrder α]
    {a : α} {C : WeightedChain α} (i : ℕ) (h : a ≼ C i) : a ≼ wSup C :=
  wle_trans h (le_wSup C i)

theorem Φ_wSup_isLfp (p : Policy[F,𝒮]) : IsLfp (Φ p) (Φ_wSup p) := by
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
      · simp [Φ_chain]
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

theorem Policy.iter_sem_eq_lfp (p : Policy[F,𝒮]) : wnk_policy {~p*}.sem = Φ_wSup p := by
  simp [Φ_wSup]
  sorry
