import WeightedNetKAT.Syntax

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]

-- TODO: inferInstance
open WeightedOmegaCompletePartialOrder in
instance WeightedOmegaCompletePartialOrder.instCountablePi : WeightedOmegaCompletePartialOrder (𝒲 𝒮 X) where
  wSup C := ⟨fun i ↦ wSup (C.map (·.val i) sorry), sorry⟩
  le_wSup := sorry
  wSup_le := sorry

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
  | .Iter p => fun h ↦ ⟨fun h' ↦ ⨁' n : ℕ, (((p ^ n).sem h).val h'), by
    simp [WeightedSum_eq_wSup_Nat]
    -- TODO: the support of wSup is coultable
    sorry
    ⟩
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Predicate[F]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Predicate.sem]

noncomputable def Φ (p : Policy[F,𝒮]) (d : H[F] → 𝒲 𝒮 H[F]) : H[F] → 𝒲 𝒮 H[F] :=
  fun h ↦ η h ⨁ (p.sem h ≫= d)

open WeightedOmegaCompletePartialOrder in
theorem WeightedSum_mono [Encodable X] : WeightedMonotone (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) := by
  intro f₁ f₂ h₁₂
  apply wSup_le _ _ fun i ↦ ?_
  apply le_wSup_of_le i
  simp [WeightedSum_chain, DFunLike.coe]
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [Nat.fold_succ]
    gcongr
    split
    · apply h₁₂
    · simp
open WeightedPartialOrder WeightedOmegaCompletePartialOrder in
theorem WeightedSum_cont [Encodable X] :
    WeightedOmegaContinuous (fun (f : X → 𝒮) ↦ ⨁' i : X, f i) WeightedSum_mono := by
  intro C
  apply wle_antisymm
  · apply wSup_le _ _ fun i ↦ ?_
    simp [WeightedSum_chain, DFunLike.coe]
    induction i with
    | zero => simp
    | succ i ih =>
      simp
      split
      · rename_i x hx
        sorry -- TODO: wSup_wAdd
      · simp; apply wle_trans ih (wle_refl _)
  · apply wSup_le _ _ fun i ↦ ?_
    simp [WeightedChain.map]
    simp only [DFunLike.coe]
    simp
    apply wSup_le _ _ fun j ↦ ?_
    apply le_wSup_of_le j
    simp [WeightedSum_chain]
    simp only [DFunLike.coe]
    induction j with
    | zero => simp
    | succ j ih =>
      simp
      gcongr
      · split
        · apply le_wSup_of_le i
          simp only [DFunLike.coe]
          simp
        · simp
      · exact wle_trans ih (wle_refl _)

omit [WeightedOmegaContinuousSemiring 𝒮] [Fintype F] [DecidableEq F] in
@[ext]
theorem 𝒲.ext {a b : 𝒲 𝒮 X} (h : ∀ x, a.val x = b.val x) : a = b := by
  cases a; cases b
  congr; ext
  simp_all

omit [Fintype F] [DecidableEq F] in
open WeightedOmegaContinuousSemiring in
theorem 𝒲.bind_mono (f : 𝒲 𝒮 H[F]) : WeightedMonotone (ι:=H[F] → 𝒲 𝒮 H[F]) (f ≫= ·) := by
  apply fun a b hab h ↦ WeightedSum_mono fun i ↦ (wMul_gconr (by simp) (hab i.val h))
open WeightedOmegaCompletePartialOrder in
theorem 𝒲.bind_continuous (f : 𝒲 𝒮 H[F]) : WeightedOmegaContinuous (f ≫= ·) f.bind_mono := by
  intro C
  ext h
  simp only
  simp [bind, DFunLike.coe]
  simp [WeightedChain.map]
  sorry

open WeightedPartialOrder WeightedOmegaContinuousSemiring WeightedOmegaCompletePartialOrder

theorem 𝒲.add_mono_left (f : 𝒲 𝒮 H[F]) : WeightedMonotone (f ⨁ ·) := by
  sorry
theorem 𝒲.add_mono_right (f : 𝒲 𝒮 H[F]) : WeightedMonotone (· ⨁ f) := by
  sorry
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
  simp [DFunLike.coe]
  simp [WeightedAdd.wAdd]
  simp [WeightedSemiring.left_distrib]
  rw [WeightedSum_add]
  congr
  rw [WeightedSum_mul_right]
  simp [hf]

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
      apply wAdd_gconr (by simp)
      apply wle_trans ih; clear ih
      simp only [DFunLike.coe, WeightedSum_chain, WeightedChain.val_apply, Nat.fold_succ, wle_refl]
  · apply wSup_le _ _ fun i ↦ ?_
    rcases i with _ | i
    · simp [WeightedSum_chain, DFunLike.coe]
    · apply le_wSup_of_le i ?_
      simp [DFunLike.coe, WeightedSum_chain]
      induction i with
      | zero =>
        simp [DFunLike.coe]
        simp [DFunLike.coe, h]
      | succ i ih =>
        simp only [DFunLike.coe, Nat.fold_succ]
        apply wAdd_gconr (by simp)
        apply wle_trans ih; clear ih
        simp only [DFunLike.coe, Nat.fold_succ, wle_refl]

theorem Policy.iter_k {h h'} (p : Policy[F,𝒮]) (hhh' : h ≠ h') :
    (wnk_policy {~p;~p*}.sem h).val h' = (wnk_policy {~p*}.sem h).val h' := by
  simp [sem]
  simp [𝒲.bind]
  rw [← WeightedSum_succ]
  · simp [sem, 𝒲.bind]
    sorry
  · simp [sem, Predicate.sem]
    sorry

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
      simp [DFunLike.coe, WeightedSum_chain]
      simp [WeightedAdd.wAdd]
      induction i with
      | zero => simp
      | succ i ih =>
        apply wle_trans _ ih; clear ih
        simp
        sorry
    · sorry

theorem Policy.iter_sem_eq_lfp (p : Policy[F,𝒮]) : wnk_policy {~p*}.sem = Φ_wSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_wSup_isLfp
