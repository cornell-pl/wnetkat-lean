import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.Equiv.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax
import WeightedNetKAT.WeightedFinsum

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

variable {X : Type} {𝒮 : Type} [WeightedOmegaCompletePartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [DecidableEq N]

noncomputable instance : DecidableEq (𝒲 𝒮 H[F,N]) := Classical.typeDecidableEq (𝒲 𝒮 H)

noncomputable def Predicate.sem (p : Predicate[F,N]) : H[F,N] → 𝒲 𝒮 H[F,N] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun (π, h) ↦ if π f = n then η (π, h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.sem h ≫= fun h ↦ η h ⨁ ((if t.sem h = 𝟘 then η h else 𝟘) ≫= u.sem))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ t.sem h ≫= u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 𝟘 then η h else 𝟘

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

omit [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,N,X]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

open WeightedOmegaCompletePartialOrder in
noncomputable def Policy.sem (p : Policy[F,N,𝒮]) : H[F,N] → 𝒲 𝒮 H[F,N] := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η (π, π::h)
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

example {t u : Predicate[F,N]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Predicate.sem]

noncomputable def Φ (p : Policy[F,N,𝒮]) (d : H[F,N] → 𝒲 𝒮 H[F,N]) : H[F,N] → 𝒲 𝒮 H[F,N] :=
  fun h ↦ η h ⨁ (p.sem h ≫= d)

example {p : Policy[F,N,𝒮]} : Φ p (wnk_policy {~p*}.sem) = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  ext
  unfold Φ
  simp [WeightedAdd.wAdd, Policy.sem, Predicate.sem]

open WeightedPartialOrder WeightedOmegaContinuousPreSemiring WeightedOmegaCompletePartialOrder

theorem Φ_mono (p : Policy[F,N,𝒮]) : WeightedMonotone (Φ p) :=
  fun hab h ↦ wAdd_mono_left (η h) (𝒲.bind_mono _ hab)
theorem Φ_continuous (p : Policy[F,N,𝒮]) : WeightedOmegaContinuous (Φ p) (Φ_mono p) := by
  intro C
  ext h
  unfold Φ
  set f := p.sem h
  have := f.bind_continuous C
  have := wAdd_wSup (η h) (C.map (f ≫= ·) f.bind_mono)
  simp_all only
  rfl

omit [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.wZero_le (p : 𝒲 𝒮 H[F,N]) : 𝟘 ≼ p := by intro; simp
omit [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.Pi_wZero_le {X : Type} (p : X → 𝒲 𝒮 H[F,N]) : 𝟘 ≼ p := fun _ ↦ 𝒲.wZero_le _

noncomputable def Φ_chain (p : Policy[F,N,𝒮]) : WeightedChain (H[F,N] → 𝒲 𝒮 H[F,N]) :=
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
noncomputable def Φ_wSup (p : Policy[F,N,𝒮]) := wSup (Φ_chain p)

def IsLfp {α : Type} [WeightedOmegaCompletePartialOrder α]
    (f : α → α) (p : α) : Prop :=
  f p = p ∧ ∀ p', f p' = p' → p ≼ p'

theorem IsLfp_unique {α : Type} [WeightedOmegaCompletePartialOrder α] {f : α → α} {p₁ p₂ : α}
    (h₁ : IsLfp f p₁) (h₂ : IsLfp f p₂) : p₁ = p₂ :=
  wle_antisymm (h₁.right _ h₂.left) (h₂.right _ h₁.left)

theorem Policy.Φ_wSup_isLfp (p : Policy[F,N,𝒮]) : IsLfp (Φ p) (Φ_wSup p) := by
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

theorem Policy.iter_sem_isLfp (p : Policy[F,N,𝒮]) : IsLfp (Φ p) (wnk_policy {~p*}.sem) := by
  constructor
  · ext h h'
    simp [sem, Φ]
    suffices
          (p.sem h ≫= fun h ↦ ⨁' (n : ℕ), (p.iter n).sem h)
        = ⨁' (n : ℕ), (p.sem h ≫= fun h ↦ (p.iter n).sem h) by
      simp [this]; clear this
      nth_rw 2 [WeightedSum_nat_eq_succ]
      simp [Policy.sem, Predicate.sem]
    ext
    simp [𝒲.bind]
    magic_simp
    simp [← WeightedSum_mul_left]
    rw [WeightedSum_comm]
  · intro f hf h
    simp [sem, Φ, 𝒲.bind, WeightedAdd.wAdd]
    apply WeightedSum_nat_le (𝒮:=𝒲 𝒮 H[F,N]) (f:=(fun n ↦ (p.iter n).sem h))
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
          simp
          magic_simp
          simp [← WeightedFinsum_mul_left]
          rw [WeightedSum_WeightedFinset_comm]
        _ ≼ (p.sem h ≫= f) := by
          apply 𝒲.bind_mono
          intro h₁
          convert ih h₁
          simp [WeightedPreSemiring.instPi]

theorem Policy.iter_sem_eq_lfp (p : Policy[F,N,𝒮]) : wnk_policy {~p*}.sem = Φ_wSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_wSup_isLfp

example {p : Policy[F,N,𝒮]} : wnk_policy {~p*}.sem = wnk_policy { skip ⨁ ~p; ~p* }.sem := by
  have := Policy.iter_sem_isLfp p |>.left
  rw [← this]
  ext
  unfold Φ
  simp [WeightedAdd.wAdd, Policy.sem, Predicate.sem]

@[simp]
instance : Zero Policy[F,N,𝒮] where
  zero := wnk_policy {drop}
@[simp]
instance : HAdd Policy[F,N,𝒮] Policy[F,N,𝒮] Policy[F,N,𝒮] where
  hAdd p q := p.Add q
@[simp]
instance : Add Policy[F,N,𝒮] where
  add p q := p.Add q

open WeightedOmegaCompletePartialOrder in
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

open WeightedOmegaCompletePartialOrder in
noncomputable def Policy.sem_n (p : Policy[F,N,𝒮]) (n : ℕ) : H[F,N] → 𝒲 𝒮 H[F,N] := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η (π, π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem_n n h ≫= q.sem_n n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w ⨀ p.sem_n n h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem_n n h ⨁ q.sem_n n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁ᶠ i ∈ Finset.range n, (p ^ i).sem_n n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

attribute [local simp] Policy.approx_n Policy.sem Policy.sem_n Predicate.sem in
theorem Policy.approx_n_sem (p : Policy[F,N,𝒮]) (n : ℕ) : (p.approx_n n).sem = p.sem_n n := by
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

omit [DecidableEq F] in
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem η_apply {x y : H[F,N]} : η x y = if x = y then (𝟙 : 𝒮) else 𝟘 := by rfl
omit [DecidableEq F] in
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem η_subtype_apply {x y : H[F,N]} : η x y = if x = y then (𝟙 : 𝒮) else 𝟘 := by rfl

theorem Policy.sem_n_mono (p : Policy[F,N,𝒮]) : WeightedMonotone p.sem_n := by
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
      simp [sem_n]
      apply wle_trans (𝒲.bind_mono_left ((p.iter i).sem_n n₁) (ih h₁₂ h)) (𝒲.bind_mono_right _ ih')

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.iter_m_sem_eq_wSup_sem_n [Fintype N] {p : Policy[F,N,𝒮]} (h : p.sem = wSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
    (p.iter m).sem = wSup ⟨fun n ↦ (p.iter m).sem_n n, (p.iter m).sem_n_mono⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp
    funext h₀
    simp_all; clear h ih
    simp [WeightedOmegaCompletePartialOrder.instPi]
    magic_simp
    have := @𝒲.bind_continuous (f:=wSup ⟨(p.sem_n · h₀), (p.sem_n_mono · h₀)⟩) _ _ _ _ _
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
      have := @𝒲.bind_continuous' (g:=(p.iter m).sem_n n) _ _ _ _ _ _
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
-- theorem Policy.iter_m_sem_eq_wSup_sem_n' {p : Policy[F,N,𝒮]} (h : p.sem = wSup ⟨p.sem_n, p.sem_n_mono⟩) (m : ℕ) :
--     (p.iter m).sem = wSup ⟨fun n ↦ (p.approx_n n)^m |>.sem, ⋯⟩ := ⋯

attribute [local simp] Policy.sem Policy.sem_n in
theorem Policy.sem_n_approx [Fintype N] (p : Policy[F,N,𝒮]) : p.sem = wSup ⟨p.sem_n, sem_n_mono p⟩ := by
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
    have := @𝒲.bind_continuous (f:=wSup ⟨fun x ↦ p₁.sem_n x h, (p₁.sem_n_mono · h)⟩) _ _ _ _ _
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
      have := @𝒲.bind_continuous' (g:=p₂.sem_n n) _ _ _ _ _ _
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
theorem Policy.sem_n_lowerBounds [Fintype N] (p : Policy[F,N,𝒮]) (n : ℕ) : p.sem_n n ≼ p.sem := by
  rw [sem_n_approx]
  apply le_wSup_of_le n
  magic_simp

end WeightedNetKAT
