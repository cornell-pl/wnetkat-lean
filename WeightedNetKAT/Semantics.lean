import WeightedNetKAT.Countsupp
import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax

open OmegaCompletePartialOrder

@[simp]
theorem OmegaCompletePartialOrder.ωSup_const {α : Type*} [OmegaCompletePartialOrder α] (x : α) :
    ωSup ⟨fun _ ↦ x, by intro; simp⟩ = x := by
  apply le_antisymm
  · apply ωSup_le _ _ fun i ↦ ?_; rfl
  · apply le_ωSup_of_le 0; rfl

theorem List.succ_range_map {α : Type*} (f : ℕ → α) {n : Nat} :
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

abbrev η {ι : Type*} {α : Type*} [DecidableEq ι] [Zero α] [One α] (i : ι): ι →c α :=
  ⟨Pi.single i 1, Set.Countable.mono Pi.support_single_subset (Set.countable_singleton i)⟩

@[simp] theorem η_apply {ι : Type*} {α : Type*} [DecidableEq ι] [Zero α] [One α] {x y : ι} :
    η x y = if x = y then (1 : α) else 0 := by
  simp [DFunLike.coe, Pi.single, Function.update]; grind

-- @[simp] theorem η_subtype_apply {x y : H[F,N]} : η x y = if x = y then (1 : 𝒮) else 0 := by rfl

variable {X : Type*} {𝒮 : Type*}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]

variable {F : Type*} [Fintype F] [DecidableEq F]
variable {N : Type*} [DecidableEq N]

noncomputable instance : DecidableEq (X →c 𝒮) := Classical.typeDecidableEq _
-- noncomputable instance : DecidableEq (H[F,N] →c 𝒮) := Classical.typeDecidableEq (𝒲 𝒮 H)

@[simp]
def Pred.orDepth : Pred[F,N] → ℕ
| wnk_pred {false} => 0
| wnk_pred {true} => 0
| wnk_pred {~_ = ~_} => 0
| wnk_pred {~t ∨ ~u} => t.orDepth ⊔ u.orDepth + 1
| wnk_pred {~t ∧ ~u} => t.orDepth ⊔ u.orDepth
| wnk_pred {¬~t} => t.orDepth

noncomputable def Pred.sem (p : Pred[F,N]) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | wnk_pred {false} => fun _ ↦ 0
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun (π, h) ↦ if π f = n then η (π, h) else 0
  | wnk_pred {~t ∨ ~u} => fun h ↦
    -- ⟦t ⨁ ¬t; u⟧
    t.sem h + (wnk_pred {¬~t}.sem h).bind u.sem
  | wnk_pred {~t ∧ ~u} => fun h ↦ (t.sem h).bind u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 0 then η h else 0
termination_by (p.orDepth, sizeOf p)
decreasing_by all_goals simp_all; omega

def Pred.test (t : Pred[F,N]) (pk : Pk[F,N]) : Prop :=
  match t with
  | wnk_pred {false} => false
  | wnk_pred {true} => true
  | wnk_pred {~f = ~n} => pk f = n
  | wnk_pred {~t ∨ ~u} => t.test pk ∨ u.test pk
  | wnk_pred {~t ∧ ~u} => t.test pk ∧ u.test pk
  | wnk_pred {¬~t} => ¬Pred.test t pk
def Pred.test_decidable {t : Pred[F,N]} : DecidablePred t.test := fun pk ↦
  match h : t with
  | wnk_pred {false} => .isFalse (by simp [Pred.test])
  | wnk_pred {true} => .isTrue (by simp [Pred.test])
  | wnk_pred {~f = ~n} => if h' : pk f = n then .isTrue h' else .isFalse h'
  | wnk_pred {~t ∨ ~u} =>
    have := t.test_decidable pk
    have := u.test_decidable pk
    if h' : t.test pk ∨ u.test pk then .isTrue h' else .isFalse h'
  | wnk_pred {~t ∧ ~u} =>
    have := t.test_decidable pk
    have := u.test_decidable pk
    if h' : t.test pk ∧ u.test pk then .isTrue h' else .isFalse h'
  | wnk_pred {¬~t} =>
    have := t.test_decidable pk
    if h' : ¬t.test pk then .isTrue h' else .isFalse h'
instance Pred.test_instDecidable {t : Pred[F,N]} : DecidablePred t.test := test_decidable

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [DecidableEq F] in
theorem Pred.sem_eq_test (t : Pred[F,N]) :
    t.sem (𝒮:=𝒮) = fun (h : H[F,N]) ↦ if t.test h.1 then η h else 0 := by
  induction t with
  | Bool b =>
    if b = true then
      simp_all [sem, Pred.sem, Pred.test]
    else
      simp_all [sem, Pred.sem, Pred.test]
  | Test =>
    ext h₀ h₁
    simp_all [sem, Pred.sem, Pred.test]
    split_ifs
    subst_eqs
    · split
      simp_all
    · split
      simp_all
  | Dis u v =>
    ext h₀ h₁
    simp_all [sem, Pred.sem, Pred.test]
    split_ifs
    · simp_all
    · simp_all
    · simp_all
      if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
      split_ifs
      · rw [ωSum_eq_single ⟨h₀, by simp_all⟩]
        · simp_all
        · simp_all
      · simp_all
    · simp_all
  | Con =>
    ext h₀ h₁
    simp_all [sem, Pred.sem, Pred.test]
    split_ifs
    · simp_all
      if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
      rw [ωSum_eq_single ⟨h₀, by simp_all⟩]
      · simp
      · simp_all
    · simp_all
  | Not =>
    ext h₀ h₁
    simp_all [sem, Pred.sem, Pred.test]
    split_ifs
    · simp_all
    · simp_all
    · simp_all
    · simp_all

instance : Subst Pk[F,N] F N where
  subst pk f n := fun f' ↦ if f = f' then n else pk f'

@[simp]
def Pol.iter (p : Pol[F,N,X]) : ℕ → Pol[F,N,X]
  | 0 => wnk_pol { skip }
  | n+1 => wnk_pol {~p ; ~(p.iter n)}

@[simp, reducible] instance Pol.instHPow : HPow Pol[F,N,X] ℕ Pol[F,N,X] where hPow p n := p.iter n

@[simp]
def Pol.iterDepth : Pol[F,N,X] → ℕ
-- TODO: use syntax
| .Filter _ | wnk_pol {~_ ← ~_} | wnk_pol {dup} => 0
| wnk_pol {~p ⨁ ~q} | wnk_pol {~p ; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_pol {~_ ⨀ ~q} => q.iterDepth
| wnk_pol {~p *} => p.iterDepth + 1

omit [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem Pol.iterDepth_iter {p : Pol[F,N,X]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

open OmegaCompletePartialOrder in
noncomputable def Pol.sem (p : Pol[F,N,𝒮]) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | .Filter t => t.sem
  | wnk_pol {~f ← ~n} => fun (π, h) ↦ η (π[f ↦ n], h)
  | wnk_pol {dup} => fun (π, h) ↦ η (π, π::h)
  | wnk_pol {~p; ~q} => fun h ↦ (p.sem h).bind q.sem
  | wnk_pol {~w ⨀ ~p}=> fun h ↦ w * p.sem h
  | wnk_pol {~p ⨁ ~q} => fun h ↦ p.sem h + q.sem h
  | wnk_pol {~p*} => fun h ↦ ω∑ n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Pred[F,N]} :
    wnk_pol { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_pol { @filter ~t ⨁ (¬~t; @filter ~u) }.sem := by
  simp [Pol.sem, Pred.sem]

noncomputable def Φ (p : Pol[F,N,𝒮]) (d : H[F,N] → H[F,N] →c 𝒮) : H[F,N] → H[F,N] →c 𝒮 :=
  fun h ↦ η h + (p.sem h).bind d

example {p : Pol[F,N,𝒮]} : Φ p (wnk_pol {~p*}.sem) = wnk_pol { skip ⨁ ~p; ~p* }.sem := by
  ext
  unfold Φ
  simp [Pol.sem, Pred.sem]

open OmegaCompletePartialOrder OmegaContinuousNonUnitalSemiring

omit [MulRightMono 𝒮] in
theorem Φ_mono (p : Pol[F,N,𝒮]) : Monotone (Φ p) := by
  intro a b hab h
  simp [Φ]
  gcongr
  exact Countsupp.bind_mono_right (p.sem h) _ _ hab
theorem Φ_continuous [OmegaContinuousNonUnitalSemiring 𝒮] (p : Pol[F,N,𝒮]) : ωScottContinuous (Φ p) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨Φ_mono p, ?_⟩
  intro C
  ext h
  unfold Φ
  simp [(p.sem h).bind_continuous_right.map_ωSup, ωSup_add_left _ |>.map_ωSup]
  congr! 1

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.wZero_le (p : H[F,N] →c 𝒮) : 0 ≤ p := by intro; simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.Pi_wZero_le {X : Type*} (p : X → H[F,N] →c 𝒮) : 0 ≤ p := fun _ ↦ 𝒲.wZero_le _

noncomputable def Φ_chain (p : Pol[F,N,𝒮]) : Chain (H[F,N] → H[F,N] →c 𝒮) :=
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
noncomputable def Φ_ωSup (p : Pol[F,N,𝒮]) := ωSup (Φ_chain p)

def IsLfp {α : Type*} [OmegaCompletePartialOrder α]
    (f : α → α) (p : α) : Prop :=
  f p = p ∧ ∀ p', f p' = p' → p ≤ p'

theorem IsLfp_unique {α : Type*} [OmegaCompletePartialOrder α] {f : α → α} {p₁ p₂ : α}
    (h₁ : IsLfp f p₁) (h₂ : IsLfp f p₂) : p₁ = p₂ :=
  le_antisymm (h₁.right _ h₂.left) (h₂.right _ h₁.left)

variable [OmegaContinuousNonUnitalSemiring 𝒮]

theorem Pol.Φ_ωSup_isLfp (p : Pol[F,N,𝒮]) : IsLfp (Φ p) (Φ_ωSup p) := by
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

theorem Pol.iter_sem_isLfp (p : Pol[F,N,𝒮]) : IsLfp (Φ p) (wnk_pol {~p*}.sem) := by
  constructor
  · ext h h'
    simp only [Φ, sem, instHPow, Countsupp.add_apply, η_apply, Countsupp.ωSum_apply]
    suffices
          ((p.sem h).bind fun h ↦ ω∑ (n : ℕ), (p.iter n).sem h)
        = ω∑ (n : ℕ), (p.sem h).bind fun h ↦ (p.iter n).sem h by
      simp [this]; clear this
      nth_rw 2 [ωSum_nat_eq_succ]
      simp [Pol.sem, Pred.sem]
    ext

    simp [Countsupp.bind]
    simp [DFunLike.coe]
    simp [← ωSum_mul_left]
    rw [ωSum_comm]
  · intro f hf h
    simp [sem]
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

theorem Pol.iter_sem_eq_lfp (p : Pol[F,N,𝒮]) : wnk_pol {~p*}.sem = Φ_ωSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_ωSup_isLfp

example {p : Pol[F,N,𝒮]} : wnk_pol {~p*}.sem = wnk_pol { skip ⨁ ~p; ~p* }.sem := by
  have := Pol.iter_sem_isLfp p |>.left
  rw [← this]
  ext
  unfold Φ
  simp [Pol.sem, Pred.sem]

end WeightedNetKAT
