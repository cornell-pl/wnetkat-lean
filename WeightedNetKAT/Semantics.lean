import WeightedNetKAT.Countsupp
import WeightedNetKAT.Subst
import WeightedNetKAT.Syntax
import Mathlib.Algebra.Ring.Hom.Defs

open OmegaCompletePartialOrder

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
  simp [Pi.single, Function.update]; grind

-- @[simp] theorem η_subtype_apply {x y : H[F,N]} : η x y = if x = y then (1 : 𝒮) else 0 := by rfl

variable {X : Type} {𝒮 : Type}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [DecidableEq N]

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

def Pred.sem (p : Pred[F,N]) (h : H[F,N]) : H[F,N] →c 𝒮 :=
  if p.test h.1 then η h else 0

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

variable {M : Type} [Semiring M] [OmegaCompletePartialOrder M] [OrderBot M] [IsPositiveOrderedAddMonoid M] in
open OmegaCompletePartialOrder in
noncomputable def Pol.map (p : Pol[F,N,𝒮]) (f : 𝒮 →+* M) : Pol[F,N,M] := match p with
  | .Filter t => .Filter t
  | wnk_pol {~f ← ~n} => wnk_pol {~f ← ~n}
  | wnk_pol {dup} => wnk_pol {dup}
  | wnk_pol {~p; ~q} => wnk_pol {~(p.map f); ~(q.map f)}
  | wnk_pol {~w ⨀ ~p}=> wnk_pol {~(f w) ⨀ ~(p.map f)}
  | wnk_pol {~p ⨁ ~q} => wnk_pol {~(p.map f) ⨁ ~(q.map f)}
  | wnk_pol {~p*} => wnk_pol {~(p.map f)*}
variable {M : Type} [Semiring M] [OmegaCompletePartialOrder M] [OrderBot M] [IsPositiveOrderedAddMonoid M] in
open OmegaCompletePartialOrder in
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem map_ωSum {ι : Type} [Countable ι] (g : 𝒮 →+* M) (hg : ωScottContinuous g) (f : ι → 𝒮) :
    g (ω∑ i, f i) = ω∑ i, g (f i) := by
  simp only [ωSum]
  rw [hg.map_ωSup]
  simp only [Chain.map, OrderHom.mk_comp_mk, Function.comp_def, map_sum]
  grind [map_zero]
variable {M : Type} [Semiring M] [OmegaCompletePartialOrder M] [OrderBot M] [IsPositiveOrderedAddMonoid M] in
open OmegaCompletePartialOrder in
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem Pol.map_sem (p : Pol[F,N,𝒮]) (f : 𝒮 →+* M) (hf : ωScottContinuous f) (h h') :
    f (p.sem h h') = (p.map f).sem h h' := by
  induction p generalizing h h' with
  | Filter =>
    simp only [map, sem, Pred.sem]
    split_ifs
    · simp only [η_apply, MonoidWithZeroHom.map_ite_one_zero]
    · simp only [Countsupp.coe_zero, Pi.zero_apply]
      grind [map_zero]
  | Mod => simp only [map, sem]; split; simp
  | Dup => simp only [map, sem]; split; simp
  | Seq p q =>
    simp only [map, sem, Countsupp.bind_apply, map_ωSum f hf, map_mul]
    symm
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨a, _⟩, h⟩ ↦ ⟨a, by contrapose! h; simp_all⟩)
    · intro; grind
    · intro; simp only [Set.mem_range, Subtype.exists]
      grind [Countsupp.mem_support_iff, map_zero, Function.mem_support]
    · grind
  | Add p q ihp ihq => simp only [map, sem, Countsupp.add_apply, ihp, ihq, map_add]
  | Weight w p ih => simp only [map, sem, Countsupp.hMul_apply_left, ih, map_mul]
  | Iter p ih =>
    simp only [map, sem, instHPow, Countsupp.ωSum_apply]
    suffices ∀ x, (((p.map f).iter x).sem h) h' = f ((p.iter x).sem h h') by
      simp only [this]; apply map_ωSum f hf
    intro x
    induction x generalizing h h' with
    | zero => simp [sem, Pred.sem]; split_ifs <;> simp
    | succ x ih' =>
      simp [sem, ih, ih', map_ωSum f hf]
      apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨a, _⟩, h⟩ ↦ ⟨a, by contrapose! h; simp_all⟩)
      · intro; grind
      · intro; simp only [Set.mem_range, Subtype.exists]
        grind [Countsupp.mem_support_iff, map_zero, Function.mem_support]
      · grind

example {t u : Pred[F,N]} :
    wnk_pol { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_pol { @filter ~t ⨁ (¬~t; @filter ~u) }.sem := by
  if h01 : (0 : 𝒮) = 1 then
    ext; simp [eq_zero_of_zero_eq_one h01]
  else
    ext ⟨π₁, h₁⟩ ⟨π₂, h₂⟩
    simp [Pol.sem, Pred.sem, Pred.test]
    if h : t.test π₁ then
      simp [h]
    else
      simp [h]
      rw [ωSum_eq_single ⟨(π₁, h₁), by simp_all; grind⟩] <;> simp_all

noncomputable def Φ (p : Pol[F,N,𝒮]) (d : H[F,N] → H[F,N] →c 𝒮) : H[F,N] → H[F,N] →c 𝒮 :=
  fun h ↦ η h + (p.sem h).bind d

example {p : Pol[F,N,𝒮]} : Φ p (wnk_pol {~p*}.sem) = wnk_pol { skip ⨁ ~p; ~p* }.sem := by
  ext
  unfold Φ
  simp [Pol.sem, Pred.sem, Pred.test]

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
  simp [(p.sem h).bind_continuous_right.map_ωSup, add_ωSup]
  congr! 1

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.wZero_le (p : H[F,N] →c 𝒮) : 0 ≤ p := by intro; simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [Fintype F] [DecidableEq F] [DecidableEq N] in
@[simp] theorem 𝒲.Pi_wZero_le {X : Type} (p : X → H[F,N] →c 𝒮) : 0 ≤ p := fun _ ↦ 𝒲.wZero_le _

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

def IsLfp {α : Type} [OmegaCompletePartialOrder α]
    (f : α → α) (p : α) : Prop :=
  f p = p ∧ ∀ p', f p' = p' → p ≤ p'

theorem IsLfp_unique {α : Type} [OmegaCompletePartialOrder α] {f : α → α} {p₁ p₂ : α}
    (h₁ : IsLfp f p₁) (h₂ : IsLfp f p₂) : p₁ = p₂ :=
  le_antisymm (h₁.right _ h₂.left) (h₂.right _ h₁.left)

variable [OmegaContinuousNonUnitalSemiring 𝒮]

attribute [-simp] Function.iterate_succ in
theorem Pol.Φ_ωSup_isLfp (p : Pol[F,N,𝒮]) : IsLfp (Φ p) (Φ_ωSup p) := by
  constructor
  · simp only [Φ_ωSup]
    apply le_antisymm
    · rw [Φ_continuous p |>.map_ωSup]
      apply ωSup_le _ _ fun i ↦ ?_
      apply le_ωSup_of_le (i + 1)
      simp only [Chain.map, Φ_chain, OrderHom.mk_comp_mk, Chain.mk_apply, Function.comp_apply,
        Function.iterate_succ', le_refl]
    · apply ωSup_le
      intro i
      rcases i with _ | i
      · simp only [Φ_chain, Chain.mk_apply, Function.iterate_zero, id_eq, zero_le'']
      · simp only [Φ_chain, Chain.mk_apply, Function.iterate_succ', Function.comp_apply]
        apply Φ_mono _ (le_ωSup_of_le i (by simp only [Chain.mk_apply, le_refl]))
  · intro x hx
    refine ωSup_le _ _ fun i ↦ ?_
    induction i with
    | zero => simp [Φ_chain]
    | succ i ih =>
      simp only [Φ_chain, Chain.mk_apply, Function.iterate_succ', Function.comp_apply]
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
      simp [Pol.sem, Pred.sem, Pred.test]
    ext
    simp [Countsupp.bind, ← ωSum_mul_left]
    rw [ωSum_comm]
  · intro f hf h
    simp [sem, ωSum_nat_eq_ωSup]
    intro n
    induction n generalizing h with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_le'']
    | succ n ih =>
      rw [add_comm]
      simp only [Finset.sum_range_add, Finset.range_one, Finset.sum_singleton, iter, sem, Pred.sem, Pred.test, ↓reduceIte]
      rw [← hf]
      simp only [Φ]
      gcongr
      simp [add_comm, sem]
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
          simp only [Finset.sum_apply]

theorem Pol.iter_sem_eq_lfp (p : Pol[F,N,𝒮]) : wnk_pol {~p*}.sem = Φ_ωSup p :=
  IsLfp_unique p.iter_sem_isLfp p.Φ_ωSup_isLfp

example {p : Pol[F,N,𝒮]} : wnk_pol {~p*}.sem = wnk_pol { skip ⨁ ~p; ~p* }.sem := by
  have := Pol.iter_sem_isLfp p |>.left
  rw [← this]
  ext
  unfold Φ
  simp [Pol.sem, Pred.sem, Pred.test]

end WeightedNetKAT
