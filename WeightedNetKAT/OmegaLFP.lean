import WeightedNetKAT.Language
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Star
import WeightedNetKAT.MatrixExt
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Topology.Order.ScottTopology

open OmegaCompletePartialOrder
open scoped RightActions

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

scoped notation "𝟙" => Unit

scoped notation "𝒲[" x ", " y ", " s "]" => Matrix x y s

def ωlfp : (𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  ⟨⟨fun f ↦ ωSup ⟨fun n ↦ f^[n] ⊥, by
    intro a b hab
    simp
    obtain ⟨c, _, _⟩ : ∃ c, b = a + c := Nat.exists_eq_add_of_le hab
    simp [Function.iterate_add]
    clear hab
    induction a with
    | zero => simp
    | succ a ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      apply f.mono ih⟩, by
    intro a b hab
    simp
    intro i
    apply le_ωSup_of_le i
    simp
    induction i with
    | zero => simp
    | succ i ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      apply le_trans (hab _) (b.mono ih)⟩, by
    simp
    intro c
    apply le_antisymm
    · simp
      intro i
      apply le_ωSup_of_le i
      induction i with
      | zero => simp
      | succ i ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ContinuousHom.ωSup_apply]
        simp
        intro j
        apply le_trans ((c j).mono ih)
        simp
        rw [(c j).continuous]
        simp
        intro k
        apply le_ωSup_of_le (k + 1)
        simp only [Chain.mk_apply, Function.iterate_succ', Function.comp_apply]
        sorry
    · sorry⟩

theorem ωlfp_isLeast (f : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) : IsLeast {a | f a ≤ a} (ωlfp f) := by
  constructor
  · simp
    simp [ωlfp]
    rw [f.continuous]
    apply ωSup_le_ωSup_of_le
    intro i; use i + 1
    simp only [Chain.map_coe, OrderHomClass.coe_coe, Function.comp_apply, Chain.mk_apply,
      Function.iterate_succ']
    rfl
  · simp [lowerBounds, ωlfp]
    intro a ha i
    induction i with
    | zero => simp
    | succ i ih =>
      simp_all only [Function.iterate_succ', Function.comp_apply]
      apply le_trans (f.mono ih) ha

theorem map_ωlfp (f : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) : f (ωlfp f) = ωlfp f := by
  simp [ωlfp, f.continuous]
  apply le_antisymm
  · simp
    intro i
    apply le_ωSup_of_le (i + 1)
    simp only [Chain.mk_apply, Function.iterate_succ', Function.comp_apply]
    rfl
  · simp
    intro i
    rcases i with _ | i
    · simp
    · apply le_ωSup_of_le i
      simp only [Function.iterate_succ', Function.comp_apply, Chain.map_coe, OrderHomClass.coe_coe,
        Chain.mk_apply]
      rfl

theorem ωlfp_le (f : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) {a} (h : f a ≤ a) :
    ωlfp f ≤ a := (ωlfp_isLeast f).right h

theorem le_ωlfp (f : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) {a} (h : ∀ b, f b ≤ b → a ≤ b) :
    a ≤ ωlfp f := by
  have := (ωlfp_isLeast f).left
  simp at this
  apply le_trans _ this
  apply h
  simp [map_ωlfp]


namespace Chain

variable {α : Type} [OmegaCompletePartialOrder α] (C : Chain α) (p : α → Prop) [DecidablePred p] (b : α)

def filter_fun : ℕ → α
  | 0 => if p (C 0) then C 0 else b
  | n + 1 => if p (C (n + 1)) then C (n + 1) else filter_fun n

-- TODO: hb can be loosened to be ∀ i, p (C i) → b ≤ C i
def filter (hb : b ≤ C 0) :
    Chain α :=
  ⟨filter_fun C p b, by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ k hik ih =>
      apply le_trans ih; clear ih
      simp [filter_fun]
      split_ifs with h
      · suffices filter_fun C p b k ≤ C k by apply le_trans this (C.mono (by simp))
        clear! i j h
        induction k with
        | zero =>
          simp [filter_fun]; split_ifs <;> simp_all
        | succ k ihk =>
          simp_all [filter_fun]
          split_ifs
          · simp
          · apply le_trans ihk (C.mono (by simp))
      · simp
  ⟩

theorem filter_filters (hb) (h : p b) (i) : p (filter C p b hb i) := by
  induction i with
  | zero =>
    simp_all [filter, filter_fun]
    split_ifs
    · assumption
    · simp_all
  | succ i ih => simp_all [filter, filter_fun]; grind

end Chain

theorem ωSup_succ (f : Chain 𝒮) : ωSup f = ωSup ⟨fun n ↦ f (n + 1), sorry⟩ := sorry

-- salomaa axiomatization the sytem c1-13

open scoped Classical in
theorem ωlfp_induction (f : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮]) {p : 𝒲[Pk[F,N], Pk[F,N], 𝒮] → Prop}
    (step : ∀ (a : 𝒲[Pk[F,N], Pk[F,N], 𝒮]), p a → a ≤ ωlfp f → p (f a))
    (hSup : ∀ (s : Chain 𝒲[Pk[F,N], Pk[F,N], 𝒮]), (∀ a ∈ s, p a) → p (ωSup s)) :
    p (ωlfp f) := by
  simp [ωlfp]
  rw [ωSup_succ]
  simp only [Chain.mk_apply, Function.iterate_succ', Function.comp_apply]
  have := f.continuous (fixedPoints.iterateChain f ⊥ (by simp))
  simp [Chain.map, OrderHom.comp, Function.comp_def, fixedPoints.iterateChain] at this
  rw [← this]
  apply step
  · sorry
  · rfl

end WeightedNetKAT
