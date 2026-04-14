import Mathlib.Data.Finsupp.Defs
import WeightedNetKAT.RPol
import WeightedNetKAT.Semantics
import WeightedNetKAT.RPol
import WeightedNetKAT.Listed
import Mathlib.Logic.Function.Basic

theorem Finset.filterMap_insert {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → Option β) (hf : ∀ a a', ∀ b ∈ f a, b ∈ f a' → a = a') (a : α) (s : Finset α) :
      (insert a s).filterMap f hf
    = match f a with | some x => insert x (s.filterMap f hf) | none => s.filterMap f hf := by
  simp only [insert_eq]
  split
  · ext
    simp_all
    grind
  · ext b
    simp_all

theorem Finset.sum_filterMap {ι : Type} {κ : Type} {M : Type} [AddCommMonoid M] [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (e : ι → Option κ) (he : ∀ a a', ∀ b ∈ e a, b ∈ e a' → a = a') (f : κ → M) :
    ∑ x ∈ s.filterMap e he, f x = ∑ x ∈ s, match e x with | some y => f y | none => 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    simp_all
    rw [← ih]; clear ih
    simp_all [Finset.filterMap_insert]
    split
    · rw [sum_insert]
      simp_all
      intro i hi hi'
      have := he x i
      simp_all
    · simp_all

namespace WeightedNetKAT

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

variable {F : Type} [DecidableEq F] [Listed F]
variable {N : Type} [DecidableEq N]

instance {X : Type} [Countable X] : One (X →c 𝒮) where
  one := ⟨1, SetCoe.countable _⟩

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem Countsupp.one_apply {X : Type} [Countable X] {x : X} : (1 : X →c 𝒮) x = 1 := by rfl

@[simp]
theorem Countsupp.zero_bind {X : Type} [Countable X] [Encodable X] {g : X → X →c 𝒮} :
    ((0 : X →c 𝒮).bind g) = 0 := by ext x; simp

@[simp]
theorem Countsupp.one_bind {X : Type} [Countable X] [Encodable X] {g : X → X →c 𝒮} :
    ((1 : X →c 𝒮).bind g) = ω∑ x, g x := by
  ext x
  simp
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  apply ωSum_eq_ωSum_of_ne_one_bij fun ⟨x, _⟩ ↦ ⟨x, by simp_all⟩
  · intro; grind
  · simp
  · simp

noncomputable def RPol.sem (p : RPol[F,N,𝒮]) : H[F,N] → H[F,N] →c 𝒮 := match p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} => η
  | wnk_rpol {@test ~t} => fun (π, h) ↦ if π = t then η (π, h) else 0
  | wnk_rpol {@mod ~t} => fun (_, h) ↦ η (t, h)
  | wnk_rpol {dup} => fun (π, h) ↦ η (π, π::h)
  | wnk_rpol {~p; ~q} => fun h ↦ (p.sem h).bind q.sem
  | wnk_rpol {~w ⨀ ~p}=> fun h ↦ w * p.sem h
  | wnk_rpol {~p ⨁ ~q} => fun h ↦ p.sem h + q.sem h
  | wnk_rpol {~p*} => fun h ↦ ω∑ n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

theorem RPol.seq_of_prefix {p : RPol[F,N,𝒮]} {h₀ h₁ : H[F,N]} (h : (p.sem h₀) h₁ ≠ 0) :
    h₀.2 <:+ h₁.2 := by
  induction p generalizing h₀ h₁ with
  | Drop => simp [RPol.sem] at h
  | Skip => simp [RPol.sem] at h; grind
  | Test π₀ =>
    simp [RPol.sem] at h; split at h <;> simp_all
  | Mod γ =>
    simp [RPol.sem] at h
    grind
  | Dup =>
    simp [RPol.sem] at h
    grind
  | Seq p₁ p₂ ih₁ ih₂ =>
    simp [RPol.sem] at h
    grind
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [RPol.sem] at h
    grind
  | Weight w p₁ ih =>
    simp [RPol.sem] at h
    grind
  | Iter p₁ ih =>
    simp [RPol.sem] at h
    obtain ⟨x, y⟩ := h₁
    simp_all
    obtain ⟨n, h⟩ := h
    induction n generalizing h₀ with
    | zero => simp_all [RPol.sem]
    | succ => simp_all [RPol.sem]; grind

@[simp]
instance RPol.instZero : Zero RPol[F,N,𝒮] where
  zero := wnk_rpol {drop}
instance : Add RPol[F,N,𝒮] := ⟨RPol.Add⟩
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq F] [DecidableEq N] in
@[simp]
theorem RPol.add_def (p q : RPol[F,N,𝒮]) : p + q = p.Add q := rfl

@[simp]
theorem RPol.instAdd_sem (p q : RPol[F,N,𝒮]) : (p + q).sem = p.sem + q.sem := by
  ext; simp [sem]

@[simp]
theorem RPol.instZero_sem : RPol.sem (F:=F) (N:=N) (𝒮:=𝒮) 0 = 0 := by
  unfold sem; rfl

variable [Listed N]

def Pol.toRPol (p : Pol[F,N,𝒮]) : RPol[F,N,𝒮] := match p with
  -- ⨁ᶠ α ∈ At, [α ≤ t] ⨀ α
  | wnk_pol {@filter ~t} =>
    let At : Array Pk[F,N] := Listed.array
    At.filterMap (fun α ↦ if t.test α then some (wnk_rpol {@test ~α}) else none) |>.sum
  -- ⨁ᶠ α ∈ At, α; α[f ↦ n]
  | wnk_pol {~f ← ~n} =>
    let At : Array Pk[F,N] := Listed.array
    At.map (fun α ↦ wnk_rpol {@test ~α; @mod ~α[f ↦ n]}) |>.sum
  | wnk_pol {dup} => wnk_rpol {dup}
  | wnk_pol {~p; ~q} => wnk_rpol {~p.toRPol; ~q.toRPol}
  | wnk_pol {~w ⨀ ~p} => wnk_rpol {~w ⨀ ~p.toRPol}
  | wnk_pol {~p ⨁ ~q} => wnk_rpol {~p.toRPol ⨁ ~q.toRPol}
  | wnk_pol {~p*} => wnk_rpol {~p.toRPol*}

theorem Pol.filter_toRol_sem_eq_sum (t : Pred[F,N]) :
    (wnk_pol {@filter ~t}).toRPol.sem (𝒮:=𝒮) = ∑ α, if t.test α then wnk_rpol {@test ~α}.sem else 0 := by
  simp [toRPol]
  have : (Listed.array : Array Pk[F,N]).toList.toArray = (Listed.array : Array Pk[F,N]) := by simp
  rw [← this]
  generalize h : (Listed.array : Array Pk[F,N]).toList = L
  simp
  have : ∀ l : List RPol[F,N,𝒮], l.sum.sem = (l.map RPol.sem).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp_all [RPol.sem]; rfl
  rw [this]; clear this
  -- TODO: this might not be needed once we have `DecidableEq RPol`
  classical
  rw [← List.sum_toFinset]
  rw [List.toFinset_filterMap]
  · rw [Finset.sum_filterMap _ _ (by simp_all)]
    congr! 1 with p
    · simp [← h]
    · grind
  · grind
  · refine List.Nodup.filterMap ?_ ?_
    · grind
    · simp [← h, Array.nodup_iff_toList_nodup]

theorem Pol.assign_toRol_sem_eq_sum (f : F) (v : N) :
    (wnk_pol {~f ← ~v}).toRPol.sem (𝒮:=𝒮) = ∑ α, wnk_rpol {@test ~α; @mod ~α[f ↦ v]}.sem := by
  simp [toRPol]
  have : (Listed.array : Array Pk[F,N]).toList.toArray = (Listed.array : Array Pk[F,N]) := by simp
  rw [← this]
  generalize h : (Listed.array : Array Pk[F,N]).toList = L
  simp
  have : ∀ l : List RPol[F,N,𝒮], l.sum.sem = (l.map RPol.sem).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp_all [RPol.sem]; rfl
  simp [this]; clear this
  -- TODO: this might not be needed once we have `DecidableEq RPol`
  classical
  rw [← List.sum_toFinset _ ?_]
  · simp
    apply Finset.sum_bij (fun a _ ↦ a) <;> simp
    simp [← h]
  · simp [← h, Array.nodup_iff_toList_nodup]

theorem Pol.toRol_sem_eq_sem (p : Pol[F,N,𝒮]) : p.toRPol.sem = p.sem := by
  induction p with
  | Filter t =>
    simp [Pol.sem]
    simp [Pol.filter_toRol_sem_eq_sum]
    ext h₀ h₁
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp [RPol.sem, Pred.sem]
    split_ifs
    · simp_all
      split_ifs
      · subst_eqs
        rw [Finset.sum_eq_single h₀.1]
        · simp_all
        · simp_all
          intro p
          split_ifs
          · simp_all
            split <;> simp_all
          · simp_all
        · simp_all
      · simp_all
        intro p
        split_ifs
        · simp_all
          split <;> simp_all
        · simp_all
    · simp_all
      intro p
      split_ifs
      · simp_all
        split <;> simp_all
      · simp_all
  | Mod f v =>
    simp [Pol.sem]
    simp [Pol.assign_toRol_sem_eq_sum, RPol.sem]
    ext h₀ h₁
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp
    split_ifs
    · subst_eqs
      rw [Finset.sum_eq_single h₀.1]
      · simp
        rw [ωSum_eq_single ⟨h₀, by simp [h10]⟩]
        · simp
        · simp
      · simp_all
        intro p hp a
        split_ifs
        · simp_all
        · simp_all
      · simp_all
    · simp_all
      intro p a
      split_ifs
      · subst_eqs
        simp_all
        grind
      · simp_all
  | Dup => simp [toRPol, sem, RPol.sem]
  | Seq p₁ p₂ ih₁ ih₂ => simp [toRPol, sem, RPol.sem, ih₁, ih₂]
  | Add p₁ p₂ ih₁ ih₂ => simp [toRPol, sem, RPol.sem, ih₁, ih₂]
  | Weight w p₁ ih => simp [toRPol, sem, RPol.sem, ih]
  | Iter p₁ ih =>
    simp [toRPol, sem, RPol.sem]
    ext h₀ h₁
    simp
    congr with n
    suffices (p₁.toRPol.iter n).sem= (p₁.iter n).sem by simp_all
    clear h₀ h₁
    induction n with
    | zero => simp [sem, RPol.sem]; rfl
    | succ n ih' => simp [sem, RPol.sem, ih, ih']


end WeightedNetKAT
