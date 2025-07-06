import Mathlib.Data.Finsupp.Defs
import WeightedNetKAT.RPol
import WeightedNetKAT.Semantics
import WeightedNetKAT.RPol

namespace WeightedNetKAT

variable {F : Type} -- [DecidableEq Pk[F,N]]
variable {N : Type} [DecidableEq N]
variable {𝒮 : Type}

def Pred.test (t : Pred[F,N]) (pk : Pk[F,N]) : Prop :=
  match t with
  | wnk_pred {false} => false
  | wnk_pred {true} => true
  | wnk_pred {~f = ~n} => pk f = n
  | wnk_pred {~t ∨ ~u} => t.test pk ∨ u.test pk
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => t.test pk ∧ u.test pk
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
  -- TODO: update this once we fix the syntax for ;
  | .Con t u =>
    have := t.test_decidable pk
    have := u.test_decidable pk
    if h' : t.test pk ∧ u.test pk then .isTrue h' else .isFalse h'
  | wnk_pred {¬~t} =>
    have := t.test_decidable pk
    if h' : ¬t.test pk then .isTrue h' else .isFalse h'
instance Pred.test_instDecidable {t : Pred[F,N]} : DecidablePred t.test := test_decidable

end WeightedNetKAT

namespace WeightedNetKAT

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [CanonicallyOrderedAdd 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

instance {X : Type} [Countable X] : One (X →c 𝒮) where
  one := ⟨1, SetCoe.countable _⟩

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [CanonicallyOrderedAdd 𝒮] in
@[simp]
theorem Countsupp.one_apply {X : Type} [Countable X] {x : X} : (1 : X →c 𝒮) x = 1 := by rfl

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [CanonicallyOrderedAdd 𝒮] in
@[simp]
theorem Countsupp.zero_bind {X : Type} [Countable X] [Encodable X] {g : X → X →c 𝒮} :
    ((0 : X →c 𝒮).bind g) = 0 := by ext x; simp

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
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

omit [DecidableEq F] [Encodable F] [Fintype N] [Encodable N] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.seq_of_prefix {p : RPol[F,N,𝒮]} {h₀ h₁ : H[F,N]} (h : (p.sem h₀) h₁ ≠ 0) :
    h₀.2 <:+ h₁.2 := by
  induction p generalizing h₀ h₁ with
  | Drop => simp [RPol.sem] at h
  | Skip => simp [RPol.sem] at h; grind
  | Test π₀ =>
    simp [RPol.sem] at h; split at h; split at h; simp_all
    subst_eqs
    obtain ⟨_, _⟩ := h
    · subst_eqs
      simp
    · simp_all
  | Mod γ =>
    simp [RPol.sem] at h; split at h
    obtain ⟨_, _⟩ := h₁
    simp_all
    obtain ⟨⟨_⟩, _⟩ := h
    simp_all
  | Dup =>
    simp [RPol.sem] at h; split at h
    obtain ⟨_, _⟩ := h₁
    simp_all
    obtain ⟨⟨_⟩, _⟩ := h
    simp
  | Seq p₁ p₂ ih₁ ih₂ =>
    simp [RPol.sem] at h
    obtain ⟨x, y⟩ := h₁
    simp_all
    obtain ⟨h₂, h₃, h₄⟩ := h
    have h₄ : ¬(p₂.sem h₂) (x, y) = 0 := by intro; simp_all
    specialize ih₁ h₃
    specialize ih₂ h₄
    simp_all
    exact List.IsSuffix.trans ih₁ ih₂
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [RPol.sem] at h
    obtain ⟨x, y⟩ := h₁
    simp_all
    apply not_or_of_imp at h
    rcases h with h | h
    · apply ih₁ h
    · apply ih₂ h
  | Weight w p₁ ih =>
    simp [RPol.sem] at h
    obtain ⟨x, y⟩ := h₁
    simp_all
    have : ¬(p₁.sem h₀) (x, y) = 0 := by intro; simp_all
    apply ih this
  | Iter p₁ ih =>
    simp [RPol.sem] at h
    obtain ⟨x, y⟩ := h₁
    simp_all
    obtain ⟨n, h⟩ := h
    induction n generalizing h₀ with
    | zero => simp_all [RPol.sem]
    | succ n ih' =>
      simp_all [RPol.sem]
      obtain ⟨w, l, r⟩ := h
      have : ¬((p₁.iter n).sem w) (x, y) = 0 := by intro; simp_all
      specialize ih' this
      specialize ih l
      exact List.IsSuffix.trans ih ih'

def Finset.toList' {α : Type} [Encodable α] [DecidableEq α] (s : Finset α) : List α := s.val.rep
theorem Finset.nodup_toList' {α : Type} [Encodable α] [DecidableEq α] (s : Finset α) :
    (Finset.toList' s).Nodup := by
  have := Quotient.rep_spec s.val
  simp at this
  rw [toList', ← Multiset.coe_nodup, this]
  exact s.nodup
theorem Finset.mem_toList'_iff {α : Type} [Encodable α] [DecidableEq α] (s : Finset α) (x : α) :
    x ∈ (Finset.toList' s) ↔ x ∈ s := by
  have := Quotient.rep_spec s.val
  simp at this
  rw [toList', ← Multiset.mem_coe, this]
  rfl
@[simp]
theorem Finset.toList'_empty {α : Type} [Encodable α] [DecidableEq α] :
    Finset.toList' (∅ : Finset α) = [] := by
  have := Quotient.rep_spec (∅ : Finset α).val
  simp at this
  exact (Multiset.coe_eq_zero (toList' ∅)).mp this

@[simp]
instance RPol.instZero : Zero RPol[F,N,𝒮] where
  zero := wnk_rpol {drop}
@[simp]
instance : HAdd RPol[F,N,𝒮] RPol[F,N,𝒮] RPol[F,N,𝒮] where
  hAdd p q := p.Add q
@[simp]
instance : Add RPol[F,N,𝒮] where
  add p q := p.Add q

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [DecidableEq F] [Encodable F] [Fintype N] [Encodable N] in
@[simp]
theorem RPol.instAdd_sem (p q : RPol[F,N,𝒮]) : (p + q).sem = p.sem + q.sem := by
  ext; simp [sem]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [DecidableEq F] [Encodable F] [Fintype N] [Encodable N] in
@[simp]
theorem RPol.instZero_sem : RPol.sem (F:=F) (N:=N) (𝒮:=𝒮) 0 = 0 := by
  unfold sem; rfl

def Policy.toRPol (p : Policy[F,N,𝒮]) : RPol[F,N,𝒮] := match p with
  -- ⨁ᶠ α ∈ At, [α ≤ t] ⨀ α
  | wnk_policy {@filter ~t} =>
    let At : List Pk[F,N] := Finset.toList' Finset.univ
    At.filterMap (fun α ↦ if t.test α then some (wnk_rpol {@test ~α}) else none) |>.sum
  -- ⨁ᶠ α ∈ At, α; α[f ↦ n]
  | wnk_policy {~f ← ~n} =>
    let At : List Pk[F,N] := Finset.toList' Finset.univ
    At.map (fun α ↦ wnk_rpol {@test ~α; @mod ~α[f ↦ n]}) |>.sum
  | wnk_policy {dup} => wnk_rpol {dup}
  | wnk_policy {~p; ~q} => wnk_rpol {~p.toRPol; ~q.toRPol}
  | wnk_policy {~w ⨀ ~p} => wnk_rpol {~w ⨀ ~p.toRPol}
  | wnk_policy {~p ⨁ ~q} => wnk_rpol {~p.toRPol ⨁ ~q.toRPol}
  | wnk_policy {~p*} => wnk_rpol {~p.toRPol*}


theorem Pred.sem_eq_test (t : Pred[F,N]) :
    t.sem (𝒮:=𝒮) = fun (h : H[F,N]) ↦ if t.test h.1 then η h else 0 := by
  induction t with
  | Bool b =>
    if b = true then
      simp_all [sem, Pred.sem, Pred.test]
    else
      simp_all [sem, Pred.sem, Pred.test]
  | Test => sorry
  | Dis => sorry
  | Con => sorry
  | Not => sorry

theorem Policy.filter_toRol_sem_eq_sum (t : Pred[F,N]) [DecidableEq RPol[F,N,𝒮]] :
    (wnk_policy {@filter ~t}).toRPol.sem (𝒮:=𝒮) = ∑ α, if t.test α then η else 0 := by
  simp [toRPol]
  have : ∀ l : List RPol[F,N,𝒮], l.sum.sem = (l.map (RPol.sem)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp_all
  simp [this]; clear this
  rw [← List.sum_toFinset]
  apply Finset.sum_bij_ne_zero (fun x _ _ ↦ sorry)
  · simp
  · simp [Finset.mem_toList'_iff]
    simp [RPol.sem]
    intro a ha ha' b hb hb'
    ext f
    simp_all
    sorry
  · sorry
  · sorry
  · sorry

theorem Policy.toRol_sem_eq_sem (p : Policy[F,N,𝒮]) : p.toRPol.sem = p.sem := by
  induction p with
  | Filter t =>
    sorry
    -- simp [Policy.filter_toRol_sem_eq_sum]
    -- simp [toRPol, sem, RPol.sem]
    -- ext h₀ h₁
    -- simp
    -- simp [Pred.sem_eq_test]
    -- rw [Finset.sum_eq_single h₀.1]
    -- split_ifs
    -- · simp
    -- · simp
    -- · obtain ⟨h₀, h₀'⟩ := h₀
    --   simp
    --   rintro p h
    --   split_ifs
    --   · simp
    --     sorry
    --   · simp
    -- · simp

    -- have : ∀ l : List RPol[F,N,𝒮], l.sum.sem = (l.map (RPol.sem)).sum := by
    --   intro l
    --   induction l with
    --   | nil => simp
    --   | cons p l ih => simp_all
    -- simp [this]; clear this
    -- simp [List.map_filterMap]
    -- have : ∀ l : List Pk[F,N],
    --       (l.filterMap (fun x ↦ if t.test x then some (wnk_rpol {@test ~x}.sem (𝒮:=𝒮)) else none)).sum
    --     = (l.map (fun x ↦ if t.test x then (wnk_rpol {@test ~x}.sem (𝒮:=𝒮)) else 0)).sum := by
    --   intro l
    --   induction l with
    --   | nil => simp
    --   | cons p l ih =>
    --     simp
    --     simp [← ih]
    --     rw [List.filterMap_cons]
    --     split_ifs <;> simp
    --     -- apply?
    --     -- simp_all

    -- simp [this]; clear this
    -- simp [List.sum_map_ite]
    -- simp [nsmul_zero]
    -- have :
    --   ∀ S,
    --     ((List.filter (fun b ↦ decide (t.test b)) (Finset.toList' S)).map (fun a ↦ wnk_rpol {@test ~a}.sem (𝒮:=𝒮))).sum =
    --       ∑ a ∈ S, if t.test a then wnk_rpol {@test ~a}.sem else 0 := by
    --   intro S
    --   induction S using Finset.induction with
    --   | empty => simp
    --   | insert a S ha ih =>
    --     simp_all
    --     sorry

    -- simp

      -- refine List.filterMap_eq_map_iff_forall_eq_some.mpr ?_
      -- simp [RPol.sem]
      -- intro x hxl


    -- induction t with
    -- | Bool b =>
    --   if b then
    --     subst_eqs
    --     simp [Pred.test, Pred.sem]
    --     ext h₀ h₁
    --     simp
    --     split_ifs
    --     · subst_eqs
    --       generalize hS : (Finset.toList' Finset.univ : List Pk[F,N]) = S
    --       have : S ≠ [] := sorry
    --       have : S.Nodup := by sorry
    --       clear hS
    --       induction S with
    --       | nil => sorry
    --       | cons x S ih =>
    --         simp at *
    --         simp_all
    --         rcases S with _ | ⟨y, S⟩
    --         · simp_all [RPol.sem]
    --           split; split_ifs <;> simp_all
    --         simp_all [ih, RPol.sem]
    --         split
    --         · split_ifs
    --           · subst_eqs
    --             simp
    --             sorry
    --           · simp
    --     · sorry
    --   else
    --     simp_all
    --     subst_eqs
    --     sorry
    -- | _ => sorry
  | Mod => simp [toRPol, sem, RPol.sem]; sorry
  | Dup => simp [toRPol, sem, RPol.sem]; rfl
  | Seq p₁ p₂ ih₁ ih₂ => simp [toRPol, sem, RPol.sem, ih₁, ih₂]
  | Add p₁ p₂ ih₁ ih₂ => simp [toRPol, sem, RPol.sem, ih₁, ih₂]
  | Weight w p₁ ih => simp [toRPol, sem, RPol.sem, ih]
  | Iter p₁ ih =>
    simp [toRPol, sem, RPol.sem, ih]
    ext h₀ h₁
    simp
    congr with n
    suffices (p₁.toRPol.iter n).sem= (p₁.iter n).sem by simp_all
    clear h₀ h₁
    induction n with
    | zero => simp [sem, Pred.sem, RPol.sem]
    | succ n ih' => simp [sem, Pred.sem, RPol.sem, ih, ih']


end WeightedNetKAT
