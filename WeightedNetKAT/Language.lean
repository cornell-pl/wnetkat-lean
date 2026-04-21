module

public import Mathlib.Data.Finsupp.Defs
public import WeightedNetKAT.RPol
public import WeightedNetKAT.Semantics
public import WeightedNetKAT.Reduction
public import WeightedNetKAT.ListExt

@[expose] public section

namespace WeightedNetKAT

/-- `Pk?` is the set of complete tests. -/
def Pk? (F : Type) (N : Type) [Listed F] : Type := Pk[F,N]

/-- `Pk!` is the set of all complete assignments. -/
def Pk! (F : Type) (N : Type) [Listed F] : Type := Pk[F,N]

/--
The language of guarded strings.

Isomorphically defined as `Pk? ⬝ (Pk! ⬝ dup)* ⬝ Pk!`.
-/
def GS (F : Type) (N : Type) [Listed F] := Pk[F,N] × List Pk[F,N] × Pk[F,N]
notation "GS[" f "," n "]" => GS (F:=f) (N:=n)

instance {F N : Type} [Listed F] [DecidableEq F] [DecidableEq N] : DecidableEq GS[F,N] := instDecidableEqProd
instance {F N : Type} [Listed F] [Listed N] [DecidableEq N] : Countable GS[F,N] := instCountableProd

variable {F : Type} [Listed F] [DecidableEq F]
variable {N : Type} [Listed N] [DecidableEq N]

notation "gs[" α ";" β "]" => (⟨α, [], β⟩ : GS _ _)
notation "gs[" α ";" x ";" "dup" ";" β "]" => (⟨α, [x], β⟩ : GS _ _)
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" β "]" => (⟨α, [x, y], β⟩ : GS _ _)
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" z ";" "dup" ";" β "]" => (⟨α, [x, y, z], β⟩ : GS _ _)

@[notation_class]
class Concat (α : Type*) (β : outParam Type*) where
  /-- Concatenation `♢` -/
  concat : α → α → β

export Concat (concat)

@[inherit_doc]
infixl:70 " ♢ " => Concat.concat

class ConcatAssoc (α : Type*) [Concat α α] where
  concat_assoc (a b c : α) : a ♢ b ♢ c = a ♢ (b ♢ c)

export ConcatAssoc (concat_assoc)

instance : Concat GS[F,N] (Option GS[F,N]) where
  concat | ⟨α, x, β⟩, ⟨γ, y, ξ⟩ => if β = γ then some ⟨α, x ++ y, ξ⟩ else none

variable {𝒮 : Type} [Semiring 𝒮]

def GS.splitAtJoined (g : GS[F,N]) (n : ℕ) (γ : Pk[F,N]) : GS[F,N] × GS[F,N] :=
  let (g₀, g, gₙ) := g
  let (l, r) := g.splitAt n
  ((g₀, l, γ), (γ, r, gₙ))

example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    GS.splitAtJoined gs[α;α₁;dup;α₂;dup;α₃] 0 γ = (gs[α;γ], gs[γ;α₁;dup;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    GS.splitAtJoined gs[α;α₁;dup;α₂;dup;α₃] 1 γ = (gs[α;α₁;dup; γ], gs[γ;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    GS.splitAtJoined gs[α;α₁;dup;α₂;dup;α₃] 2 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    GS.splitAtJoined gs[α;α₁;dup;α₂;dup;α₃] 3 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl

instance : Concat (GS[F,N] →c 𝒮) (GS[F,N] →c 𝒮) where
  concat L R := ⟨
    fun xₙ ↦ ∑ i ∈ Finset.range (xₙ.2.1.length + 1), ∑ (γ : Pk[F,N]), L (xₙ.splitAtJoined i γ).1 * R (xₙ.splitAtJoined i γ).2,
    SetCoe.countable _,
  ⟩

omit [DecidableEq F] in
theorem G.concat_apply {L R : GS F N →c 𝒮} {xₙ : GS F N} :
      ((L ♢ R) : _ →c 𝒮) xₙ
    = ∑ i ∈ Finset.range (xₙ.2.1.length + 1), ∑ (γ : Pk[F,N]), L (xₙ.splitAtJoined i γ).1 * R (xₙ.splitAtJoined i γ).2 := by
  rfl

variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

theorem G.concat_eq_ωSum {L R : GS F N →c 𝒮} {xₙ : GS F N} :
      ((L ♢ R) : _ →c 𝒮) xₙ
    = ω∑ (x : L.support) (y : R.support), if (x.val ♢ y.val) = some xₙ then L x * R y else 0 := by
  symm
  obtain ⟨α, A, αₙ⟩ := xₙ
  simp [Concat.concat]
  rw [← Finset.sum_product']
  rw [← ωSum_finset]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨i, γ⟩, hi⟩, hi'⟩ ↦ by
    exact ⟨(α, A.take i, γ), by simp; contrapose! hi'; simp [hi', GS.splitAtJoined]⟩)
  · intro ⟨⟨⟨i, γ⟩, hi⟩, b⟩; grind [List.take_eq_take_iff]
  · intro ⟨g₀, hg₀⟩
    simp at hg₀ ⊢
    intro g₁ hg₁ h h'
    split at h
    split at h
    · subst_eqs
      simp only [List.length_append]
      rename_i A₀ γ A₁
      simp [GS.splitAtJoined]
      use A₀.length
      simp +arith only [List.take_left', List.drop_left', true_and]
      use γ
    · contradiction
  · simp [GS.splitAtJoined]
    intro i γ hi hγ
    rw [ωSum_eq_single ⟨(γ, List.drop i A, αₙ), by simp; contrapose! hγ; simp [hγ]⟩]
    · simp
    · grind

omit [Listed N] [DecidableEq F] [DecidableEq N] in
@[simp, grind =]
theorem GS.mk_eq {α β γ δ : Pk[F,N]} {xs} : (@Eq (GS F N) gs[α;β] (γ, xs, δ)) ↔ α = γ ∧ xs = [] ∧ β = δ := by
  simp_all [GS]
omit [Listed N] [DecidableEq F] [DecidableEq N] in
@[simp, grind =]
theorem GS.mk_one_eq {α κ β γ δ : Pk[F,N]} {xs} : (@Eq (GS F N) gs[α;κ;dup;β] (γ, xs, δ)) ↔ α = γ ∧ xs = [κ] ∧ β = δ := by
  simp_all [GS, eq_comm]

def G.ofPk (f : Pk[F,N] → GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if ∃ α, f α = · then 1 else 0), SetCoe.countable _⟩
def G.ofConst [DecidableEq GS[F,N]] (f : GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if f = · then 1 else 0), SetCoe.countable _⟩

open scoped Classical in
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofPk_apply (f : Pk[F,N] → GS[F,N]) (x : GS[F,N]) :
    G.ofPk f x = if ∃ α, f α = x then (1 : 𝒮) else 0 := rfl
omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofConst_apply [DecidableEq GS[F,N]] (f : GS[F,N]) (x : GS[F,N]) :
    G.ofConst f x = if f = x then (1 : 𝒮) else 0 := rfl

noncomputable def G (p : RPol[F,N,𝒮]) : GS[F,N] →c 𝒮 := match p with
  | wnk_rpol { drop } => 0
  -- [x = α; α | α ∈ Pk]
  | wnk_rpol { skip } => G.ofPk fun α ↦ gs[α; α]
  -- [x = α; α]
  | wnk_rpol { @test ~α } => G.ofConst gs[α; α]
  -- [x = α; π | α ∈ Pk]
  | wnk_rpol { @mod ~π } => G.ofPk fun α ↦ gs[α; π]
  -- [x = α; α; dup; α | α ∈ Pk]
  | wnk_rpol { dup } => G.ofPk fun α ↦ gs[α; α; dup; α]
  | wnk_rpol { ~p₁ ⨁ ~p₂ } => G p₁ + G p₂
  | wnk_rpol { ~p₁ ; ~p₂ } => G p₁ ♢ G p₂
  | wnk_rpol { ~w ⨀ ~p₁ } => w * G p₁
  | wnk_rpol { ~p₁* } => ω∑ n : ℕ, G (p₁ ^ n)
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega
syntax "G⟦" cwnk_rpol "⟧" : term
macro_rules | `(G⟦$p⟧) => `(G wnk_rpol { $p })
open Lean Elab PrettyPrinter Delaborator Meta Command Term in
@[app_unexpander G]
meta def G.unexpander : Unexpander
| `($_ $y) => do
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | y => `(cwnk_rpol|~$y)
  `(G⟦$y⟧)
| _ => throw ()

namespace G

variable {gs : GS[F,N]}

@[simp]
theorem skip_eq : (G⟦skip⟧ gs : 𝒮) = if gs.1 = gs.2.2 ∧ gs.2.1 = [] then 1 else 0 := by
  obtain ⟨α, (_ | ⟨x, xs⟩), β⟩ := gs <;> simp [G]
@[simp]
theorem test_eq {π} : (G⟦@test ~π⟧ gs : 𝒮) = if gs.1 = gs.2.2 ∧ gs.1 = π ∧ gs.2.1 = [] then 1 else 0 := by
  obtain ⟨α, (_ | ⟨x, xs⟩), β⟩ := gs <;> simp [G]; grind
@[simp]
theorem mod_eq {π} : (G⟦@mod ~π⟧ gs : 𝒮) = if gs.2.2 = π ∧ gs.2.1 = [] then 1 else 0 := by
  obtain ⟨α, (_ | ⟨x, xs⟩), β⟩ := gs <;> simp [G]; grind
@[simp]
theorem dup_eq : (G⟦dup⟧ gs : 𝒮) = if gs.2.2 = gs.1 ∧ gs.2.1 = [gs.1] then 1 else 0 := by
  obtain ⟨α, (_ | ⟨x, xs⟩), β⟩ := gs <;> simp [G]; grind

@[simp]
theorem skip_concat {x : GS F N →c 𝒮} : G⟦skip⟧ ♢ x = x := by
  ext ⟨α, xn, β⟩
  simp [G, concat_apply, GS.splitAtJoined, ite_and]
  rcases xn with _ | _ <;> simp
@[simp]
theorem concat_skip {x : GS F N →c 𝒮} : x ♢ G⟦skip⟧ = x := by
  ext ⟨α, xn, β⟩
  simp [G, concat_apply, GS.splitAtJoined, ite_and]
  rw [Finset.sum_eq_single xn.length] <;> simp
  grind [Prod.mk.injEq, List.take_eq_nil_iff, List.length_nil]

@[simp]
theorem seq_skip {p : RPol[F,N,𝒮]} : G⟦~p; skip⟧ = G⟦~p⟧ := by
  ext ⟨α, xs, β⟩;
  simp [G.concat_apply, G, GS.splitAtJoined, Finset.sum_range_succ, ite_and]
  rw [Finset.sum_ite_of_false] <;> simp

attribute [-simp] Function.iterate_succ in
theorem iter_succ (p₁ : RPol[F,N,𝒮]) (n : ℕ) :
    G (p₁.iter (n + 1)) = (G p₁ ♢ ·)^[n] (G p₁) := by
  induction n with
  | zero =>
    ext gs
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    if hgs : ¬(G p₁) gs = 0 then
      simp only [RPol.iter, G, ofPk, Function.iterate_zero, id_eq]
      simp [concat_eq_ωSum, Countsupp.coe_mk, mul_ite, mul_one, mul_zero]
      simp [Concat.concat]
      rw [ωSum_eq_single ⟨gs, by grind [Countsupp.mem_support_iff]⟩]
      · rw [ωSum_eq_single ⟨⟨gs.2.2, [], gs.2.2⟩, by simp only [Countsupp.mem_support_iff,
        Countsupp.coe_mk, exists_apply_eq_apply, ↓reduceIte, ne_eq, h10, not_false_eq_true]⟩]
        · simp only [exists_apply_eq_apply, ↓reduceIte, ite_eq_left_iff]
          grind
        · grind only [= List.append_assoc, Countsupp.coe_mk, Countsupp.mem_support_iff,
          =_ List.append_assoc, Subtype.mk.injEq, → List.eq_nil_of_append_eq_nil,
          cases eager Subtype]
      · simp only [ωSum_eq_zero_iff]
        grind
    else
      simp at hgs
      simp only [RPol.iter, G, concat_eq_ωSum, ofPk, Countsupp.coe_mk, mul_ite,
        mul_one, mul_zero, Function.iterate_zero, id_eq, hgs, ωSum_eq_zero_iff, ite_eq_right_iff,
        forall_exists_index, Subtype.forall, Countsupp.mem_support_iff, ne_eq, not_forall,
        forall_apply_eq_imp_iff]
      simp only [Concat.concat]
      grind
  | succ n ih =>
    simp only [RPol.iter, G, Function.iterate_succ', Function.comp_apply]
    grind only [G, RPol.iter]

attribute [-simp] Function.iterate_succ in
theorem iter (p₁ : RPol[F,N,𝒮]) (n : ℕ) :
    G (p₁.iter n) = (G p₁ ♢ ·)^[n] (G wnk_rpol {skip}) := by
  induction n with
  | zero =>
    ext gs
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    if hgs : ¬(G p₁) gs = 0 then
      simp only [RPol.iter, G, ofPk, Function.iterate_zero, id_eq]
    else
      simp at hgs
      simp only [RPol.iter, G, ofPk, Countsupp.coe_mk, Concat.concat,
        Function.iterate_zero, id_eq]
  | succ n ih =>
    simp only [RPol.iter, G, Function.iterate_succ', Function.comp_apply]
    grind only [G, RPol.iter]

end G

namespace GS

noncomputable instance : HPow (GS F N →c 𝒮) ℕ (GS F N →c 𝒮) where
  hPow s n := (s ♢ ·)^[n] G⟦skip⟧

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq F] in
instance : ConcatAssoc (GS F N →c 𝒮) where
  concat_assoc a b c := by
    ext ⟨α, xs, β⟩
    simp [G.concat_apply]
    simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, splitAtJoined, GS]
    simp [List.take_take, List.take_drop]
    simp [List.drop_take]

    simp [Finset.sum_comm (γ := ℕ)]
    rw [Finset.sum_comm]
    congr! 2 with γ _ κ

    have {n} {f : ℕ → ℕ → 𝒮} : ∑ x ∈ ..=n, ∑ y ∈ ..=n - x, f x y = ∑ x ∈ ..=n, ∑ y ∈ ..=x, f y (x - y) := by
      induction n with
      | zero => simp
      | succ n ih =>
        simp [Finset.sum_range_succ (n := n + 1)]
        have : ∑ x ∈ ..=n, ∑ y ∈ ..=n + 1 - x, f x y = ∑ x ∈ ..=n, ∑ y ∈ ..=(n - x) + 1, f x y := by
          congr! 2
          ext
          simp_all
          omega
        simp [this]
        conv => enter [1, 1, 2, x]; rw [Finset.sum_range_succ]
        simp [ih, Finset.sum_add_distrib]
        simp [add_assoc]
        congr! 3 with i hi j hj k hk
        grind
    simp [this]

    congr! <;> grind

variable (M : GS F N →c 𝒮)

@[simp]
theorem pow_zero : M^0 = G⟦skip⟧ := by
  simp [HPow.hPow]
@[simp]
theorem pow_one : M^1 = M := by
  ext ⟨α, xn, β⟩
  simp [HPow.hPow, G, G.concat_apply, splitAtJoined]
  rw [Finset.sum_eq_single xn.length] <;> simp
  grind
theorem pow_succ {n} : M^(n+1) = M ♢ M^n := by
  simp only [HPow.hPow, G, Function.iterate_succ', Function.comp_apply]
theorem pow_succ' {n} : M^(n+1) = M^n ♢ M := by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 1 [pow_succ]
    nth_rw 2 [pow_succ]
    rw [ih]
    rw [concat_assoc]
theorem pow_add {n m : ℕ} : M^(n + m) = M^n ♢ M^m := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ', ← concat_assoc, ← ih, ← add_assoc]

end GS

def GS.pks (s : GS[F,N]) : List Pk[F,N] := s.1 :: s.2.1 ++ [s.2.2]
def GS.H (s : GS[F,N]) : H[F,N] := (s.2.2, s.2.1.reverse)

def GS.toRPol (g : GS[F,N]) : RPol[F,N,𝒮] :=
  wnk_rpol {@test ~g.1}.Seq <| g.2.1.foldr (fun x y ↦ wnk_rpol { @mod ~x; dup; ~y }) wnk_rpol { @mod ~g.2.2 }

example (a b c d : Pk[F,N]) :
    GS.toRPol gs[a;b;dup;c;dup;d] (𝒮:=𝒮) = wnk_rpol { @test ~a; @mod ~b; dup; @mod ~c; dup; @mod ~d } := by
  rfl

noncomputable def GS.sem (g : GS[F,N]) : H[F,N] → H[F,N] →c 𝒮 :=
  g.toRPol.sem
omit [Listed N] in
theorem GS.sem_eq (g : GS[F,N]) (h) :
    g.sem (𝒮:=𝒮) h = if g.1 = h.1 then η (g.H.1, g.H.2 ++ h.2) else 0 := by
  if h10 : (1 : 𝒮) = 0 then ext; simp [eq_zero_of_zero_eq_one h10.symm] else
  rcases h with ⟨π, h⟩
  simp_all [GS.sem]
  split_ifs with h₀
  · simp [GS.toRPol, RPol.sem, h₀]
    ext ⟨π', h'⟩
    simp
    rw [ωSum_eq_single ⟨⟨π, h⟩, by simp [h10]⟩ (by simp_all)]
    simp
    obtain ⟨g₀, g, g₁⟩ := g
    simp_all
    subst_eqs
    simp [H]
    induction g generalizing π h with
    | nil => simp_all [RPol.sem]
    | cons x g ih =>
      simp_all [RPol.sem]
      rw [ωSum_eq_single ⟨⟨x, h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
      rw [ωSum_eq_single ⟨⟨x, x::h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
  · ext; simp [GS.toRPol, RPol.sem, ne_comm.mp h₀]

@[simp]
noncomputable def RPol.sem_G_theorem (p : RPol[F,N,𝒮]) : Prop :=
  p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h

theorem RPol.sem_G.Drop : wnk_rpol {drop}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext h; simp [sem, G]
theorem RPol.sem_G.Skip : wnk_rpol {skip}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;π], (by simp [G, h10])⟩]
  · simp [GS.H]
  · simp +contextual [G, GS.H, h10, Countsupp.ite_apply]
theorem RPol.sem_G.Test {π₀} : wnk_rpol {@test ~π₀}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
    ext ⟨π, h⟩
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp [GS.sem_eq, sem, G]
    if h₀ : π = π₀ then
      subst_eqs
      rw [ωSum_eq_single ⟨gs[π₀;π₀], (by simp [G, h10])⟩]
      · simp [GS.H, η]
      · simp [G, GS.H]
    else
      symm
      have : π₀ ≠ π := fun a ↦ h₀ (Eq.symm a)
      simp [h₀, G, GS.H, h10, this]
theorem RPol.sem_G.Mod {γ} : wnk_rpol {@mod ~γ}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;γ], (by simp [G, h10])⟩]
  · simp [GS.H, η]
  · simp +contextual [G, GS.H, h10, Countsupp.ite_apply]
theorem RPol.sem_G.Dup : wnk_rpol {dup}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩ ⟨π', h'⟩
  simp
  simp [GS.sem_eq]
  simp [sem, GS.H]
  split_ifs with h₀
  · cases h₀
    symm
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    rw [ωSum_eq_single ⟨gs[π;π;dup;π], (by simp [G, h10])⟩]
    · simp_all [η]
    · simp [G]
      intro g hg
      split_ifs
      · grind
      · simp
  · symm
    simp [G, Countsupp.ite_apply]
    grind

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

theorem RPol.sem_G.Seq {p₁ p₂} (ih₁ : p₁.sem_G_theorem) (ih₂ : p₂.sem_G_theorem) :
    wnk_rpol {~p₁ ; ~p₂}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp only [sem_G_theorem] at *
  simp [sem, G]
  rw [ih₁, ih₂]; clear ih₁ ih₂
  simp
  simp [Countsupp.bind, G.concat_eq_ωSum]
  simp [Concat.concat]
  ext h₀ h₁
  simp [← ωSum_mul_right, ← ωSum_mul_left]
  conv => left; arg 1; ext; rw [ωSum_comm]
  simp [← ωSum_prod' (α:=𝒮)]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, h⟩ ↦
    ⟨⟨(b.2.2, b.2.1.reverse ++ h₀.2), by
      simp_all
      obtain ⟨b₀, b₁, b₂⟩ := b
      obtain ⟨c₀, c₁, c₂⟩ := c
      simp_all [G, GS.sem_eq, GS.H]
      simp [Concat.concat] at ha
      obtain ⟨⟨⟨_⟩, ⟨_⟩⟩, h⟩ := h
      use (b₀, b₁, b₂)
      split_ifs at h <;> simp_all⟩,
      ⟨b, hb⟩, ⟨c, hc⟩⟩)
  · simp
    intro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, h⟩
    simp_all only [Prod.mk.injEq, Subtype.mk.injEq, Subtype.forall, Function.mem_support, ne_eq,
      ite_eq_right_iff, Classical.not_imp, and_imp, Prod.forall, and_true,
      Countsupp.mem_support_iff]
    simp_all only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
    grind
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    simp_all only [Function.mem_support, ne_eq, Subtype.coe_eta, Prod.mk.eta, Set.mem_range,
      Prod.mk.injEq, Subtype.mk.injEq, Subtype.exists, ite_eq_right_iff, Classical.not_imp,
      exists_and_left, exists_prop, Prod.exists, exists_eq_right_right, Countsupp.mem_support_iff]
    simp_all only [Countsupp.mem_support_iff, Countsupp.ωSum_apply, Countsupp.hMul_apply_left,
      ne_eq, ωSum_eq_zero_iff, Subtype.forall, not_forall]
    simp_all only [exists_prop]
    obtain ⟨a, ha, ha'⟩ := ha
    intro h
    simp_all [GS.sem_eq, GS.H]
    split_ifs at * <;> try simp_all [Countsupp.coe_zero,  ite_eq_right_iff, ite_self, mul_ite, mul_one, mul_zero, zero_mul, η_apply]
    obtain ⟨a₀, a₁, a₂⟩ := a
    obtain ⟨b₀, b₁, b₂⟩ := b
    obtain ⟨c₀, c₁, c₂⟩ := c
    subst_eqs
    simp_all
    obtain ⟨⟨_⟩, h, h'⟩ := h
    obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
    simp_all [G, G.concat_eq_ωSum]
    simp_all [Concat.concat]
    apply Exists.intro
    use ha
    apply Exists.intro
    use hc
    simp_all
  · simp [G]
    simp_all [GS.sem_eq, GS.H]
    intro a ha b hb c hc h h'
    split at h
    simp at h
    obtain ⟨⟨_⟩, _⟩ := h
    simp_all
    split_ifs at *
    · simp_all only [η_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff, Classical.not_imp,
      ↓reduceIte]
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
    · simp_all
      grind
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
    · simp_all
      grind
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
theorem RPol.sem_G.Add {p₁ p₂} (ih₁ : p₁.sem_G_theorem) (ih₂ : p₂.sem_G_theorem) : wnk_rpol {~p₁ ⨁ ~p₂}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp [sem]
  rw [ih₁, ih₂]; clear ih₁ ih₂
  ext h h'
  simp [G, right_distrib, ωSum_add]
  congr! 1
  · symm
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨x, h₀⟩, h₁⟩ ↦ ⟨x, by simp at h₀; simp [G, h₀]⟩)
    · intro ⟨⟨_, _⟩, _⟩; simp
    · intro ⟨_, h₀⟩
      simp at h₀
      simp_all [G]
      contrapose! h₀
      simp_all [G]
      rcases h₀
      simp_all
    · simp
  · symm
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨x, h₀⟩, h₁⟩ ↦ ⟨x, by simp at h₀; simp [G, h₀]⟩)
    · intro ⟨⟨_, _⟩, _⟩; simp
    · intro ⟨_, h₀⟩
      simp at h₀
      simp_all [G]
      contrapose! h₀
      simp_all [G]
      rcases h₀
      simp_all
    · simp
theorem RPol.sem_G.Weight {w} {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~w ⨀ ~p₁}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp only [sem_G_theorem] at ih
  simp [sem, ih, G]; clear ih
  ext h h'
  simp [← ωSum_mul_left]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, by simp_all; contrapose! ha'; simp_all⟩)
  · intro ⟨_, _⟩ ⟨_, _⟩
    simp_all
    exact fun a ↦ SetCoe.ext a
  · intro ⟨s, h₀⟩; simp
    obtain ⟨π, h⟩ := h
    simp_all [G]
    contrapose! h₀
    simp_all [← mul_assoc]
    obtain ⟨_, _⟩ := h₀
    simp_all
  · simp [G]
    intro g h₀ h₁
    simp_all [← mul_assoc]

theorem RPol.sem_G.Iter {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~p₁*}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  funext h₀
  simp [sem]
  if h10 : (1 : 𝒮) = 0 then ext; simp [eq_zero_of_zero_eq_one h10.symm] else
  have : ∀ n, (p₁.iter n).sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
    intro n
    induction n with
    | zero =>
      simp [G, sem]
      ext h h'
      simp
      rw [ωSum_eq_single ⟨⟨h.1, [], h.1⟩, by simp [G, h10]⟩]
      · if hh :  h = h' then
          subst_eqs
          simp only [↓reduceIte]
          split_ifs with hβ
          · simp [GS.sem_eq, GS.H]
          · contrapose hβ
            use h.1
        else
          simp [GS.sem_eq, GS.H, hh]
      · simp [GS.sem_eq, GS.H, G, Countsupp.ite_apply]
        grind
    | succ n ih' =>
      have := RPol.sem_G.Seq (p₁:=p₁) (p₂:=p₁.iter n) ih ih'
      simp_all only [sem_G_theorem, iter, iter.eq_2]
  simp only [sem_G_theorem] at this; simp only [this]; clear this
  simp [G]
  ext α
  simp [← ωSum_mul_right]
  rw [ωSum_comm]
  congr with n
  apply ωSum_eq_ωSum_of_ne_one_bij
  rotate_right
  · exact fun ⟨x, hx⟩ ↦ ⟨x, by simp_all; contrapose! hx; simp [hx]⟩
  · intro; grind
  · simp_all [G]; grind
  · simp

theorem RPol.sem_G (p : RPol[F,N,𝒮]) :
    p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h := by
  induction p with
  | Drop => exact RPol.sem_G.Drop
  | Skip => exact RPol.sem_G.Skip
  | Test π₀ => exact RPol.sem_G.Test
  | Mod γ => exact RPol.sem_G.Mod
  | Dup => exact RPol.sem_G.Dup
  | Seq p₁ p₂ ih₁ ih₂ => exact RPol.sem_G.Seq ih₁ ih₂
  | Add p₁ p₂ ih₁ ih₂ => exact RPol.sem_G.Add ih₁ ih₂
  | Weight w p₁ ih => exact RPol.sem_G.Weight ih
  | Iter p₁ ih => exact RPol.sem_G.Iter ih

end WeightedNetKAT
