import WeightedNetKAT.Computation
import Mathlib.Computability.Language
import Mathlib.Data.Finite.Sum
import WeightedNetKAT.RPol

namespace WeightedNetKAT

variable {F : Type} -- [DecidableEq Pk[F,N]]
variable {N : Type} [DecidableEq N]
variable {𝒮 : Type}

def Predicate.test (t : Predicate[F,N]) (pk : Pk[F,N]) : Prop :=
  match t with
  | wnk_pred {false} => false
  | wnk_pred {true} => true
  | wnk_pred {~f = ~n} => pk f = n
  | wnk_pred {~t ∨ ~u} => t.test pk ∨ u.test pk
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => t.test pk ∧ u.test pk
  | wnk_pred {¬~t} => ¬Predicate.test t pk
def Predicate.test_decidable {t : Predicate[F,N]} : DecidablePred t.test := fun pk ↦
  match h : t with
  | wnk_pred {false} => .isFalse (by simp [Predicate.test])
  | wnk_pred {true} => .isTrue (by simp [Predicate.test])
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
instance Predicate.test_instDecidable {t : Predicate[F,N]} : DecidablePred t.test := test_decidable

end WeightedNetKAT

section

variable {F : Type}
variable {N : Type} [DecidableEq N]
variable {𝒮 : Type}
variable [Semiring 𝒮]

-- def 𝒲.map {X Y : Type} (m : X →c 𝒮) (f : Y → X) (hf : f.Injective) : 𝒲 𝒮 Y :=
--   ⟨(m <| f ·), by
--     simp only [Set.countable_coe_iff]
--     convert Set.Countable.preimage_of_injOn m.countable (fun ⦃x₁⦄ a ⦃x₂⦄ a ↦ by apply hf)⟩

-- def 𝒲.liftPi {Q : Type} [Countable Q] (f : Q → 𝒲 𝒮 Q) : 𝒲 𝒮 (Q × Q) :=
--   ⟨fun (x, y) ↦ f x y, SetCoe.countable _⟩
def Finsupp.liftPi {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P] (f : Q → P →₀ 𝒮) : (Q × P) →₀ 𝒮 :=
  ⟨(i.elems.biUnion (fun q ↦ (f q).support.map ⟨(q, ·), (Prod.mk_right_injective q)⟩)),
    (fun (x, y) ↦ f x y),
    (by simp [Fintype.complete])⟩

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
-- @[simp]
-- theorem 𝒲.liftPi_apply {Q : Type} [Countable Q]
--     (f : Q → 𝒲 𝒮 Q) (q : Q) (p : Q) : 𝒲.liftPi f ⟨q, p⟩ = f q p := rfl
-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem 𝒞.liftPi_apply {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P]
    (f : Q → P →₀ 𝒮) (q : Q) (p : P) : Finsupp.liftPi f ⟨q, p⟩ = f q p := rfl

-- def 𝒲.equiv {X Y : Type} (m : X →c 𝒮) {e : Y ≃ X} : 𝒲 𝒮 Y := m.map _ e.injective

end

namespace WeightedNetKAT

/-- `At` is the set of complete tests. -/
def At (F : Type) (N : Type) : Type := Pk[F,N]

/-- `Π` is the set of all complete assignments. -/
def Pi (F : Type) (N : Type) : Type := Pk[F,N]
@[inherit_doc] notation "Π" => WeightedNetKAT.Pi

/--
The language of guarded strings.

Isomorphically defined as `At ⬝ (Π ⬝ dup)* ⬝ Π`.
-/
def GS (F : Type) (N : Type) := Pk[F,N] × List Pk[F,N] × Pk[F,N]
notation "GS[" f "," n "]" => GS (F:=f) (N:=n)

instance {F N : Type} [Fintype F] [DecidableEq F] [DecidableEq N] : DecidableEq GS[F,N] := instDecidableEqProd
instance {F N : Type} [Fintype F] [Fintype N] : Countable GS[F,N] := instCountableProd
instance {F N : Type} [Fintype F] [Fintype N] [Encodable F] [Encodable N] : Encodable GS[F,N] := Encodable.Prod.encodable

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

def GS.mk (α : Pk[F,N]) (x : List Pk[F,N]) (β : Pk[F,N]) : GS[F,N] := ⟨α, x, β⟩

class WeightedConcat (α : Type) (β : outParam Type := Option α) where
  /-- Weighted concatination -/
  concat : α → α → β

@[inherit_doc]
infixl:50 " ♢ " => WeightedConcat.concat

instance : WeightedConcat GS[F,N] where
  concat | ⟨α, x, β⟩, ⟨γ, y, ξ⟩ => if β = γ then some ⟨α, x ++ y, ξ⟩ else none

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

noncomputable instance : WeightedConcat (GS[F,N] →c 𝒮) (GS[F,N] →c 𝒮) where
  concat m m' := ⟨
    fun g ↦ ω∑ (x : m.support) (y : m'.support), if (x.val ♢ y.val) = some g then m x * m' y else 0,
    SetCoe.countable _,
  ⟩

#check (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0)) ♢ (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0))

notation "gs[" α ";" β "]" => GS.mk α [] β
notation "gs[" α ";" x ";" "dup" ";" β "]" => GS.mk α [x] β
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" β "]" => GS.mk α [x, y] β

#check gs[1;2]
#check gs[1;2;dup;3]
#check gs[1;2;dup;3]

open scoped Classical in
noncomputable def G.ofPk (f : Pk[F,N] → GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if ∃ α, f α = · then 1 else 0), SetCoe.countable _⟩
def G.ofConst [DecidableEq GS[F,N]] (f : GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if f = · then 1 else 0), SetCoe.countable _⟩

open scoped Classical in
omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofPk_apply (f : Pk[F,N] → GS[F,N]) (x : GS[F,N]) :
    G.ofPk f x = if ∃ α, f α = x then (1 : 𝒮) else 0 := rfl
omit [Encodable F] [Encodable N] in
omit [DecidableEq N] [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofConst_apply [DecidableEq GS[F,N]] (f : GS[F,N]) (x : GS[F,N]) :
    G.ofConst f x = if f = x then (1 : 𝒮) else 0 := rfl

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [CanonicallyOrderedAdd 𝒮]

open scoped Classical in
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

open WeightedOmegaCompletePartialOrder in
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

def GS.pks (s : GS[F,N]) : List Pk[F,N] := s.1 :: s.2.1 ++ [s.2.2]
def GS.H (s : GS[F,N]) : H[F,N] := (s.2.2, s.2.1.reverse)

def GS.toRPol (g : GS[F,N]) : RPol[F,N,𝒮] :=
  wnk_rpol {@test ~g.1}.Seq <| g.2.1.foldr (fun x y ↦ wnk_rpol { @mod ~x; dup; ~y }) wnk_rpol { @mod ~g.2.2 }

example (a b c d : Pk[F,N]) :
    gs[a;b;dup;c;dup;d].toRPol (𝒮:=𝒮) = wnk_rpol { @test ~a; @mod ~b; dup; @mod ~c; dup; @mod ~d } := by
  rfl

noncomputable def GS.sem (g : GS[F,N]) : H[F,N] → H[F,N] →c 𝒮 :=
  g.toRPol.sem
omit [DecidableEq F] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
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
    | nil =>
      simp_all [RPol.sem, η]
    | cons x g ih =>
      simp_all [RPol.sem, 𝒲.bind_apply]
      rw [ωSum_eq_single ⟨⟨x, h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
      rw [ωSum_eq_single ⟨⟨x, x::h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
  · simp [GS.toRPol, RPol.sem, h₀, ne_comm.mp h₀]

@[simp]
noncomputable def RPol.sem_G_theorem (p : RPol[F,N,𝒮]) : Prop :=
  p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
omit [Encodable F] [Encodable N] in
theorem RPol.sem_G.Drop : wnk_rpol {drop}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext h; simp [sem, G]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Skip : wnk_rpol {skip}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;π], (by simp [G, h10])⟩]
  · simp [GS.mk, GS.H, η]
  · simp [G, GS.mk, GS.H, h10]
    rintro α _ _ ⟨_⟩
    have : α ≠ π := by rintro ⟨_⟩; grind
    simp_all
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Test {π₀} : wnk_rpol {@test ~π₀}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
    ext ⟨π, h⟩
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp [GS.sem_eq, sem, G]
    if h₀ : π = π₀ then
      subst_eqs
      rw [ωSum_eq_single ⟨gs[π₀;π₀], (by simp [G, h10])⟩]
      · simp [GS.mk, GS.H, η]
      · simp [G, GS.mk, GS.H]
    else
      symm
      have : π₀ ≠ π := fun a ↦ h₀ (Eq.symm a)
      simp [h₀, G, GS.mk, GS.H, h10, this]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Mod {γ} : wnk_rpol {@mod ~γ}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;γ], (by simp [G, h10])⟩]
  · simp [GS.mk, GS.H, η]
  · simp [G, GS.mk, GS.H, h10]
    rintro α _ _ ⟨_⟩
    have : α ≠ π := by grind
    simp [this]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Dup : wnk_rpol {dup}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩ ⟨π', h'⟩
  simp
  simp [GS.sem_eq]
  simp [sem, G, GS.H]
  split_ifs with h₀
  · cases h₀
    symm
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    rw [ωSum_eq_single ⟨gs[π;π;dup;π], (by simp [G, h10])⟩]
    · simp_all [GS.mk, η]
    · simp_all [G, GS.mk]
      intro g hg
      split_ifs
      · grind
      · simp
  · symm
    simp [G]
    rintro g h10 h' ⟨⟨α, ⟨_⟩⟩, h10⟩
    --  ⟨⟨α, ⟨_⟩⟩, h10⟩
    simp [GS.mk]
    split_ifs
    · subst_eqs
      simp [η, h10]
      grind
    · rfl
theorem RPol.sem_G.Seq {p₁ p₂} (ih₁ : p₁.sem_G_theorem) (ih₂ : p₂.sem_G_theorem) : wnk_rpol {~p₁ ; ~p₂}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  sorry
omit [Encodable F] [Encodable N] in
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
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
omit [Encodable F] [Encodable N] in
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Weight {w} {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~w ⨀ ~p₁}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp only [sem_G_theorem, instWeightedHMul𝒲] at ih
  simp [sem, ih, G]; clear ih
  ext h h'
  simp [← ωSum_mul_left]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, by simp_all; contrapose! ha'; simp_all⟩)
  · intro ⟨_, _⟩ ⟨_, _⟩
    simp_all
    exact fun a ↦ SetCoe.ext a
  · intro ⟨s, h₀⟩; simp [GS.H]
    obtain ⟨π, h⟩ := h
    simp_all [G]
    contrapose! h₀
    simp_all [← mul_assoc, G]
    obtain ⟨_, _⟩ := h₀
    simp_all
  · simp [G]
    intro g h₀ h₁
    simp_all [← mul_assoc, G]
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Iter {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~p₁*}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp [sem, G] at ih ⊢
  ext h h'
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp
  simp [← ωSum_mul_right]
  letI : DecidableEq (GS F N) := instDecidableEqProd
  rw [ωSum_comm]
  congr with n
  suffices (p₁.iter n).sem = fun h ↦ ω∑ (x : ↑(G wnk_rpol {~p₁*}).support), (G (p₁.iter n)) x * (x.val.sem (𝒮:=𝒮) h) by
    simp [this]
  clear h h'
  induction n with
  | zero =>
    ext h h'
    simp [sem, G, GS.sem_eq, GS.H, GS.mk]
    split_ifs
    · subst_eqs
      symm
      sorry
    · symm
      simp [G]
      intro ⟨g₀, g, g₁⟩ n h₀
      split_ifs with h₁ h₂
      · simp_all [η]
        -- obtain ⟨α, _, _⟩ := h₂
        sorry
        -- simp_all
      · simp
      -- · simp
      -- · sorry
  | succ n ih' =>
    simp [sem]
    simp [ih]
    simp [ih']
    clear ih ih'
    ext h h'
    simp [𝒲.bind_apply, G]
    simp [WeightedConcat.concat]
    sorry
    -- simp [← WeightedSum_mul_left, ← WeightedPreSemiring.mul_assoc, ← WeightedSum_mul_right]
    -- rw [WeightedSum_comm]
    -- congr! with ⟨i, hi⟩
    -- rw [WeightedSum_comm]
    -- congr! with ⟨j, hj⟩
    -- simp_all only
    -- simp only [G, instHPow, W.support_mem_iff, 𝒲.toFun_apply, WeightedSum_apply_𝒲, ne_eq,
    --   WeightedSum_eq_zero_iff, not_forall] at hi hj
    -- apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨x, h₀⟩, h₁⟩ ↦ ⟨x.H, by
    --   simp_all [GS.H]
    --   simp_all
    --   split_ifs at h₁ with h₁'
    --   · split at h₁'
    --     simp_all
    --     obtain ⟨⟨_⟩, ⟨_⟩⟩ := h₁'
    --     sorry
    --   · sorry


    --   ⟩)
    -- · sorry
    -- · sorry
    -- · sorry

variable [OmegaContinuousNonUnitalSemiring 𝒮] in
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
