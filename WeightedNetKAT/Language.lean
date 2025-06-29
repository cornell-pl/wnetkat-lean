import WeightedNetKAT.Computation
import Mathlib.Computability.Language
import Mathlib.Data.Finite.Sum
import WeightedNetKAT.RPol

namespace WeightedNetKAT

variable {F : Type} -- [DecidableEq Pk[F,N]]
variable {N : Type} [DecidableEq N]
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

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
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

def 𝒲.map {X Y : Type} (m : 𝒲 𝒮 X) (f : Y → X) (hf : f.Injective) : 𝒲 𝒮 Y :=
  ⟨(m <| f ·), by
    simp only [Set.countable_coe_iff]
    convert Set.Countable.preimage_of_injOn m.countable (fun ⦃x₁⦄ a ⦃x₂⦄ a ↦ by apply hf)⟩

def 𝒲.liftPi {Q : Type} [Countable Q] (f : Q → 𝒲 𝒮 Q) : 𝒲 𝒮 (Q × Q) :=
  ⟨fun (x, y) ↦ f x y, SetCoe.countable _⟩
def 𝒞.liftPi {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P] (f : Q → 𝒞 𝒮 P) : 𝒞 𝒮 (Q × P) :=
  𝒞.mk'
    (fun (x, y) ↦ f x y)
    (i.elems.biUnion (fun q ↦ (f q).finSupp.map ⟨(q, ·), (Prod.mk_right_injective q)⟩))
    (by simp [Fintype.complete])

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem 𝒲.liftPi_apply {Q : Type} [Countable Q]
    (f : Q → 𝒲 𝒮 Q) (q : Q) (p : Q) : 𝒲.liftPi f ⟨q, p⟩ = f q p := rfl
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem 𝒞.liftPi_apply {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P]
    (f : Q → 𝒞 𝒮 P) (q : Q) (p : P) : 𝒞.liftPi f ⟨q, p⟩ = f q p := rfl

def 𝒲.equiv {X Y : Type} (m : 𝒲 𝒮 X) {e : Y ≃ X} : 𝒲 𝒮 Y := m.map _ e.injective

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

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]

instance : Countable GS[F,N] := instCountableProd

def GS.mk (α : Pk[F,N]) (x : List Pk[F,N]) (β : Pk[F,N]) : GS[F,N] := ⟨α, x, β⟩

class WeightedConcat (α : Type) (β : outParam Type := Option α) where
  concat : α → α → β

-- Options: ⋄ ◇ ♢ ⬦
infixl:50 " ♢ " => WeightedConcat.concat

instance : WeightedConcat GS[F,N] where
  concat | ⟨α, x, β⟩, ⟨γ, y, ξ⟩ => if β = γ then some ⟨α, x ++ y, ξ⟩ else none

variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

noncomputable instance [DecidableEq GS[F,N]] : WeightedConcat (𝒲 𝒮 GS[F,N]) (𝒲 𝒮 GS[F,N]) where
  concat m m' := ⟨
    fun g ↦ ⨁' (x : m.supp) (y : m'.supp), if (x.val ♢ y.val) = some g then m x ⨀ m y else 𝟘,
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
noncomputable def G.ofPk (f : Pk[F,N] → GS[F,N]) : 𝒲 𝒮 GS[F,N] :=
  ⟨(if ∃ α, f α = · then 𝟙 else 𝟘), SetCoe.countable _⟩
def G.ofConst [DecidableEq GS[F,N]] (f : GS[F,N]) : 𝒲 𝒮 GS[F,N] :=
  ⟨(if f = · then 𝟙 else 𝟘), SetCoe.countable _⟩

open scoped Classical in
omit [DecidableEq N] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem G.ofPk_apply (f : Pk[F,N] → GS[F,N]) (x : GS[F,N]) :
    G.ofPk f x = if ∃ α, f α = x then (𝟙 : 𝒮) else 𝟘 := rfl
omit [DecidableEq N] [DecidableEq F] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem G.ofConst_apply [DecidableEq GS[F,N]] (f : GS[F,N]) (x : GS[F,N]) :
    G.ofConst f x = if f = x then (𝟙 : 𝒮) else 𝟘 := rfl

open scoped Classical in
noncomputable def G (p : RPol[F,N,𝒮]) : 𝒲 𝒮 GS[F,N] := match p with
  | wnk_rpol { drop } => 𝟘
  -- [x = α; α | α ∈ Pk]
  | wnk_rpol { skip } => G.ofPk fun α ↦ gs[α; α]
  -- [x = α; α]
  | wnk_rpol { @test ~α } => G.ofConst gs[α; α]
  -- [x = α; π | α ∈ Pk]
  | wnk_rpol { @mod ~π } => G.ofPk fun α ↦ gs[α; π]
  -- [x = α; α; dup; α | α ∈ Pk]
  | wnk_rpol { dup } => G.ofPk fun α ↦ gs[α; α; dup; α]
  -- [G(p₁)(x) = 𝟘]
  | wnk_rpol { ¬~α } => ⟨(if ∃ β, gs[β; β] = · ∧ β ≠ α then 𝟙 else 𝟘), SetCoe.countable _⟩
  | wnk_rpol { ~p₁ ⨁ ~p₂ } => G p₁ ⨁ G p₂
  | wnk_rpol { ~p₁ ; ~p₂ } => G p₁ ♢ G p₂
  | wnk_rpol { ~w ⨀ ~p₁ } => w • G p₁
  | wnk_rpol { ~p₁* } => ⨁' n : ℕ, G (p₁ ^ n)
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

instance {X : Type} [Countable X] : WeightedOne (𝒲 𝒮 X) where
  wOne := ⟨𝟙, SetCoe.countable _⟩

open WeightedOmegaCompletePartialOrder in
noncomputable def RPol.sem (p : RPol[F,N,𝒮]) : H[F,N] → 𝒲 𝒮 H[F,N] := match p with
  | wnk_rpol {drop} => 𝟘
  | wnk_rpol {skip} => fun _ ↦ ⟨𝟙, SetCoe.countable _⟩
  | wnk_rpol {@test ~t} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => if π = t then 𝟙 else 𝟘
  | wnk_rpol {@mod ~t} => sorry
  | wnk_rpol {¬ ~t} => sorry
  | wnk_rpol {dup} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π::π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem h ≫= q.sem)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w • p.sem h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem h ⨁ q.sem h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁' n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

def GS.pks (s : GS[F,N]) : List Pk[F,N] := s.1 :: s.2.1 ++ [s.2.2]

def GS.sem (g : GS[F,N]) : H[F,N] → 𝒲 𝒮 H[F,N] :=
  (if g.pks = · then 𝟙 else 𝟘)

theorem RPol.sem_G (p : RPol[F,N,𝒮]) :
    p.sem = fun h ↦ ⨁' x : (G p).supp, G p x • x.val.sem h := by
  induction p with
  | Drop => ext h; simp [sem, G]
  | Skip =>
    simp [sem, G, GS.sem]
    sorry
  | Test => sorry
  | Mod => sorry
  | Neg => sorry
  | Dup =>
    ext h
    simp [sem, G]
    split
    · symm
      simp [G, GS.sem, GS.pks]
    · rename_i π h'
      simp [G, GS.sem, GS.pks]
      sorry
  | Seq p₁ p₂ ih₁ ih₂ =>
    simp [sem]
    rw [ih₁, ih₂]; clear ih₁ ih₂
    ext h
    simp [G]

    sorry
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [sem]
    rw [ih₁, ih₂]; clear ih₁ ih₂
    ext h h'
    simp [G]
    sorry
  | Weight w p₁ ih =>
    simp [sem, ih, G]; clear ih
    ext h h'
    simp [← WeightedSum_mul_left]
    apply WeightedSum_eq_WeightedSum_of_ne_one_bij (fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, by simp_all; contrapose! ha'; simp_all⟩)
    · intro ⟨_, _⟩ ⟨_, _⟩
      simp_all
      exact fun a ↦ SetCoe.ext a
    · intro ⟨_, h₀⟩; simp
      intro h₁
      contrapose! h₀
      simp_all [← WeightedPreSemiring.mul_assoc, G]
    · grind [← WeightedPreSemiring.mul_assoc, G]
  | Iter => sorry


end WeightedNetKAT
