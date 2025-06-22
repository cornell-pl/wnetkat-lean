import WeightedNetKAT.Computation
import Mathlib.Computability.Language
import Mathlib.Data.Finite.Sum

section

variable {F : Type} [DecidableEq Pk[F]]
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

def Predicate.test (t : Predicate[F]) (pk : Pk[F]) : Prop :=
  match t with
  | wnk_pred {false} => false
  | wnk_pred {true} => true
  | wnk_pred {~f = ~n} => pk f = n
  | wnk_pred {~t ∨ ~u} => t.test pk ∨ u.test pk
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => t.test pk ∧ u.test pk
  | wnk_pred {¬~t} => ¬Predicate.test t pk
def Predicate.test_decidable {t : Predicate[F]} : DecidablePred t.test := fun pk ↦
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
instance Predicate.test_instDecidable {t : Predicate[F]} : DecidablePred t.test := test_decidable

def 𝒲.map {X Y : Type} (m : 𝒲 𝒮 X) (f : Y → X) (hf : f.Injective) : 𝒲 𝒮 Y :=
  ⟨(m <| f ·), by
    simp only [Set.countable_coe_iff]
    convert Set.Countable.preimage_of_injOn m.countable (fun ⦃x₁⦄ a ⦃x₂⦄ a ↦ by apply hf)⟩

def 𝒲.liftPi {Q : Type} [Countable Q] (f : Q → 𝒲 𝒮 Q) : 𝒲 𝒮 (Q × Q) :=
  ⟨fun (x, y) ↦ f x y, SetCoe.countable _⟩

def 𝒲.equiv {X Y : Type} (m : 𝒲 𝒮 X) {e : Y ≃ X} : 𝒲 𝒮 Y := m.map _ e.injective

end

namespace WeightedNetKAT

/-- `At` is the set of complete tests. -/
def At (F : Type) : Type := sorry

/-- `Π` is the set of all complete assignments. -/
def Pi (F : Type) : Type := sorry
@[inherit_doc] notation "Π" => WeightedNetKAT.Pi

/--
The language of guarded strings.

Isomorphically defined as `At ⬝ (Π ⬝ dup)* ⬝ Π`.
-/
def GS (F : Type) := Pk[F] × List Pk[F] × Pk[F]

variable {F : Type} [DecidableEq Pk[F]] [Encodable Pk[F]]

def GS.mk (α : Pk[F]) (x : List Pk[F]) (β : Pk[F]) : GS F := ⟨α, x, β⟩

class WeightedConcat (α : Type) (β := Option α) where
  concat : α → α → β

-- Options: ⋄ ◇ ♢ ⬦
infixl:50 " ♢ " => WeightedConcat.concat

instance : WeightedConcat (GS F) where
  concat | ⟨α, x, β⟩, ⟨γ, y, ξ⟩ => if β = γ then some ⟨α, x ++ y, ξ⟩ else none

variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

noncomputable instance [DecidableEq (GS F)] : WeightedConcat (𝒲 𝒮 (GS F)) (𝒲 𝒮 (GS F)) where
  concat m m' := ⟨
    fun g ↦ ⨁' (x : m.supp) (y : m'.supp), if (x.val ♢ y.val) = some g then m x ⨀ m y else 𝟘,
    by
      simp
      sorry⟩

#check (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0)) ♢ (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0))

notation "gs[" α ";" β "]" => GS.mk α [] β
notation "gs[" α ";" x ";" "dup" ";" β "]" => GS.mk α [x] β
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" β "]" => GS.mk α [x, y] β

#check gs[1;2]
#check gs[1;2;dup;3]
#check gs[1;2;dup;3]

open scoped Classical in
noncomputable def G (p : Policy[F,𝒮]) : 𝒲 𝒮 (GS F) := match p with
  | wnk_policy {drop} => 𝟘
  | wnk_policy {skip} => ⟨(if ∃ α, gs[α; α; dup; α] = · then 𝟙 else 𝟘), sorry⟩
  -- TODO: α
  -- TODO: π
  | wnk_policy {~x ← ~v} => ⟨(if ∃ α β, gs[α; β] = · ∧ α[x ↦ v] = β then 𝟙 else 𝟘), sorry⟩
  | wnk_policy {dup} => ⟨(if ∃ α, gs[α; α; dup; α] = · then 𝟙 else 𝟘), sorry⟩
  | wnk_policy {¬ ~p₁} => ⟨(if G wnk_policy {@filter ~p₁} · = 𝟘 then 𝟙 else 𝟘), sorry⟩
  | wnk_policy {~p₁ ⨁ ~p₂} => G p₁ ⨁ G p₂
  | wnk_policy {~p₁ ; ~p₂} => G p₁ ♢ G p₂
  | wnk_policy {~w ⨀ ~p₁} => ⟨(w ⨀ G p₁ ·), sorry⟩
  | wnk_policy {~p₁*} => ⨁' n : ℕ, G (p₁ ^ n)
  -- TODO: figure out how these play with α
  | wnk_policy {@filter ~t} => ⟨(if ∃ α, gs[α; α] = · ∧ Predicate.test t α then 𝟙 else 𝟘), sorry⟩
  -- | wnk_policy {@filter ~(.Con t u)} => sorry
  -- | wnk_policy {~t ∨ ~u} => sorry
  -- | wnk_policy {~t = ~u} => sorry
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

end WeightedNetKAT
