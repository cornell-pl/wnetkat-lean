import WeightedNetKAT.Computation
import Init.Data.Vector.Basic
import Batteries.Lean.HashMap
import Mathlib.Std.Data.HashMap

variable {𝒮 : Type*} [WeightedPartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮]
variable {X : Type*} [DecidableEq X] [Hashable X]
variable {F : Type*} [Ffin : Fintype F] [DecidableEq F] [Hashable F] [Encodable F]

def FinMap (α : Type*) (β : Type*) [i : Fintype α] := Vector β i.card

instance instHashableVector {α : Type*} [Hashable α] (n : ℕ) : Hashable (Vector α n) where
  hash x := hash x.toArray

instance (α : Type*) (β : Type*) [i : Fintype α] [Hashable β] : Hashable (FinMap α β) :=
  inferInstanceAs (Hashable (Vector β i.card))

instance (α : Type*) (β : Type*) [i : Fintype α] [DecidableEq β] : DecidableEq (FinMap α β) :=
  inferInstanceAs (DecidableEq (Vector β i.card))

instance (α : Type*) (β : Type*) [i : Fintype α] [BEq β] : BEq (FinMap α β) :=
  inferInstanceAs (BEq (Vector β i.card))

abbrev Pk' := FinMap F ℕ
notation "Pk'[" F "]" => Pk' (F:=F)

abbrev H' := Array Pk'[F]
notation "H'[" F "]" => H' (F:=F)

-- instance : Setoid (F ≃ Fin (Fintype.card F)) := sorry

-- instance {x1 x2} : @HasEquiv.Equiv (F ≃ Fin (Fintype.card F)) instHasEquivOfSetoid x1 x2 := sorry

def Pk'.toPk (pk : Pk'[F]) : Pk[F,N] := fun x ↦ pk.getD ((Ffin.truncEquivFinOfCardEq (n:=Ffin.card) (by simp)).rep) 0
def H'.toH (h : H'[F]) : H[F,N] := h.toList.map Pk'.toPk

structure 𝒟
    (𝒮 : Type*) [WeightedPartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedMonotonePreSemiring 𝒮]
    (X : Type*) [DecidableEq X] [Hashable X] where
  map : Std.HashMap X 𝒮

def 𝒟.toFun (m : 𝒟 𝒮 X) : W X 𝒮 := (m.map.getD · 𝟘)

def 𝒟.supp (m : 𝒟 𝒮 X) : List X := m.map.keys.filter (m.toFun · ≠ 𝟘)

def 𝒟.to𝒞 (m : 𝒟 𝒮 H'[F]) : 𝒞 𝒮 H[F,N] := {
  toFun := fun x ↦ m.toFun x.toH
  supp := m.supp.toFinset
  supp_is_supp := by
    ext x
    simp [toFun, supp, Std.HashMap.getD_eq_getD_getElem?, Option.getD_eq_iff]
  }

instance : WeightedAdd (𝒟 𝒮 H'[F]) where wAdd a b := ⟨a.map.mergeWith (fun _ x y ↦ x ⨁ y) b.map⟩
instance : WeightedMul (𝒟 𝒮 H'[F]) where wMul a b := ⟨a.map.mergeWith (fun _ x y ↦ x ⨀ y) b.map⟩
instance : WeightedZero (𝒟 𝒮 H'[F]) where wZero := ⟨∅⟩

theorem 𝒟.sound_add (a b : 𝒟 𝒮 H'[F]) : (a ⨁ b).to𝒞 = @WeightedAdd.wAdd (𝒞 𝒮 H'[F]) _ a.to𝒞 b.to𝒞 := by
  sorry
