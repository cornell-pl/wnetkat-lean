import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.FinRange

class Listed (α : Type*) where
  list : List α
  nodup : list.Nodup
  complete : ∀ a, a ∈ list

namespace Listed

variable {α : Type*} {β : Type*}
variable [Listed α] [Listed β]

@[simp] theorem mem_list (a : α) : a ∈ list := complete a

attribute [simp] Listed.nodup

def listOf (α : Type*) [Listed α] : List α := Listed.list

def encode [DecidableEq α] (a : α) : ℕ := list.findIdx (· = a)
def decode [DecidableEq α] (i : ℕ) : Option α := list[i]?

theorem encode_decode [DecidableEq α] (a : α) : decode (encode a) = some a := by
  simp [encode, decode]
  obtain ⟨i, hi, ⟨_⟩⟩ := List.mem_iff_getElem.mp (complete a)
  refine (List.Nodup.getElem_inj_iff ?_).mpr ?_
  · simp
  · refine (List.findIdx_eq hi).mpr ?_
    simp_all
    intro j hj h
    have := Listed.nodup (α:=α)
    have := List.nodup_iff_injective_getElem.mp this
    simp [Function.Injective] at this
    have := this (a₁:=⟨i, by omega⟩) (a₂:=⟨j, by omega⟩)
    grind

def fintype [DecidableEq α] : Fintype α := {
  elems := (listOf α).toFinset
  complete := by simp [listOf, complete]
}

@[simp] theorem list_toFinset [DecidableEq α] : (list (α:=α)).toFinset = @Finset.univ α fintype := rfl

instance : Listed (α × β) where
  list := list ×ˢ list
  nodup := List.Nodup.product nodup nodup
  complete := by intro ⟨a, b⟩; simp [complete]

inductive T where | a | b | c | d
deriving DecidableEq, Repr, Inhabited

instance : Listed T where
  list := [.a, .b, .c, .d]
  nodup := by simp
  complete := by intro x; cases x <;> simp

instance {n : ℕ} : Listed (Fin n) where
  list := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

#eval listOf (Fin 3) ×ˢ listOf T

#eval List.permutations (listOf (Fin 3)) ×ˢ List.permutations (listOf T)

instance [Inhabited β] [DecidableEq α] [DecidableEq β] : Listed (α → β) where
  list := (listOf α).foldl (fun (acc : List (α → β)) a ↦ (listOf β).flatMap (fun b ↦ acc.map (fun f ↦  Function.update f a b))) [(fun _ ↦ default)]
  nodup := by
    sorry
  complete := by
    sorry

instance [Repr α] [Repr β] : Repr (α → β) where
  reprPrec f n := reprPrec ((listOf α).map (fun a ↦ (a, f a))) n

#eval! listOf (T → Fin 2)

end Listed
