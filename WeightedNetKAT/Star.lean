import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import WeightedNetKAT.Listed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.Matrix.Block

namespace WeightedNetKAT

/-- `Star` introduces notation `m^*` which is supposed to satisfy `m^* = ω∑ n : ℕ, m^n`. Note that
  this is not imposed by the `Star` type class but rather `LawfulStar` since it requires
  `OmegaCompletePartialOrder` which is in general non-computable.
-/
class Star (α : Type) where
  star : α → α
postfix:max "^*" => WeightedNetKAT.Star.star
class LawfulStar (α : Type)
    [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [Star α] where
  star_eq_sum : ∀ m : α, m^* = ω∑ n : ℕ, m^n

instance instUnitStar {α : Type} [Star α] : Star (Matrix Unit Unit α) where
  star m := fun α β ↦ (m α β)^*
-- instance : LawfulStar (Matrix Unit Unit 𝒮) where
--   star_eq_sum := sorry

end WeightedNetKAT

def Matrix.listedEquivNat {α A : Type} [DecidableEq A] [i : Listed A] :
    Matrix A A α ≃ Matrix (Fin i.size) (Fin i.size) α :=
  ⟨fun m ↦ m.submatrix Listed.decodeFin Listed.decodeFin,
   fun m ↦ m.submatrix Listed.encodeFin Listed.encodeFin,
   by intro m; ext i j; simp,
   by intro m; ext i j; simp⟩

namespace Matrix.Star

open WeightedNetKAT

variable {α : Type} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

scoped notation "𝟙" => Unit

def nice {n : ℕ} (m : Matrix (Fin (n + 1)) (Fin (n + 1)) α) : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α
  | .inl l,  .inl r  => m ⟨l, by omega⟩ ⟨r, by omega⟩
  | .inl l,  .inr () => m ⟨l, by omega⟩ ⟨n, by omega⟩
  | .inr (), .inl r  => m ⟨n, by omega⟩ ⟨r, by omega⟩
  | .inr (), .inr () => m ⟨n, by omega⟩ ⟨n, by omega⟩

def conice {n : ℕ} (m : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α) : Matrix (Fin (n + 1)) (Fin (n + 1)) α
  | l,  r  =>
    let l' := if hl : l = n then .inr () else .inl ⟨l, by omega⟩
    let r' := if hr : r = n then .inr () else .inl ⟨r, by omega⟩
    m l' r'

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  match n with
  | 0 => fun a b ↦ m a b
  | n+1 =>
    let m' := nice m
    let a : Matrix (Fin n) (Fin n) α := m'.toBlocks₁₁
    let b := m'.toBlocks₁₂
    let c := m'.toBlocks₂₁
    let d := m'.toBlocks₂₂

    let η₁ := star_fin a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ := (d + η₃)^*
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    let m'' := Matrix.fromBlocks α β γ δ

    conice m''

instance instListed {A : Type} [DecidableEq A] [Listed A] : WeightedNetKAT.Star (Matrix A A α) where
  star m :=
    let m' := Matrix.listedEquivNat m
    let m'' := star_fin m'
    Matrix.listedEquivNat.symm m''

end Matrix.Star
