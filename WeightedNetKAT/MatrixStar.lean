import WeightedNetKAT.OmegaContinuousNonUnitalSemiring
import WeightedNetKAT.Star
import WeightedNetKAT.MatrixExt

namespace Matrix.Star

open WeightedNetKAT

section

variable {α : Type*} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α]

scoped notation "𝟙" => Unit

instance : WeightedNetKAT.Star (Matrix 𝟙 𝟙 α) where
  star m := (m () ())^*
instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [LawfulStar α] :
    LawfulStar (Matrix 𝟙 𝟙 α) where
  star_eq_sum m := by
    have := LawfulStar.star_eq_sum (m () ())
    ext ⟨⟩ ⟨⟩
    simp_all
    convert this; clear this
    rename_i n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Matrix.mul_apply, ih]

def nice {n : ℕ} (m : Matrix (Fin (n + 1)) (Fin (n + 1)) α) : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α
  | .inl l,  .inl r  => m ⟨l, by omega⟩ ⟨r, by omega⟩
  | .inl l,  .inr () => m ⟨l, by omega⟩ ⟨n, by omega⟩
  | .inr (), .inl r  => m ⟨n, by omega⟩ ⟨r, by omega⟩
  | .inr (), .inr () => m ⟨n, by omega⟩ ⟨n, by omega⟩

def conice {n : ℕ} (m : Matrix (Fin n ⊕ 𝟙) (Fin n ⊕ 𝟙) α) : Matrix (Fin (n + 1)) (Fin (n + 1)) α :=
  Matrix.concrete fun l r =>
    let l' := if hl : l = n then .inr () else .inl ⟨l, by omega⟩
    let r' := if hr : r = n then .inr () else .inl ⟨r, by omega⟩
    m l' r'

instance {m n : ℕ} : HMul α (NMatrix m n α) (NMatrix m n α) where
    hMul s M := M.map (fun x ↦ s * x)
instance {m n : ℕ} : HMul (NMatrix m n α) α (NMatrix m n α) where
    hMul M s := M.map (fun x ↦ x * s)

instance : WeightedNetKAT.Star (NMatrix 1 1 α) where
  star a := .fill (a 0 0)^*

instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] : StarIter (NMatrix 1 1 α) where
  star_iter m := by
    simp [instStarNMatrixOfNatNat]
    nth_rw 2 [← StarIter.star_iter]
    ext ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ <;> try omega
    simp [NMatrix.fill, Matrix.mul_apply]

def star_fin' {n : ℕ} (m : NMatrix n n α) : NMatrix n n α :=
  match n with
  | 0 => .ofFn fun a b ↦ False.elim (by have := a.isLt; omega)
  | n'+1 =>
    let m' := m
    let a : NMatrix n' n' α := m'.toBlocks₁₁
    let b := m'.toBlocks₁₂
    let c := m'.toBlocks₂₁
    let d := m'.toBlocks₂₂

    let η₁ := star_fin' a
    let η₂ := c * η₁
    let η₂' := η₁ * b
    let η₃ := η₂ * b

    let δ : NMatrix 1 1 α := (d + η₃)^*
    let γ := δ * η₂
    let β := η₂' * δ
    let α := η₁ + β * η₂

    NMatrix.fromBlocks α β γ δ

instance {n : ℕ} [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star (NMatrix n n α) := ⟨star_fin'⟩
instance {n : Type*} [Listed n] [AddCommMonoid α] [Mul α] [WeightedNetKAT.Star α] :
    WeightedNetKAT.Star (EMatrix n n α) := inferInstanceAs (WeightedNetKAT.Star (NMatrix _ _ α))

def star_fin {n : ℕ} (m : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  star_fin' (.ofMatrix m) |>.asMatrix

instance instStar {n : ℕ} : WeightedNetKAT.Star (Matrix (Fin n) (Fin n) α) := ⟨star_fin⟩

instance instListed {A : Type*} [DecidableEq A] [Listed A] : WeightedNetKAT.Star (Matrix A A α) where
  star m := EMatrix.asMatrix (EMatrix.ofMatrix m)^*

end

theorem star_fin'_iter {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : NMatrix n n α) :
    1 + M * M^* = M^* := by
  induction n with
  | zero => ext ⟨_, _⟩; omega
  | succ n ih =>
    let a : NMatrix n n α := M.toBlocks₁₁
    let b := M.toBlocks₁₂
    let c := M.toBlocks₂₁
    let d := M.toBlocks₂₂

    set a' := star_fin' a
    have ha' : star_fin' a = a' := rfl
    replace ih : 1 + a * a' = a' := ih _

    wlog h : M = NMatrix.fromBlocks a b c d generalizing a b c d
    · absurd h; simp [a, b, c, d]
    · simp [h] at *
      simp [WeightedNetKAT.Star.star]
      rw [star_fin']
      simp only [NMatrix.fromBlocks_toBlocks₁₁, NMatrix.fromBlocks_toBlocks₁₂,
        NMatrix.fromBlocks_toBlocks₂₂, NMatrix.fromBlocks_toBlocks₂₁]
      simp only [ha']
      set δ' := (d + c * a' * b)^*
      simp [← NMatrix.mul_assoc]
      set γ' := δ' * c * a'
      have : a' * b * δ' * c * a' = a' * b * γ' := by simp [γ', NMatrix.mul_assoc]
      simp [this]; clear this
      set β' := a' * b * δ'
      set α' := a' + a' * b * γ'

      simp [NMatrix.fromBlocks_mul]
      rw [← NMatrix.fromBlocks_eq_one (α:=α) (n:=n) (m:=1)]
      simp [NMatrix.fromBlocks_add]
      have hδ : 1 + (d + c * a' * b) * δ' = δ' := by simp [δ']; exact StarIter.star_iter (d + c * a' * b)

      congr! 1
      · grind only [NMatrix.add_mul, add_assoc, NMatrix.one_mul, add_comm, NMatrix.mul_assoc,
        left_distrib]
      · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc]
      · simp [γ']
        nth_rw 2 [← ih]
        simp [α', γ', NMatrix.mul_add, ← NMatrix.mul_assoc]
        nth_rw 3 [← hδ]
        simp [NMatrix.add_mul]
        nth_rw 1 [← ih]
        simp [NMatrix.mul_add, ← NMatrix.mul_assoc, NMatrix.add_assoc]
        congr! 1
        nth_rw 4 [← ih]
        simp [NMatrix.mul_add, ← NMatrix.mul_assoc]
        nth_rw 3 [← ih]
        simp only [NMatrix.mul_add, NMatrix.mul_one]
        grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc,
          NMatrix.add_assoc]
      · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.mul_assoc, ← NMatrix.add_assoc]

-- theorem star_fin'_iter' {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] {n : ℕ} (M : NMatrix n n α) :
--     1 + M^* * M = M^* := by
--   induction n with
--   | zero => ext ⟨_, _⟩; omega
--   | succ n ih =>
--     let a : NMatrix n n α := M.toBlocks₁₁
--     let b := M.toBlocks₁₂
--     let c := M.toBlocks₂₁
--     let d := M.toBlocks₂₂

--     set a' := star_fin' a
--     have ha' : star_fin' a = a' := rfl
--     replace ih : 1 + a' * a = a' := ih _

--     wlog h : M = NMatrix.fromBlocks a b c d generalizing a b c d
--     · absurd h; simp [a, b, c, d]
--     · simp [h] at *
--       simp [WeightedNetKAT.Star.star]
--       rw [star_fin']
--       simp only [NMatrix.fromBlocks_toBlocks₁₁, NMatrix.fromBlocks_toBlocks₁₂,
--         NMatrix.fromBlocks_toBlocks₂₂, NMatrix.fromBlocks_toBlocks₂₁]
--       simp only [ha']
--       set δ' := (d + c * a' * b)^*
--       simp [← NMatrix.mul_assoc]
--       set γ' := δ' * c * a'
--       have : a' * b * δ' * c * a' = a' * b * γ' := by simp [γ', NMatrix.mul_assoc]
--       simp [this]; clear this
--       set β' := a' * b * δ'
--       set α' := a' + a' * b * γ'

--       simp [NMatrix.fromBlocks_mul]
--       rw [← NMatrix.fromBlocks_eq_one (α:=α) (n:=n) (m:=1)]
--       simp [NMatrix.fromBlocks_add]
--       have hδ : 1 + δ' * (d + c * a' * b) = δ' := by simp [δ']; exact StarIter.star_iter' (d + c * a' * b)

--       congr! 1
--       · grind? [NMatrix.add_mul, Matrix.mul_add, NMatrix.mul_one, add_assoc, NMatrix.one_mul, add_comm, NMatrix.mul_assoc,
--         left_distrib, right_distrib]
--       · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc]
--       · simp [γ']
--         nth_rw 2 [← ih]
--         simp [α', γ', NMatrix.mul_add, ← NMatrix.mul_assoc]
--         nth_rw 3 [← hδ]
--         simp [NMatrix.add_mul]
--         nth_rw 1 [← ih]
--         simp [NMatrix.mul_add, ← NMatrix.mul_assoc, NMatrix.add_assoc]
--         congr! 1
--         nth_rw 4 [← ih]
--         simp [NMatrix.mul_add, ← NMatrix.mul_assoc]
--         nth_rw 3 [← ih]
--         simp only [NMatrix.mul_add, NMatrix.mul_one]
--         grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.one_mul, NMatrix.mul_assoc,
--           NMatrix.add_assoc]
--       · grind only [NMatrix.add_mul, NMatrix.add_comm, NMatrix.mul_assoc, ← NMatrix.add_assoc]

-- TODO: we need this
-- instance {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [LawfulStar α] {n : ℕ} :
--     LawfulStar (NMatrix n n α) where
--   unique_star X A B h := by
--     apply uniqueStarMatrix h
    -- induction n with
    -- | zero => exact h.symm
    -- | succ n ih =>
    --   simp [WeightedNetKAT.Star.star] at *
    --   simp [star_fin']
    --   set a : NMatrix n n α := A.toBlocks₁₁
    --   set b := A.toBlocks₁₂
    --   set c := A.toBlocks₂₁
    --   set d := A.toBlocks₂₂

    --   replace ih := ih (A:=a)

    --   set a' := star_fin' a

    --   apply uniqueStarMatrix (synthetic := false)

section

@[simp]
theorem NMatrix.ofMatrix_pow {α : Type*} [Semiring α] {n : ℕ} {M : Matrix (Fin n) (Fin n) α} {i : ℕ} : (NMatrix.ofMatrix M) ^ i = NMatrix.ofMatrix (M^i) := by
  ext x y
  simp
  induction i generalizing x y with
  | zero => simp; rfl
  | succ i ih => simp_all [pow_succ, Matrix.mul_apply]

@[simp]
theorem EMatrix.ofMatrix_pow {α n : Type*} [Semiring α] [Listed n] [Fintype n] [DecidableEq n] {M : Matrix n n α} {i : ℕ} : (EMatrix.ofMatrix M) ^ i = EMatrix.ofMatrix (M^i) := by
  ext x y
  simp
  induction i generalizing x y with
  | zero => simp; simp [OfNat.ofNat, One.one, NMatrix.ofMatrix, Matrix.diagonal_apply]
  | succ i ih => simp_all [pow_succ, Matrix.mul_apply]

variable {α : Type*} [Semiring α] [WeightedNetKAT.Star α] [StarIter α] [OmegaCompletePartialOrder α] [OrderBot α] [IsPositiveOrderedAddMonoid α] [LawfulStar α]
variable [∀ n, LawfulStar (NMatrix n n α)]

instance {n : Type*} [Listed n] : LawfulStar (EMatrix n n α) :=
  inferInstanceAs (LawfulStar (NMatrix _ _ _))
instance {n : Type*} [Listed n] [Fintype n] [DecidableEq n] : LawfulStar (Matrix n n α) where
  star_eq_sum X := by
    ext i j
    have := congrFun₂ (congrArg DFunLike.coe (LawfulStar.star_eq_sum (EMatrix.ofMatrix X))) i j
    simpa

end

open OmegaCompletePartialOrder

section

variable {α : Type*} [OmegaCompletePartialOrder α] {n : ℕ}

theorem ωSup_apply  : ∀ (c : Chain (NMatrix n n α)) x y, ωSup c x y = ωSup (c.map ⟨fun n ↦ n x y, fun ⦃_ _⦄ a ↦ a x y⟩) := fun c x y ↦ by
      simp [ωSup]; rfl

variable [Semiring α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [StarIter α] [MulLeftMono α] [MulRightMono α] [OmegaContinuousNonUnitalSemiring α]
    [LawfulStar α]

instance : MulRightMono (NMatrix n n α) where
  elim x y z h := by
    simp_all [Function.swap]
    intro i j
    simp [Matrix.mul_apply]
    gcongr with k
    exact h i k
instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [StarIter α] [MulLeftMono α] [MulRightMono α]
    [OmegaContinuousNonUnitalSemiring α] [LawfulStar α] {n : ℕ} :
    OmegaContinuousNonUnitalSemiring (NMatrix n n α) where
  ωScottContinuous_add_right x := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    exists fun a b h ↦ add_le_add_right h x
    intro c
    ext i j
    have : ∀ (c : Chain (NMatrix n n α)) x y, ωSup c x y = ωSup (c.map ⟨fun n ↦ n x y, fun ⦃_ _⦄ a ↦ a x y⟩) := fun c x y ↦ by
      simp [ωSup]; rfl
    simp [ωSup_apply, ωSup_add, Chain.map, OrderHom.comp]
    congr! with n
    simp
  ωScottContinuous_add_left x := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    exists fun a b h ↦ add_le_add_left h x
    intro c
    ext i j
    have : ∀ (c : Chain (NMatrix n n α)) x y, ωSup c x y = ωSup (c.map ⟨fun n ↦ n x y, fun ⦃_ _⦄ a ↦ a x y⟩) := fun c x y ↦ by
      simp [ωSup]; rfl
    simp [ωSup_apply, add_ωSup, Chain.map, OrderHom.comp]
    congr! with n
    simp
  ωScottContinuous_mul_right x := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    exists fun a b h ↦ mul_le_mul_right' h x
    intro c
    ext i j
    simp [mul_apply, ωSup_apply, ωSup_mul, sum_ωSup', Chain.map, OrderHom.comp]
    congr! with n
    simp [mul_apply]
  ωScottContinuous_mul_left x := by
    refine ωScottContinuous.of_monotone_map_ωSup ?_
    exists fun a b h ↦ mul_le_mul_left' h x
    intro c
    ext i j
    simp [mul_apply, ωSup_apply, mul_ωSup, sum_ωSup', Chain.map, OrderHom.comp]
    congr! with n
    simp [mul_apply]

end

instance {n α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α] [Listed n]
    [LawfulStar (NMatrix (Listed.size n) (Listed.size n) α)] :
    LawfulStar (EMatrix n n α) := inferInstanceAs (LawfulStar (NMatrix _ _ α))

instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α]
    {n : ℕ} [LawfulStar (NMatrix n n α)] :
    LawfulStar (Matrix (Fin n) (Fin n) α) where
  star_eq_sum m := by
    convert congrArg NMatrix.asMatrix (LawfulStar.star_eq_sum (.ofMatrix m)); ext; simp

instance {α : Type*} [Semiring α] [OmegaCompletePartialOrder α] [OrderBot α]
    [IsPositiveOrderedAddMonoid α] [WeightedNetKAT.Star α]
    {n : Type*} [Listed n] [DecidableEq n] [Fintype n]
    [LawfulStar (NMatrix (Listed.size n) (Listed.size n) α)] :
    LawfulStar (Matrix n n α) where
  star_eq_sum m := by
    convert congrArg EMatrix.asMatrix (LawfulStar.star_eq_sum (.ofMatrix m)); ext; simp

end Matrix.Star
