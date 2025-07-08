import WeightedNetKAT.Language
import WeightedNetKAT.FinsuppExt
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis

@[simp]
theorem List.take_length_succ {α : Type*} (A : List α) : List.take (A.length + 1) A = A := by
  simp only [List.take_eq_self_iff, le_add_iff_nonneg_right, zero_le]

namespace WeightedNetKAT

variable {F : Type*} [Fintype F] [DecidableEq F]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {𝒮 : Type*} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

-- class WeightedProduct (α : Type*) (β : Type*) (γ : outParam Type*) where
--   wProd : α → β → γ

-- infixl:70 " * " => Matrix.mul_apply

-- instance {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮] :
--     WeightedProduct ((X × Y) →₀ 𝒮) (Matrix Y Z 𝒮) ((X × Z) →₀ 𝒮) where
--   wProd m m' :=
--     ⟨(m.support.biUnion (fun (x, y) ↦
--       m'.support
--         |>.image (fun (y', z) ↦ if y = y' ∧ m ⟨x, y⟩ * m' (y, z) ≠ 0 then some (x, z) else none)
--         |>.filterMap (·) (fun _ _ _ ↦ Option.eq_of_mem_of_mem))),
--       (fun (x, z) ↦ ∑ p ∈ m.support, let (x', y) := p; if x = x' then m ⟨x, y⟩ * m' (y, z) else 0),
--       (by
--         simp only [Prod.mk.eta, ne_eq, Finset.mem_biUnion, Finsupp.mem_support_iff,
--           Finset.mem_filterMap, Finset.mem_image, Prod.exists, exists_eq_right,
--           Option.ite_none_right_eq_some, Option.some.injEq, Finset.sum_eq_zero_iff,
--           ite_eq_right_iff, Prod.forall, not_forall, Prod.mk.injEq, existsAndEq, and_true, true_and]
--         intro x z
--         constructor
--         · simp only [exists_prop, forall_exists_index, and_imp]
--           rintro _ y hxy hyz h' ⟨_⟩
--           use x, y
--         · simp
--           intro y hxy h'
--           use x, y
--           simp_all
--           contrapose! h'
--           simp [h'])⟩

-- def 𝒞.wProd_id {𝒮 X : Type*} [Fintype X] [DecidableEq X] [Semiring 𝒮] [DecidableEq 𝒮] : Matrix X X 𝒮 :=
--   1
--   -- (fun x y ↦ if x = y then 1 else 0)

-- notation "1" => 𝒞.wProd_id

-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
-- @[simp]
-- theorem 𝒞.wProd_id_apply {X : Type*} [Fintype X] [DecidableEq X] [DecidableEq 𝒮] (x x' : X) :
--     (1 : Matrix X X 𝒮) x = if x.1 = x.2 then 1 else 0 := by
--   simp [𝒞.wProd_id]
--   split_ifs <;> simp_all

-- @[simp]
-- theorem Matrix.mul_apply {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
--     (a : (X × Y) →₀ 𝒮) :
--     (a * (0 : Matrix Y Z 𝒮)) = 0 := by
--   ext ⟨x, Z⟩; simp [Matrix.mul_apply]
-- @[simp]
-- theorem WeightedProduct.wZero_wProd {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
--     (a : Matrix Y Z 𝒮) :
--     ((0 : (X × Y) →₀ 𝒮) * a) = 0 := by
--   ext ⟨x, Z⟩; simp [Matrix.mul_apply]

-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
-- @[simp]
-- theorem 𝒞.wOne_finSupp {Y : Type*} [DecidableEq Y] [Fintype Y] [DecidableEq 𝒮] :
--     (1 : (Y × Y) →₀ 𝒮).support = if (1 : 𝒮) = 0 then ∅ else Fintype.elems.map ⟨fun a ↦ (a, a), by intro; simp⟩ := by
--   ext ⟨x, y⟩
--   simp only [Finsupp.mem_support_iff, wProd_id_apply, ne_eq, ite_eq_right_iff, Classical.not_imp]
--   split_ifs with h
--   · simp [h]
--   · simp [Fintype.complete, h]

-- @[simp]
-- theorem Matrix.mul_apply_wOne {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype Y] [DecidableEq 𝒮]
--     (a : (X × Y) →₀ 𝒮) :
--     (a * (1 : (Y × Y) →₀ 𝒮)) = a := by
--   ext ⟨x, y⟩; simp [Matrix.mul_apply]
--   rw [Finset.sum_eq_single ⟨x, y⟩]
--   · simp only [↓reduceIte]
--   · grind only [cases eager Prod, cases Or]
--   · grind only [Finsupp.mem_support_iff]
-- @[simp]
-- theorem WeightedProduct.wOne_wProd {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [DecidableEq 𝒮]
--     (a : (X × Y) →₀ 𝒮) :
--     ((1 : (X × X) →₀ 𝒮) * a) = a := by
--   ext ⟨x, y⟩; simp [Matrix.mul_apply]
--   split_ifs with h
--   · simp; symm; apply eq_zero_of_zero_eq_one h.symm
--   · rw [Finset.sum_eq_single ⟨x, x⟩]
--     · simp only [↓reduceIte]
--     · grind only [Function.Embedding.coeFn_mk, Prod.mk.injEq, Finset.mem_map, Fintype.complete,
--       ite_eq_right_iff, cases eager Prod]
--     · simp only [Finset.mem_map_mk, Fintype.complete, not_true_eq_false, ↓reduceIte,
--       IsEmpty.forall_iff]

-- theorem Matrix.mul_assoc {X Y Z W : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] [DecidableEq 𝒮]
--     (a : (X × Y) →₀ 𝒮)
--     (b : Matrix Y Z 𝒮)
--     (c : (Z × W) →₀ 𝒮) :
--     (a * b * c) = (a * (b * c)) := by
--   ext ⟨x, w⟩
--   simp only [wProd, Prod.mk.eta, ne_eq, Finsupp.coe_mk, Finset.sum_mul, ite_mul, zero_mul,
--     Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ite_eq_right_iff, Prod.forall, not_forall]
--   simp only [Finset.ite_sum_zero]
--   rw [Finset.sum_comm]
--   congr! with ⟨x, y⟩ h
--   split_ifs
--   · subst_eqs
--     simp [Finset.mul_sum]
--     apply Finset.sum_bij_ne_zero (fun ⟨_, z⟩ _ _ ↦ ⟨y, z⟩)
--     · grind only [Prod.mk.injEq, Finsupp.mem_support_iff, Finset.mem_biUnion, zero_mul,
--       ite_eq_right_iff, mul_zero, cases eager Prod]
--     · grind only [Prod.mk.injEq, Finset.mem_filter, cases eager Prod]
--     · simp only [Finsupp.mem_support_iff, ne_eq, ite_eq_right_iff, Classical.not_imp, exists_prop,
--       Finset.mem_biUnion, Finset.mem_filterMap, Finset.mem_image, Prod.exists, exists_eq_right,
--       Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, existsAndEq, and_true,
--       true_and, and_imp, Prod.forall]
--       grind [mul_zero, zero_mul, mul_assoc]
--     · grind [Finset.mem_filter, mul_assoc, cases eager Prod]
--   · grind [ite_self, Finset.sum_const_zero]

-- theorem WeightedProduct.wHMul_wProd {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
--     (m : (X × Y) →₀ 𝒮) (m' : Matrix Y Z 𝒮) (w : 𝒮) :
--     w * (m * m') = w * m * m' := by
--   ext ⟨x, z⟩
--   simp [Matrix.mul_apply, Finset.mul_sum]
--   apply Finset.sum_bij_ne_zero (fun a _ _ ↦ a)
--   · simp only [Finsupp.mem_support_iff, ne_eq, ite_eq_right_iff, Classical.not_imp,
--     Finsupp.hMul_left_apply, and_imp, Prod.forall]
--     rintro x y hxy ⟨_⟩ h
--     contrapose! h
--     simp [h, ← mul_assoc]
--   · grind
--   · grind only [mul_assoc, Finsupp.hMul_left_apply, Finsupp.mem_support_iff, mul_zero, cases eager
--     Prod, cases Or]
--   · grind [mul_assoc, mul_zero]

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝒪 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F N 𝒮 Q: Type*)
    [Semiring 𝒮]
where
  /-- `ι` is the initial weightings. -/
  ι : Matrix Unit Q 𝒮
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F,N]) → Matrix Q Q 𝒮
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : (α β : Pk[F,N]) → Matrix Q Unit 𝒮
notation "WNKA[" f "," n "," s "," q "]" => WNKA (F:=f) (n:=n) (𝒮:=s) (Q:=q)

inductive StateSpace where
  | Heart
  | Club
deriving DecidableEq, Fintype

notation "♡" => StateSpace.Heart
notation "♣" => StateSpace.Club

def S : RPol[F,N,𝒮] → Type
  | wnk_rpol {drop} => I {♡}
  | wnk_rpol {skip} => I {♡}
  | wnk_rpol {@test ~_} => I {♡}
  | wnk_rpol {@mod ~_} => I {♡}
  | wnk_rpol {dup} => I {♡, ♣}
  | wnk_rpol {~_ ⨀ ~p₁} => S p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁ ; ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁*} => S p₁ ⊕ I {♡}
where I : (Set StateSpace) → Type := (↑·)

attribute [simp] S.I

def S.decidableEq (p : RPol[F,N,𝒮]) : DecidableEq (S p) :=
  match p with
  | wnk_rpol {drop} => Subtype.instDecidableEq
  | wnk_rpol {skip} => Subtype.instDecidableEq
  | wnk_rpol {@test ~_}
  | wnk_rpol {@mod ~_} => Subtype.instDecidableEq
  | wnk_rpol {dup} => Subtype.instDecidableEq
  | wnk_rpol {~_ ⨀ ~p₁} => S.decidableEq p₁
  | wnk_rpol {~p₁ ⨁ ~p₂}
  | wnk_rpol {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_rpol {~p₁*} =>
    letI := S.decidableEq p₁
    letI : DecidableEq (I {♡}) := Subtype.instDecidableEq
    instDecidableEqSum

instance S.instDecidableEq {p : RPol[F,N,𝒮]} : DecidableEq (S p) := S.decidableEq p
instance : DecidableEq (S.I {♡}) := Subtype.instDecidableEq

def S.ι {X Y : Type*} : (Matrix Unit X 𝒮) → (Matrix Unit Y 𝒮) → (Matrix Unit (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "ι[" a "," b"]" => S.ι a b
def S.𝒪 {X Y : Type*} : (Matrix X Unit 𝒮) → (Matrix Y Unit 𝒮) → (Matrix (X ⊕ Y) Unit 𝒮) :=
  fun m₁ m₂ ↦ fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "𝒪[" a "," b"]" => S.𝒪 a b
attribute [grind] Prod.map Function.Injective in
def S.δ {X Y Z W : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] :
    (Matrix X Y 𝒮) →
    (Matrix X W 𝒮) →
    (Matrix Z Y 𝒮) →
    (Matrix Z W 𝒮) →
    (Matrix (X ⊕ Z) (Y ⊕ W) 𝒮) :=
  fun mxy mxw mzy mzw ↦
    (fun xz yw ↦
      xz.elim (fun x ↦ yw.elim (mxy x ·) (mxw x ·))
              (fun z ↦ yw.elim (mzy z ·) (mzw z ·)))

notation "δ[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.δ a b c d

instance : Fintype (S.I {♡}) := ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩

instance S.fintype (p : RPol[F,N,𝒮]) : Fintype (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    inferInstanceAs (Fintype (S.I {♡}))
  | wnk_rpol {dup} => ⟨{⟨♡, by simp⟩, ⟨♣, by simp⟩}, by rintro ⟨_, (h | h | h)⟩ <;> simp_all⟩
  | wnk_rpol {~_ ⨀ ~p₁} => S.fintype p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁*} => letI := S.fintype p₁; instFintypeSum _ _
instance S.instFintype {p : RPol[F,N,𝒮]} : Fintype (S p) := S.fintype p
instance S.Finite {p : RPol[F,N,𝒮]} : Finite (S p) := Finite.of_fintype (S p)

variable [DecidableEq 𝒮]

-- @[simp]
-- theorem 𝒞.unit_pair_wProd {m₁ m₂ : (Unit × Unit) →₀ 𝒮} : m₁ ((), ()) * m₂ ((), ()) = (m₁ * m₂) ((), ()) := by
--   simp [Matrix.mul_apply]
--   rw [Finset.sum_eq_single ⟨(), ()⟩] <;> simp +contextual

abbrev η₁ {X : Type*} [DecidableEq X] (i : X) : X → 𝒮 :=
  fun i' ↦ if i = i' then 1 else 0
abbrev η₂ {X Y : Type*} [DecidableEq X] [DecidableEq Y] (i : X) (j : Y) : Matrix X Y 𝒮 :=
  fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def ι (p : RPol[F,N,𝒮]) : Matrix Unit (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η₂ () ⟨♡, rfl⟩
  | wnk_rpol {dup} => η₂ () ⟨♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~p₂} => ι[ι p₁, 0]
  | wnk_rpol {~p₁*} => ι[0, fun () ↦ 1]

-- def 𝒞.pow {X : Type*} [Fintype X] [DecidableEq X] (m : (X × X) →₀ 𝒮) : ℕ → (X × X) →₀ 𝒮
--   | 0 => 1
--   | n+1 => 𝒞.pow m n * m

class FinsuppStar (𝒮 : Type*) [Semiring 𝒮] where
  wStar : {X : Type*} → [Fintype X] → [DecidableEq X] → (Matrix X X 𝒮) → Matrix X X 𝒮
postfix:max "^*" => FinsuppStar.wStar

instance {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    OmegaCompletePartialOrder (Matrix X Y 𝒮) := inferInstanceAs (OmegaCompletePartialOrder (X → Y → 𝒮))
instance {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    OrderBot (Matrix X Y 𝒮) := inferInstanceAs (OrderBot (X → Y → 𝒮))
instance {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    IsPositiveOrderedAddMonoid (Matrix X Y 𝒮) := inferInstanceAs (IsPositiveOrderedAddMonoid (X → Y → 𝒮))

class LawfulFinsuppStar (𝒮 : Type*)
    [Semiring 𝒮]
    [OmegaCompletePartialOrder 𝒮]
    [OrderBot 𝒮]
    [MulLeftMono 𝒮]
    [MulRightMono 𝒮]
    [IsPositiveOrderedAddMonoid 𝒮]
    [OmegaContinuousNonUnitalSemiring 𝒮]
    [DecidableEq 𝒮]
    [FinsuppStar 𝒮] where
  wStar_eq_sum :
    ∀ {X : Type*} [Fintype X] [DecidableEq X],
        ∀ m : Matrix X X 𝒮, m^* = ω∑ n, m^n

-- noncomputable instance :
--     [∀ {X : Type*} [Fintype X] [DecidableEq X], WeightedOmegaCompletePartialOrder ((X × X) →₀ 𝒮)]
--     [∀ {X : Type*} [Fintype X] [DecidableEq X], WeightedOmegaContinuousPreSemiring ((X × X) →₀ 𝒮)] :
--     FinsuppStar 𝒮 where
--   wStar m := ω∑ n, 𝒞.pow m n
--   wStar_eq_sum := by intro x _ _; use inferInstance, inferInstance; intro m; rfl

def 𝒞.left_to_unit {X : Type*} [DecidableEq X] (m : Matrix (S.I {♡}) X 𝒮) : Matrix Unit X 𝒮 :=
  fun () x ↦ m ⟨♡, rfl⟩ x
def 𝒞.left_to_heart {X : Type*} [DecidableEq X] (m : (Matrix Unit X 𝒮)) : Matrix (S.I {♡}) X 𝒮 :=
  fun ⟨♡, _⟩ x ↦ m () x

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem 𝒞.left_to_unit_apply {X : Type*} [DecidableEq X] (m : Matrix (S.I {♡}) X 𝒮) (x) (y) :
    𝒞.left_to_unit m x y = m ⟨♡, rfl⟩ y := rfl
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem 𝒞.left_to_heart_apply {X : Type*} [DecidableEq X] (m : Matrix Unit X 𝒮) (x) (y) :
    𝒞.left_to_heart m x y = m () y := by simp [left_to_heart]; split; rfl

def 𝒞.transpose {X Y : Type*} [DecidableEq X] [DecidableEq Y] (m : (X × Y) →₀ 𝒮) : (Y × X) →₀ 𝒮 :=
  ⟨(m.support.image (fun (y, x) ↦ (x, y))), (fun (y, x) ↦ m (x, y)), (by simp)⟩

universe u

class Star (α : Type*) where
  -- X Z Y W : Type u
  -- promote : α → ((X ⊕ Z) × (Y ⊕ W))
  -- β : match u with | 0 => Type | v+1 => Type v
  -- promote : α → β
  star : α → α
postfix:max "^**" => Star.star

variable [Star 𝒮]

instance instUnitStar : Star (Matrix Unit Unit 𝒮) where
  star m := fun α β ↦ (m α β)^**

instance instPkStar : Star (Matrix Pk[F,N] Pk[F,N] 𝒮) where
  star m := fun α β ↦ (m α β)^**

def mmm
  {n₁ n₂ : Type*}
  [Fintype n₁] [Fintype n₂]
  [DecidableEq n₁] [DecidableEq n₂]
  [Star (Matrix n₁ n₁ 𝒮)]
  [Star (Matrix n₂ n₂ 𝒮)]
  :
    Star (Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) 𝒮) where
  star m :=
    let a : Matrix n₁ n₁ 𝒮 := fun x y ↦ m (.inl x) (.inl y)
    let b : Matrix n₁ n₂ 𝒮 := fun x w ↦ m (.inl x) (.inr w)
    let c : Matrix n₂ n₁ 𝒮 := fun z y ↦ m (.inr z) (.inl y)
    let d : Matrix n₂ n₂ 𝒮 := fun z y ↦ m (.inr z) (.inr y)
    let δ : Matrix n₂ n₂ 𝒮 := (d + c * a^** * b)^**
    let γ : Matrix n₂ n₁ 𝒮 := δ * c * a^**
    let β : Matrix n₁ n₂ 𝒮 := a^** * b * δ
    let α : Matrix n₁ n₁ 𝒮 := a^** + a^** * b * δ * c * a^**
    δ[[α,β],[γ,δ]]


-- def my_star {X Y Z W : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (m : ((X ⊕ Z) × (Y ⊕ W)) →₀ 𝒮) :
--     ((X ⊕ Z) × (Y ⊕ W)) →₀ 𝒮 :=
--   let a : (X × Y) →₀ 𝒮 := ⟨sorry, fun (x, y) ↦ m (.inl x, .inl y), sorry⟩
--   let b : (X × W) →₀ 𝒮 := ⟨sorry, fun (x, w) ↦ m (.inl x, .inr w), sorry⟩
--   let c : (Z × Y) →₀ 𝒮 := ⟨sorry, fun (z, y) ↦ m (.inr z, .inl y), sorry⟩
--   let d : (Z × W) →₀ 𝒮 := ⟨sorry, fun (z, y) ↦ m (.inr z, .inr y), sorry⟩
--   let δ := (d + c * my_star a * b)
--   sorry

def 𝒪 [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) (α β : Pk[F,N]) : Matrix (S p) Unit 𝒮 :=
  match p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} => if α = β then fun _ ↦ 1 else 0
  | wnk_rpol {@test ~γ} => if α = β ∧ β = γ then fun _ ↦ 1 else 0
  | wnk_rpol {@mod ~π} => if β = π then fun _ ↦ 1 else 0
  | wnk_rpol {dup} => if α = β then η₂ ⟨♣, by simp⟩ () else 0
  | wnk_rpol {~_ ⨀ ~p₁} => 𝒪 p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} => 𝒪[𝒪 p₁ α β, 𝒪 p₂ α β]
  | wnk_rpol {~p₁ ; ~p₂} => 𝒪[∑ γ, (𝒪 p₁ α γ * ι p₂ * 𝒪 p₂ γ β), 𝒪 p₂ α β]
  | wnk_rpol {~p₁*} =>
    let q : Matrix Unit Unit 𝒮 := 𝒪_heart p₁
    𝒪[
      𝒪 p₁ α β * q,
      𝒞.left_to_heart q
    ]
where 𝒪_heart (p₁ : RPol[F,N,𝒮]) := (ι p₁ * 𝒪 p₁ α β)^**
      -- 𝒪_heart' (p₁ : RPol[F,N,𝒮]) := (box' p₁)^**
      -- box' (p₁ : RPol[F,N,𝒮]) : (Pk[F,N] × Pk[F,N]) →₀ 𝒮 :=
      --   ((⟨Finset.univ.filter (fun (α, β) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()) ≠ 0),
      --     fun (α, β) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()), by simp⟩) : (Pk[F,N] × Pk[F,N]) →₀ 𝒮)
      -- box (p₁ : RPol[F,N,𝒮]) : (Pk[F,N] × Pk[F,N]) → S.I {♡} × Unit →₀ 𝒮 :=
      --   (fun (α, β) ↦ (⟨Finset.univ.filter (fun (_, _) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()) ≠ 0),
      --     fun (_, _) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()), by simp; sorry⟩) : (Pk[F,N] × Pk[F,N]) → S.I {♡} × Unit →₀ 𝒮)
      -- 𝒪_heart' (p₁ : RPol[F,N,𝒮]) : (Pk[F,N] × Pk[F,N]) → S.I {♡} × Unit →₀ 𝒮 := (box p₁)^**
      -- 𝒪_heart' (p₁ : RPol[F,N,𝒮]) : (Pk[F,N] × Pk[F,N]) → S.I {♡} × Unit →₀ 𝒮 :=
      --   (fun (α, β) ↦ (⟨Finset.univ.filter (fun (_, _) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()) ≠ 0),
      --     fun (_, _) ↦ (ι p₁ * 𝒪 p₁ α β) ((), ()), by simp⟩) : (Pk[F,N] × Pk[F,N]) → S.I {♡} × Unit →₀ 𝒮)^**

def δ [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) (α β : Pk[F,N]) : Matrix (S p) (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    0
  | wnk_rpol {dup} => fun s ↦ if s.val = ♡ ∧ α = β then η₁ ⟨♣, by simp⟩ else 0
  | wnk_rpol {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
      δ[[δ p₁ α β,    0],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁ ; ~p₂} =>
      δ[[δ p₁ α β,    ∑ γ, (𝒪 p₁ α γ * ι p₂ * δ p₂ γ β)],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁*} =>
    δ[[δ p₁ α β, 0],
      [𝒞.left_to_heart (𝒪_heart p₁ * ι p₁) * δ p₁ α β, 0]]
where δ₁ (p₁ : RPol[F,N,𝒮]) := δ p₁ α β + (𝒪 p₁ α β * 𝒪_heart p₁ * ι p₁ * δ p₁ α β)
      𝒪_heart (p₁ : RPol[F,N,𝒮]) := (ι p₁ * 𝒪 p₁ α β)^*

example {a : Prop} : ¬¬a ↔ a := by exact not_not

def RPol.wnka [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] where
  ι := ι p
  δ := δ p
  𝒪 := 𝒪 p

@[simp] theorem RPol.wnka_ι [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) : p.wnka.ι = ι p := rfl
@[simp] theorem RPol.wnka_δ [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) : p.wnka.δ = δ p := rfl
@[simp] theorem RPol.wnka_𝒪 [FinsuppStar 𝒮] (p : RPol[F,N,𝒮]) : p.wnka.𝒪 = 𝒪 p := rfl

def big_wprod {X : Type*} [Fintype X] [DecidableEq X] (l : List ((X × X) →₀ 𝒮)) : (X × X) →₀ 𝒮 :=
  l.foldl (· * ·) 1

def WNKA.compute' {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    Matrix Q Q 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => 1
  | α::α'::s => 𝒜.δ α α' * 𝒜.compute' (α' :: s)

def WNKA.compute'_right {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) {α α'} :
    𝒜.compute' (s ++ [α, α']) = (𝒜.compute' (s ++ [α]) * 𝒜.δ α α') := by
  induction s with
  | nil => simp [compute']
  | cons α₀ s ih =>
    simp
    rcases s with _ | ⟨α₁, s⟩
    · simp [compute']
    · simp [compute']
      simp at ih
      rw [ih]
      simp [Matrix.mul_assoc]

def WNKA.compute {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    Matrix Q Unit 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => fun _ ↦ 1
  | [α, α'] => 𝒜.𝒪 α α'
  | α::α'::s => 𝒜.δ α α' * 𝒜.compute (α' :: s)

-- def WNKA.compute_cons_append {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α α' : Pk[F,N]) :
--     𝒜.compute (α :: A ++ [α']) =  (𝒜.compute' A * 𝒜.𝒪 α' α'') := by
--   induction A generalizing α with
--   | nil => simp [compute, compute']
--   | cons α₀ A ih =>
--     simp [compute, compute']
--     simp at ih
--     rw [ih α₀]
--     rcases A with _ | ⟨α₁, A⟩
--     · simp_all [compute, compute']
--     · simp [compute, compute']
--       simp at ih
--       rw [ih]
--       simp [Matrix.mul_assoc]

def WNKA.compute_pair {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α' α'' : Pk[F,N]) :
    𝒜.compute (A ++ [α', α'']) = (𝒜.compute' (A ++ [α']) * 𝒜.𝒪 α' α'') := by
  induction A with
  | nil => grind [List.nil_append, compute, compute', Matrix.one_mul]
  | cons α₀ A ih =>
    rcases A with _ | ⟨α₁, A⟩
    · grind [List.nil_append, List.append_nil, List.cons_append, compute, compute', mul_one]
    · grind only [List.append_eq_nil_iff, List.cons_append, → List.eq_nil_of_append_eq_nil,
        compute', Matrix.mul_assoc, compute]

def WNKA.compute_pair' {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α₀ α' α'' : Pk[F,N]) :
    𝒜.compute (α₀ :: (A ++ [α', α''])) = (𝒜.compute' (α₀ :: (A ++ [α'])) * 𝒜.𝒪 α' α'') := by
  rw [← List.cons_append, WNKA.compute_pair]; rfl

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem WNKA.compute_eq_of {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) (h𝒪 : 𝒜.𝒪 = 𝒜'.𝒪) :
    𝒜.compute s = 𝒜'.compute s := by
  induction s with
  | nil => simp [compute]
  | cons x s ih =>
    induction s with
    | nil => simp [compute]
    | cons y s ih =>
      unfold compute
      split <;> try rfl
      · simp [h𝒪]
      · simp [hδ]; grind

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem WNKA.compute'_eq_of {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) :
    𝒜.compute' s = 𝒜'.compute' s := by
  induction s with
  | nil => simp [compute']
  | cons x s ih =>
    induction s with
    | nil => simp [compute']
    | cons y s ih =>
      unfold compute'
      simp [ih, hδ]

def WNKA.sem {Q : Type*} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨(fun x ↦ (𝒜.ι * 𝒜.compute x.pks) () ()), SetCoe.countable _⟩

-- def asdasd_supp {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (x : X) (y : Y) (m : Matrix Y Z 𝒮) :=
--   (η₂ (𝒮:=𝒮) x y * m).support

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
@[simp]
theorem asdasd {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [Fintype X] [Fintype Y] (x : X) (y : Y) (m : Matrix Y Z 𝒮) :
      (η₂ (𝒮:=𝒮) x y * m)
    = ((fun α β ↦ if α = x then m y β else 0) : Matrix X Z 𝒮) := by
  ext
  unfold η₂
  simp [Matrix.mul_apply]
  rw [Finset.sum_eq_single y]
  · grind
  · grind
  · simp

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.induction (P : GS[F,N] → Prop)
    (h₀ : ∀ α α₀, P gs[α; α₀])
    (h₁ : ∀ α α₀ α₁, P gs[α; α₀; dup; α₁])
    (hn : ∀ α α₀ α₁ A αₙ, P (GS.mk α (α₀ :: α₁ :: A) αₙ))
    (x : GS[F,N]) :
    P x := by
  obtain ⟨α, A, αn⟩ := x
  match A with
  | [] => exact h₀ α αn
  | [α'] => exact h₁ α α' αn
  | α' :: α'' :: A => exact hn α α' α'' A αn

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.induction' (P : GS[F,N] → Prop)
    (h₀ : ∀ α α₀, P gs[α; α₀])
    (hn : ∀ α α₀ A αₙ, P (GS.mk α (A ++ [α₀]) αₙ))
    (x : GS[F,N]) :
    P x := by
  obtain ⟨α, A, αₙ⟩ := x
  match A with
  | [] => exact h₀ α αₙ
  | α' :: A =>
    simp [mk] at hn
    obtain ⟨A', α₀, h⟩ : ∃ A' α₀, α' :: A = A' ++ [α₀] := by
      use (α'::A).dropLast, (α'::A).getLast (by simp)
      if hA : A = [] then
        subst_eqs
        simp
      else
        simp [hA, List.dropLast_cons_of_ne_nil, List.getLast_cons, List.dropLast_concat_getLast]
    grind

-- @[simp]
-- theorem WeightedFinsum_map {α ι γ : Type*} [DecidableEq γ] [DecidableEq ι] [WeightedPreSemiring α] (I : Finset ι) (g : ι ↪ γ) (f : γ → α) :
--     (∑ i ∈ I.map g, f i) = ∑ i ∈ I, f (g i) := by
--   simp [WeightedFinsum_eq_finset_sum]

-- @[simp]
-- theorem WeightedFinsum_disjSum {α ι γ : Type*} [DecidableEq γ] [DecidableEq ι] [WeightedPreSemiring α] (I : Finset ι) (J : Finset γ) (f : ι ⊕ γ → α) :
--     (∑ i ∈ I.disjSum J, f i) = (∑ i ∈ I, f (.inl i)) ⨁ ∑ j ∈ J, f (.inr j) := by
--   simp [WeightedFinsum_eq_finset_sum]
--   rfl

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem ι_wProd_𝒪 {A B : Type*} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    {X : Matrix Unit A 𝒮} {Y : Matrix Unit B 𝒮} {Z : Matrix A Unit 𝒮} {W : Matrix B Unit 𝒮} :
    (ι[X, Y] * 𝒪[Z, W]) = (X * Z) + (Y * W) := by
  ext i j
  simp [Matrix.mul_apply, S.ι, S.𝒪]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem ι_wProd_δ {A B C D : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix Unit A 𝒮} {Y : Matrix Unit B 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (ι[X, Y] * δ[[Z, W], [U, V]]) = ι[X * Z, X * W] + ι[Y * U, Y * V] := by
  ext _ a
  simp [S.ι, S.δ, Matrix.mul_apply]
  rcases a with c | d
  · simp
  · simp
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem ι_wProd_δ' {A B C D : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix Unit A 𝒮} {Y : Matrix Unit B 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (ι[X, Y] * δ[[Z, W], [U, V]]) = ι[X * Z + Y * U, X * W + Y * V] := by
  ext _ a
  simp [Matrix.mul_apply, S.ι, S.δ]
  rcases a with c | d <;> simp
theorem δ_wProd_δ {A B C D E F : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq E] [DecidableEq F]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    {A₁₁ : Matrix A C 𝒮} {A₁₂ : Matrix A D 𝒮}
    {A₂₁ : Matrix B C 𝒮} {A₂₂ : Matrix B D 𝒮}
    {B₁₁ : Matrix C E 𝒮} {B₁₂ : Matrix C F 𝒮}
    {B₂₁ : Matrix D E 𝒮} {B₂₂ : Matrix D F 𝒮}
    :
      (δ[[A₁₁, A₁₂], [A₂₁, A₂₂]] * δ[[B₁₁, B₁₂], [B₂₁, B₂₂]])
    = δ[[A₁₁ * B₁₁ + A₁₂ * B₂₁, A₁₁ * B₁₂ + A₁₂ * B₂₂],
        [A₂₁ * B₁₁ + A₂₂ * B₂₁, A₂₁ * B₁₂ + A₂₂ * B₂₂]] := by
  ext ab ef
  rcases ab with a | b
  · rcases ef with e | f
    · simp only [Matrix.mul_apply, S.δ, Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr,
      Matrix.add_apply]
    · simp only [Matrix.mul_apply, S.δ, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type,
      Matrix.add_apply]
  · rcases ef with e | f
    · simp only [Matrix.mul_apply, S.δ, Sum.elim_inr, Sum.elim_inl, Fintype.sum_sum_type,
      Matrix.add_apply]
    · simp only [Matrix.mul_apply, S.δ, Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl,
      Matrix.add_apply]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem δ_wProd_𝒪 {A B C D : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix C Unit 𝒮} {Y : Matrix D Unit 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (δ[[Z, W], [U, V]] * 𝒪[X, Y]) = 𝒪[Z * X + W * Y, U * X + V * Y] := by
  ext a _
  simp [Matrix.mul_apply, S.𝒪, S.δ]
  rcases a with c | d <;> simp

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
@[simp]
theorem S.δ_identity {A B : Type*} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B] :
    (δ[[1,0],[0,1]] : Matrix (A ⊕ B) (A ⊕ B) 𝒮) = 1 := by
  ext ab₁ ab₂
  rcases ab₁ with a₁ | b₁ <;> rcases ab₂ with a₂ | b₂ <;> simp [S.δ, Matrix.one_apply]

-- theorem wProd_left_distrib {A B C : Type*}
--     [DecidableEq A] [DecidableEq B] [DecidableEq C]
--     [Fintype A] [Fintype B] [Fintype C]
--     {AB : Matrix A B 𝒮} {BC : Matrix B C 𝒮} {BC' : Matrix B C 𝒮} :
--     AB * (BC + BC') = (AB * BC) + (AB * BC') := by
--   ext ⟨a, c⟩
--   simp
--   simp [Matrix.mul_apply]
--   simp [← Finset.sum_add_distrib]
--   congr with ⟨a', b⟩
--   simp
--   split_ifs
--   · subst_eqs; simp [left_distrib]
--   · simp
-- theorem ite_wAdd {α : Type*} [NonUnitalSemiring α] {p : Prop} [Decidable p] {a b : α} :
--     (if p then a + b else 0) = (if p then a else 0) + if p then b else 0 := by
--   split_ifs
--   · rfl
--   · simp
-- theorem wProd_right_distrib {A B C : Type*}
--     [DecidableEq A] [DecidableEq B] [DecidableEq C]
--     {AB : Matrix A B 𝒮} {AB' : Matrix A B 𝒮} {BC : Matrix B C 𝒮} :
--     (AB + AB') * BC = (AB * BC) + (AB' * BC) := by
--   ext ⟨a, c⟩
--   simp only [Matrix.mul_apply, Prod.mk.eta, Finsupp.coe_add, Pi.add_apply, right_distrib,
--     ne_eq, add_eq_zero, not_and, ite_wAdd, Finset.sum_add_distrib, Finsupp.coe_mk]
--   congr! 1
--   · apply Finset.sum_bij_ne_zero (fun a _ _ ↦ a)
--     · simp; grind [mul_zero, zero_mul]
--     · simp
--     · simp; grind [mul_zero, zero_mul]
--     · simp
--   · apply Finset.sum_bij_ne_zero (fun a _ _ ↦ a)
--     · simp; grind [mul_zero, zero_mul]
--     · simp
--     · simp; grind [mul_zero, zero_mul]
--     · simp

-- theorem Matrix.mul_sum {ι A B C : Type*}
--     [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C]
--     [Fintype ι] [Fintype A] [Fintype B] [Fintype C]
--     (AB : Matrix A B 𝒮) (fBC : ι → Matrix B C 𝒮) (S : Finset ι) :
--     (AB * ∑ i ∈ S, fBC i) = ∑ i ∈ S, AB * fBC i := by
--   exact Matrix.mul_sum S fBC AB
--   induction S using Finset.induction with
--   | empty => simp
--   | insert i S hi ih => simp_all [wProd_left_distrib]

-- theorem Matrix.sum_mul {ι A B C : Type*} [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C]
--     (BC : Matrix B C 𝒮) (fAB : ι → Matrix A B 𝒮) (S : Finset ι) :
--     ((∑ i ∈ S, fAB i) * BC) = ∑ i ∈ S, (fAB i * BC) := by
--   induction S using Finset.induction with
--   | empty => simp
--   | insert i S hi ih => simp_all [wProd_right_distrib]

def GS.ofPks (l : List Pk[F,N]) (h : 2 ≤ l.length) : GS[F,N] :=
  GS.mk (l.head (List.ne_nil_of_length_pos (by omega))) (l.drop 1).dropLast (l.getLast (List.ne_nil_of_length_pos (by omega)))

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
@[simp] theorem GS.ofPks_pks (l : List Pk[F,N]) (h : 2 ≤ l.length) : (GS.ofPks l h).pks = l := by
  simp [ofPks, pks, GS.mk]
  apply List.ext_getElem
  · simp; omega
  · simp
    intro i h₁ h₂
    rcases i with _ | i
    · simp; apply List.head_eq_getElem
    · simp [List.getElem_append]
      split_ifs
      · rfl
      · grind

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.eq_iff_pks_eq (g₁ g₂ : GS[F,N]) : g₁ = g₂ ↔ g₁.pks = g₂.pks := by
  simp only [pks, List.cons_append, List.cons.injEq]
  obtain ⟨g₁₀, g₁, g₁₁⟩ := g₁
  obtain ⟨g₂₀, g₂, g₂₁⟩ := g₂
  constructor
  · grind
  · intro h
    obtain ⟨h₀, h₁⟩ := h
    have := congrArg List.length h₁
    grind only [List.length_cons, List.length_nil, List.append_inj, List.length_append, →
      List.eq_nil_of_append_eq_nil]

variable [FinsuppStar 𝒮]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem RPol.wnka_sem_pair (p : RPol[F,N,𝒮]) (α γ : Pk[F,N]) :
    p.wnka.sem (α, [], γ) = (ι p * 𝒪 p α γ) () () := rfl

theorem RPol.wnka_sem_eq_of (p : RPol[F,N,𝒮]) (f)
    (h₂ : ∀ (A : List Pk[F,N]) (α α' : Pk[F,N]), (ι p * p.wnka.compute' (A ++ [α]) * 𝒪 p α α') () () = f (GS.ofPks (A ++ [α, α']) (by simp))) :
    p.wnka.sem = f := by
  ext g
  obtain ⟨g₀, g, g₁⟩ := g
  if g = [] then
    subst_eqs
    simp [wnka, WNKA.sem, GS.pks, WNKA.compute]
    have := h₂ [] g₀ g₁
    simp [WNKA.compute'] at this
    assumption
  else
    obtain ⟨A, α, α', h⟩ : ∃ A α α', GS.mk g₀ g g₁ = GS.ofPks (A ++ [α, α']) (by simp) := by
      conv =>
        arg 1; ext; arg 1; ext; arg 1; ext
        rw [GS.eq_iff_pks_eq]
      simp [GS.mk]
      simp [GS.pks]
      set A := g₀ :: (g ++ [g₁])
      use A.take (A.length - 2),
          A[A.length - 2]'(by simp [A]; omega),
          A[A.length - 1]'(by simp [A])
      apply List.ext_getElem
      · simp; grind
      · intro i h₀ h₁
        simp [List.getElem_append, List.getElem_cons]
        intro h₂
        split_ifs
        · congr; omega
        · congr; grind
        · omega
    simp [GS.mk] at h
    rw [h]
    simp [wnka, WNKA.sem, WNKA.compute_pair]
    simp [← Matrix.mul_assoc]
    exact h₂ A α α'

omit [DecidableEq 𝒮] in
theorem RPol.wnka_sem_drop :
    (RPol.wnka wnk_rpol {drop}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {drop} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪, Matrix.zero_apply]
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk,
      List.nil_append, WNKA.compute, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
  next α A αn =>
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, δ, GS.pks]
omit [DecidableEq 𝒮] in
theorem RPol.wnka_sem_skip :
    (RPol.wnka wnk_rpol {skip}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {skip} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝒪, ι, GS.pks]
    split_ifs with h₁ h₂ h₃ <;> subst_eqs
    · rfl
    · simp at h₂
    · obtain ⟨_, _, _⟩ := h₃
      contradiction
    · rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, ι, δ, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, Matrix.zero_mul, Matrix.zero_apply,
      right_eq_ite_iff, forall_exists_index]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff, forall_exists_index]
    grind
theorem RPol.wnka_sem_test {t} :
    (RPol.wnka wnk_rpol {@test ~t}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {@test ~t} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝒪, ι, GS.pks]
    split_ifs
    · rfl
    · grind only
    · grind only
    · rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk,
      List.nil_append, WNKA.compute, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply,
      right_eq_ite_iff]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff]
    grind
omit [DecidableEq 𝒮] in
theorem RPol.wnka_sem_mod {π} :
    (RPol.wnka wnk_rpol {@mod ~π}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {@mod ~π} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝒪, ι, GS.pks]
    split_ifs with h₁ h₂ h₃ <;> simp_all
    grind
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk,
      List.nil_append, WNKA.compute, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply,
      right_eq_ite_iff, forall_exists_index]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff, forall_exists_index]
    grind
-- -- TODO: remove
-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [FinsuppStar 𝒮] in
-- @[simp]
-- theorem 𝒞.ite_apply {X : Type*} (p : Prop) [Decidable p] (m₁ m₂ : X →₀ 𝒮) (x : X) :
--     (if p then m₁ else m₂) x = (if p then m₁ x else m₂ x) := by grind
omit [DecidableEq 𝒮] in
theorem RPol.wnka_compute'_dup {A : List Pk[F,N]} :
      wnk_rpol {dup}.wnka.compute' (𝒮:=𝒮) A
    = match A with
      | [] | [_] => 1
      | [α, β] => if α = β then η₂ ⟨♡, by simp⟩ ⟨♣, by simp⟩ else 0
      | _ => 0
    := by
  induction A with
  | nil => simp [WNKA.compute']
  | cons α₁ A ih₁ =>
    induction A with
    | nil => simp [WNKA.compute']
    | cons α₂ A ih₂ =>
      simp_all [WNKA.compute']; clear ih₁ ih₂
      split
      next => grind
      next A' α₃ h =>
        simp_all [δ]
        ext ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
        simp only
        split_ifs
        · simp only [η₁, η₂]
          grind [mul_zero, zero_mul, δ, Finsupp.η'_apply]
        · simp_all only [and_false]
        · simp_all only [and_true, Pi.zero_apply, right_eq_ite_iff, and_imp]
          grind
        · simp_all
      next A' α₃ α₄ h =>
        simp_all; clear h
        rintro ⟨_⟩
        ext ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
        simp_all only [δ, Matrix.mul_apply, mul_ite, mul_one, mul_zero, Matrix.zero_apply,
          Finset.sum_eq_zero_iff, Finset.mem_univ, ite_eq_right_iff, and_imp, forall_const,
          forall_eq']
        rintro ⟨_⟩
        split_ifs
        · grind
        · rfl
      next => simp_all

theorem RPol.wnka_sem_dup :
    (RPol.wnka wnk_rpol {dup}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {dup} := by
  apply wnka_sem_eq_of
  intro A α β
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  rw [RPol.wnka_compute'_dup]
  split
  next => grind only [=_ List.cons_append, List.length_append, → List.eq_nil_of_append_eq_nil]
  next α₀ =>
    have : A = [] := by
      contrapose! α₀
      intro h
      have := congrArg List.length h
      simp at this
      contradiction
    simp_all
    subst_eqs
    simp [G, GS.mk, GS.ofPks, ι, 𝒪, η₂]
    split_ifs
    · grind
    · grind
    · grind
    · rfl
  next α₀ α₁ h =>
    -- simp_all
    have : A = [α₀] := by
      rcases A
      · have := congrArg List.length h
        simp at this
      · have := congrArg List.length h
        simp at this
        subst_eqs
        rfl
    subst_eqs
    simp [G, GS.mk, GS.ofPks]
    if α₀ = α then
      subst_eqs
      simp
      simp [𝒪]
      split_ifs
      · subst_eqs
        simp_all [ι, Matrix.mul_apply]
        rw [Finset.sum_eq_single ⟨♣, by simp⟩]
        · simp
        · grind
        · simp only [Finset.mem_univ, not_true_eq_false, and_self, ↓reduceIte, ite_eq_right_iff,
          forall_const, IsEmpty.forall_iff]
      · simp_all
      · grind
      · simp_all
    else
      simp_all; grind
  next h =>
    simp_all [G, GS.mk, GS.ofPks]
    intro x
    contrapose! h
    use x, α
    suffices A = [x] by grind
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    simp at h
    have := congrArg List.length h.1.2.1
    simp at this
    rcases A with _ | ⟨α₀, A⟩
    · grind
    · grind only [List.length_cons, List.head_eq_getElem, List.append_eq_nil_iff, List.tail_append,
      List.head_append_of_ne_nil, → List.nil_of_isEmpty, List.getElem_cons_zero, =
      List.getElem_cons, List.getElem_append, List.cons_ne_self, List.cons_append,
      List.length_eq_zero_iff, List.cons.injEq, List.length_append, List.head_cons, →
      List.eq_nil_of_append_eq_nil, List.tail_cons, List.isEmpty_cons, List.head_append]

theorem RPol.wnka_sem_add {p₁ p₂ : RPol[F,N,𝒮]} :
    wnk_rpol {~p₁ ⨁ ~p₂}.wnka.sem = p₁.wnka.sem + p₂.wnka.sem := by
  ext S
  induction S using GS.induction'
  next α α₀ =>
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, ι, GS.pks, 𝒪]
    rw [ι_wProd_𝒪]
    simp
  next α α₀ α₁ A α₂ =>
    simp [WNKA.sem, GS.mk, GS.pks, ι, WNKA.compute_pair', 𝒪]
    generalize ι p₁ = ι₁
    generalize ι p₂ = ι₂
    generalize 𝒪 p₁ α₁ α₂ = 𝒪₁
    generalize 𝒪 p₂ α₁ α₂ = 𝒪₂
    generalize (α₀ :: (A ++ [α₁])) = A
    simp [← Matrix.mul_assoc]
    induction A generalizing ι₁ ι₂ with
    | nil =>
      simp [WNKA.compute']
      rw [ι_wProd_𝒪]
      simp
    | cons α A ih =>
      rcases A with _ | ⟨α', A⟩
      · simp [WNKA.compute']
        rw [ι_wProd_𝒪]
        rfl
      · simp [WNKA.compute', ← Matrix.mul_assoc, δ, ι_wProd_δ']
        rw [ih]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
theorem RPol.wnka_sem_weight {w} {p : RPol[F,N,𝒮]} :
    wnk_rpol {~w ⨀ ~p}.wnka.sem = (w * p.wnka.sem) := by
  ext x
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, Matrix.smul_mul, Matrix.smul_apply,
      smul_eq_mul, GS.mk, Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪,
      Countsupp.hMul_apply_left]
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, ι, δ, GS.pks, List.cons_append, Matrix.smul_mul, Matrix.smul_apply,
      smul_eq_mul, GS.mk, Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪, ← Matrix.mul_assoc,
      Countsupp.hMul_apply_left]
  next α A αn =>
    simp only [WNKA.sem, wnka, ι, δ, GS.pks, List.cons_append, Matrix.smul_mul, Matrix.smul_apply,
      smul_eq_mul, GS.mk, Countsupp.coe_mk, WNKA.compute, List.append_eq_nil_iff, List.cons_ne_self,
      and_false, imp_self, ← Matrix.mul_assoc, Countsupp.hMul_apply_left]
    congr! 2
    apply WNKA.compute_eq_of
    · rfl
    · ext; simp only [𝒪]

def GS.splitAtJoined (g : GS[F,N]) (n : ℕ) (γ : Pk[F,N]) : GS[F,N] × GS[F,N] :=
  let (g₀, g, gₙ)  := g
  let (l, r) := g.splitAt n
  ((g₀, l, γ), (γ, r, gₙ))

example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 0 γ = (gs[α;γ], gs[γ;α₁;dup;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 1 γ = (gs[α;α₁;dup; γ], gs[γ;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 2 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 3 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl

-- a;b;dup;c
--  ^     ^
-- a;γ ◇ γ;b;dup;c
-- a;b;dup;γ ◇ γ;c

omit [DecidableEq 𝒮] [FinsuppStar 𝒮] in
theorem G.concat_apply [Encodable F] [Encodable N] {p₁ p₂ : RPol[F,N,𝒮]} {xₙ : GS F N} :
      ((G p₁ ♢ G p₂) : _ →c 𝒮) xₙ
    = ∑ i ∈ Finset.range (xₙ.2.1.length + 1), ∑ (γ : Pk[F,N]), (G p₁) (xₙ.splitAtJoined i γ).1 * (G p₂) (xₙ.splitAtJoined i γ).2 := by
  obtain ⟨α, A, αₙ⟩ := xₙ
  simp
  simp [WeightedConcat.concat]
  rw [← Finset.sum_product']
  rw [← ωSum_finset]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨i, γ⟩, hi⟩, hi'⟩ ↦ by
    exact ⟨(α, A.take i, γ), by simp; contrapose! hi'; simp [hi', GS.splitAtJoined]⟩)
  · intro ⟨⟨⟨i, γ⟩, hi⟩, b⟩
    simp_all
    simp_all
    simp_all
    rintro i' γ' hi' h h'
    rw [Prod.eq_iff_fst_eq_snd_eq] at h'
    simp at h'
    grind
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
    · simp
      intro g hg hg' h
      split at h
      rename_i α' x β' γ' y ξ h'
      split_ifs at h
      subst_eqs
      simp at h
      rw [Prod.eq_iff_fst_eq_snd_eq] at h
      obtain ⟨h₀, h₁⟩ := h
      simp at h₁
      obtain ⟨h₁, ⟨_⟩⟩ := h₁
      suffices y = List.drop i A by subst_eqs; simp_all
      rw [← h₁]
      rw [List.drop_append]
      simp
      have : (i - min i A.length) = 0 := by omega
      simp [this]

theorem RPol.seq_wnka_compute'' {p₁ p₂ : RPol[F,N,𝒮]} [Inhabited Pk[F,N]] {A} :
        wnk_rpol {~p₁; ~p₂}.wnka.compute' A =
    δ[[p₁.wnka.compute' A,
        (∑ γ, ∑ i ∈ Finset.range (A.length - 1), p₁.wnka.compute' (A.take (i + 1)) * 𝒪 p₁ A[i]! γ * ι p₂ * p₂.wnka.compute' (γ :: A.drop (i + 1)))],
      [0, p₂.wnka.compute' A]] := by
  induction A using List.reverseRecOn with
  | nil => simp [WNKA.compute']
  | append_singleton A α₀ ih =>
    clear ih
    induction A using List.reverseRecOn generalizing α₀ with
    | nil => simp [WNKA.compute']
    | append_singleton A α₁ ih =>
      simp [WNKA.compute'_right]
      rw [ih]; clear ih
      simp [δ]
      rw [δ_wProd_δ]
      simp only [Matrix.mul_zero, add_zero, Matrix.mul_sum, ← Matrix.mul_assoc, Matrix.sum_mul, ←
        Finset.sum_add_distrib, Matrix.zero_mul, zero_mul, Finset.sum_const_zero, zero_add]
      congr! 4 with γ hi
      simp [Finset.sum_range_add, WNKA.compute']
      nth_rw 2 [add_comm]
      congr! 2 with n hn
      · congr; simp [List.take_append]
      · simp at hn
        simp only [List.take_append, (by omega : n + 1 - A.length = 0), List.take_zero,
          List.append_nil, List.getElem?_append, hn, ↓reduceIte, getElem?_pos, Option.getD_some,
          List.drop_append, List.drop_zero]
        nth_rw 2 [← List.cons_append]
        simp only [WNKA.compute'_right, wnka_δ]
        simp only [List.cons_append, ← Matrix.mul_assoc]

theorem RPol.wnka_sem_seq [Encodable F] [Encodable N] {p₁ p₂ : RPol[F,N,𝒮]}
    (ih₁ : p₁.wnka.sem = G p₁) (ih₂ : p₂.wnka.sem = G p₂) :
    wnk_rpol {~p₁ ; ~p₂}.wnka.sem = G wnk_rpol {~p₁; ~p₂} := by
  apply wnka_sem_eq_of
  intro A α α'
  letI : Inhabited Pk[F,N] := ⟨α⟩
  simp only [ι, seq_wnka_compute'', List.length_append, List.length_cons, List.length_nil, zero_add,
    add_tsub_cancel_right, List.getElem!_eq_getElem?_getD, 𝒪, G, GS.ofPks, GS.mk, List.drop_one,
    ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_append_of_ne_nil, List.cons_ne_self,
    List.getLast_cons, List.getLast_singleton, G.concat_apply, List.length_dropLast,
    List.length_tail, Nat.reduceAdd, Nat.add_one_sub_one, GS.splitAtJoined, List.splitAt_eq]
  simp only [← ih₁, ← ih₂]
  rw [ι_wProd_δ', ι_wProd_𝒪]
  nth_rw 2 [Finset.sum_comm]
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, ← Finset.sum_add_distrib]
  congr with γ
  simp [Finset.sum_range_add]
  rw [add_comm]
  rcases A with _ | ⟨α₀, A⟩
  · simp [WNKA.compute', ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    rw [Matrix.mul_apply]
    simp
  · simp only [List.length_cons, List.cons_append, List.take_succ_cons, List.drop_succ_cons, ←
    Matrix.mul_assoc, WNKA.sem, wnka_ι, GS.pks, List.head_cons, List.tail_cons, ne_eq, reduceCtorEq,
    not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_cons₂, List.dropLast_singleton,
    Countsupp.coe_mk, List.drop_length_add_append, List.drop_nil, List.nil_append]
    -- TODO
    congr! 1
    · congr! 2 with n hn
      simp at hn
      simp [List.take_append, List.getElem?_append, List.getElem?_cons, (by omega : n - A.length = 0)]
      rcases n with _ | n
      · simp_all [WNKA.compute, WNKA.compute',  WNKA.compute_pair', Matrix.mul_assoc]
        rw [← Matrix.mul_assoc]
        nth_rw 1 [Matrix.mul_apply]
        simp
      · simp_all only [add_lt_add_iff_right, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right, getElem?_pos, Option.getD_some, Matrix.mul_assoc,
        List.drop_append, (by omega : n + 1 - A.length = 0), List.drop_zero, List.append_assoc,
        List.cons_append, List.nil_append, WNKA.compute_pair', wnka_𝒪]
        nth_rw 2 [← Matrix.mul_assoc]
        congr! 3
        induction A using List.reverseRecOn with
        | nil => simp at hn
        | append_singleton A α₁ ih =>
          simp at hn
          simp [List.take_append, List.getElem_append]
          split_ifs
          · nth_rw 1 [← Matrix.mul_assoc]
            nth_rw 2 [← Matrix.mul_assoc]
            rw [Matrix.mul_apply]
            simp
            congr
            rw [Matrix.mul_assoc]
            congr!
            have : List.take (n + 1 - A.length) [α₁] = [] := by
              simp; omega
            simp [this]
            sorry

            -- simp [WNKA.compute]
            -- grind [List.take_eq_nil_iff, List.cons_ne_self]
          · simp_all
            have : List.take (n + 1 - A.length) [α₁] = [α₁] := by
              grind [List.take_eq_self_iff, List.length_cons, List.length_nil, zero_add]
            simp [this, WNKA.compute_pair']
            sorry
    · simp [List.take_append, WNKA.compute_pair', ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp
      congr

-- δ[[δ p α₄ α₃ * δ p α₃ α₂ * δ p α₂ α₁ * δ p α₁ α₀,                                             0],
--   [𝒞.left_to_heart (δ.𝒪_heart α₄ α₃ p * ι p) * δ p α₄ α₃ * δ p α₃ α₂ * δ p α₂ α₁ * δ p α₁ α₀, 0]]

def RPol.upper_left (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) : Matrix (S p) (S p) 𝒮 :=
  match A with
  | [] | [_] => 1
  | α::α'::A => δ p α α' * p.upper_left (α' :: A)

theorem RPol.wnka_seq_δ [Encodable F] [Encodable N] (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) :
      wnk_rpol {~p*}.wnka.compute' A =
    match A with
    | [] | [_] => 1
    | α₀::α₁::A =>
      δ[[p.upper_left (α₀::α₁::A),0],[𝒞.left_to_heart (δ.𝒪_heart α₀ α₁ p * ι p) * p.upper_left (α₀::α₁::A),0]]
  := by
  induction A with
  | nil => simp [WNKA.compute']
  | cons α₀ A ih =>
    simp only [S.I, upper_left]
    induction A with
    | nil => simp [WNKA.compute']
    | cons α₁ A ih' =>
      simp only [WNKA.compute', wnka_δ, δ, S.I]
      rw [ih]; clear ih ih'
      simp only [S.I]
      split
      · simp_all
      · simp_all [RPol.upper_left]
      · simp_all [RPol.upper_left]
        simp [← Matrix.mul_assoc]
        rename_i α₂ A h
        obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
        rw [δ_wProd_δ]
        simp [← Matrix.mul_assoc]

attribute [-simp] Function.iterate_succ in
theorem RPol.wnka_sem
    [Encodable F] [Encodable N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]
    [i : LawfulFinsuppStar 𝒮] (p : RPol[F,N,𝒮]) :
    (RPol.wnka p).sem = G p := by
  induction p with
  | Drop => exact wnka_sem_drop
  | Skip => exact wnka_sem_skip
  | Test t => exact wnka_sem_test
  | Mod π => exact wnka_sem_mod
  | Dup => exact wnka_sem_dup
  | Add p₁ p₂ ih₁ ih₂ => rw [G, ← ih₁, ← ih₂]; exact wnka_sem_add
  | Weight w p ih => rw [G, ← ih]; exact wnka_sem_weight
  | Seq p₁ p₂ ih₁ ih₂ => exact wnka_sem_seq ih₁ ih₂
  | Iter p₁ ih =>
    apply wnka_sem_eq_of
    simp [RPol.wnka_seq_δ]
    simp [G, GS.ofPks, GS.mk, ← List.tail_dropLast, List.head_append]
    simp [G.iter]
    simp [G]
    intro A α α'
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp [RPol.upper_left]
    rcases A with _ | ⟨α₀, A⟩
    · simp [ι, 𝒪]
      rw [ι_wProd_𝒪]
      simp
      simp [Matrix.mul_apply]
      simp [𝒪.𝒪_heart]
      sorry
      -- have : @Finset.card (Unit × S.I {♡}) (Finsupp.support (1 : Unit × S.I {♡} →₀ 𝒮)) = 1 := by
      --   refine Finset.card_eq_one.mpr ?_
      --   simp
      --   use ()
      --   ext ⟨_, ⟨_, _, _⟩⟩
      --   simp_all
      -- simp only [this, Nat.cast_one, one_mul]; clear this
      -- congr with n
      -- induction n with
      -- | zero =>
      --   simp [𝒞.pow, GS.mk, h10]
      --   sorry
      -- | succ n ih =>
      --   simp only [Function.iterate_succ', Function.comp_apply]
      --   simp [𝒞.pow]
      --   nth_rw 1 [Matrix.mul_apply]
      --   rw [instWeightedProductFinsuppProdOfDecidableEq]
      --   simp
      --   rw [ih]
      --   nth_rw 2 [WeightedConcat.concat]
      --   nth_rw 2 [instWeightedConcatCountsuppGS]
      --   simp
      --   sorry
        -- simp
        -- have : ∀ x, @Finset.card (Unit × Unit) x = if x = ∅ then 0 else 1 := by
        --   intro x
        --   split_ifs with h
        --   · simp_all
        --   · refine Finset.card_eq_one.mpr ?_
        --     simp
        --     use (), ()
        --     ext ⟨_, _⟩
        --     simp_all
        --     sorry
        -- simp [this]; clear this
        -- split_ifs with h
        -- · sorry
        -- · sorry





      -- sorry
    · rcases A with _ | ⟨α₁, A⟩
      · simp
        sorry
      · simp
        simp [ι]
        rw [ι_wProd_δ']
        simp [𝒪]
        rw [ι_wProd_𝒪]
        simp
        simp [← Matrix.mul_assoc, 𝒪.𝒪_heart, δ.𝒪_heart]
        sorry


end WeightedNetKAT
