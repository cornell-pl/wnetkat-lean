import WeightedNetKAT.Language
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Star
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Action.Opposite

open OmegaCompletePartialOrder

namespace Matrix

def unfold {A B C D α : Type}
    (m : Matrix A B (Matrix C D α)) : Matrix C D (Matrix A B α) :=
  fun c d a b ↦ m a b c d

@[simp]
theorem unfold_apply {A B C D α : Type} (m : Matrix A B (Matrix C D α)) (c : C) (d : D) :
    m.unfold c d = fun a b ↦ m a b c d := rfl

def down {A B α : Type} [Unique A] [Unique B] (m : Matrix A B α) : α := m default default
-- TOOD: this should probably lift to a diagonal matrix
@[coe] def up {A B α : Type} (a : α) : Matrix A B α := fun _ _ ↦ a

instance {A B α : Type} : Coe α (Matrix A B α) := ⟨up⟩

@[simp]
theorem up_apply {A B α : Type} (a : α) (x : A) (y : B) : Matrix.up (A:=A) (B:=B) a x y = a := rfl

@[simp]
theorem up_add {A B α : Type} [AddCommMonoid α] (a b : α) : Matrix.up (A:=A) (B:=B) (a + b) = ↑a + ↑b := rfl

def coe_unique_left {A A' B α : Type} [Unique A] [Unique A'] (m : Matrix A B α) : Matrix A' B α :=
  fun _ b ↦ m default b

@[simp]
theorem coe_unique_left_fun {A A' B α : Type} [Unique A] [Unique A'] (f : A → B → α) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) (fun a b ↦ f a b) = fun _ b ↦ f default b := rfl

section

variable {𝒮 : Type} [AddCommMonoid 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

instance {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    OmegaCompletePartialOrder (Matrix X Y 𝒮) := inferInstanceAs (OmegaCompletePartialOrder (X → Y → 𝒮))
instance {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    OrderBot (Matrix X Y 𝒮) := inferInstanceAs (OrderBot (X → Y → 𝒮))
instance {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    IsPositiveOrderedAddMonoid (Matrix X Y 𝒮) := inferInstanceAs (IsPositiveOrderedAddMonoid (X → Y → 𝒮))

end

section

variable {𝒮 : Type} [NonUnitalSemiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

@[simp]
theorem ωSum_apply {ι A B : Type} [Countable ι] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] {f : ι → Matrix A B 𝒮} (a : A) :
    (ω∑ x, f x) a = ω∑ x, f x a := by
  convert _root_.ωSum_apply

@[simp]
theorem up_ωSum {ι A N : Type} [Countable ι] [DecidableEq A] [Fintype A] [DecidableEq N] [Fintype N] {f : ι → Matrix A A 𝒮} :
    up (A:=N) (B:=N) (ω∑ x, f x) = ω∑ x, up (f x) := by
  ext n m a b
  simp

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem of_ωSum {ι A B : Type} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    {f : ι → Matrix A B 𝒮} :
    Matrix.of (fun a b ↦ ω∑ x, f x a b) = ω∑ x, Matrix.of (fun a b ↦ f x a b) := by
  ext; simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem of_ωSum' {ι A B : Type} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    {f : ι → Matrix A B 𝒮} :
    (fun a b ↦ ω∑ x, f x a b) = ω∑ x, (fun a b ↦ f x a b) := by
  ext; simp

theorem ωSum_mul_right {ι A B C : Type} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    {f : ι → Matrix A B 𝒮} (a : Matrix B C 𝒮) :
    ω∑ x, f x * a = (ω∑ x, f x) * a := by
  ext a c; simp [mul_apply, ← _root_.ωSum_mul_right, ωSum_sum_comm]
theorem ωSum_mul_left {ι A B C : Type} [Countable ι]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    {f : ι → Matrix B C 𝒮} (a : Matrix A B 𝒮) :
    ω∑ x, a * f x = a * (ω∑ x, f x) := by
  ext a c; simp [mul_apply, ← _root_.ωSum_mul_left, ωSum_sum_comm]

instance {N : Type} [DecidableEq N] [Fintype N] : MulLeftMono (Matrix N N 𝒮) where
  elim := by
    intro a b c hbc n n'
    simp [Matrix.mul_apply]
    gcongr with m
    exact hbc m n'
instance {N : Type} [DecidableEq N] [Fintype N] : MulRightMono (Matrix N N 𝒮) where
  elim := by
    intro a b c hbc n n'
    simp [Function.swap, Matrix.mul_apply]
    gcongr with m
    exact hbc n m
open OmegaContinuousNonUnitalSemiring in
instance {N : Type} [DecidableEq N] [Fintype N] : OmegaContinuousNonUnitalSemiring (Matrix N N 𝒮) where
  ωSup_add_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_left_mono, fun c ↦ ?_⟩
    ext i j
    convert ωSup_add_left (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
  ωSup_add_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨add_right_mono, fun c ↦ ?_⟩
    ext i j
    convert ωSup_add_right (m i j) |>.map_ωSup (c.map ⟨(· i j), fun ⦃_ _⦄ a ↦ a i j⟩)
  ωSup_mul_left m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_left_mono, fun c ↦ ?_⟩
    ext i j
    have : ∀ x, ωSup c x j = ωSup (c.map ⟨fun n ↦ n x j, fun ⦃_ _⦄ a ↦ a x j⟩) := fun _ ↦ rfl
    simp [mul_apply, this, ωSup_mul_left _ |>.map_ωSup, sum_ωSup']
    congr
  ωSup_mul_right m := by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨mul_right_mono, fun c ↦ ?_⟩
    ext i j
    have : ∀ x, ωSup c i x = ωSup (c.map ⟨fun n ↦ n i x, fun ⦃_ _⦄ a ↦ a i x⟩) := fun _ ↦ rfl
    simp [mul_apply, this, ωSup_mul_right _ |>.map_ωSup, sum_ωSup']
    congr

end

end Matrix

@[simp]
theorem List.take_length_succ {α : Type} (A : List α) : List.take (A.length + 1) A = A := by
  simp only [List.take_eq_self_iff, le_add_iff_nonneg_right, zero_le]

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F] [Listed F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

scoped notation "𝟙" => Unit

scoped notation "𝒲[" x ", " y ", " s "]" => Matrix x y s

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝒪 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F N 𝒮 Q: Type)
    [Semiring 𝒮]
where
  /-- `ι` is the initial weightings. -/
  ι : 𝒲[𝟙,Q,𝒮]
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F,N]) → 𝒲[Q,Q,𝒮]
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : (α β : Pk[F,N]) → 𝒲[Q,𝟙,𝒮]
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

def S.ι {X Y : Type} : (Matrix 𝟙 X 𝒮) → (Matrix 𝟙 Y 𝒮) → (Matrix 𝟙 (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "ι[" a "," b"]" => S.ι a b
def S.𝒪 {X Y : Type} : (Matrix X 𝟙 𝒮) → (Matrix Y 𝟙 𝒮) → (Matrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "𝒪[" a "," b"]" => S.𝒪 a b
attribute [grind] Prod.map Function.Injective in
def S.δ {X Y Z W : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] :
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
instance : Unique (S.I {♡}) where
  default := ⟨♡, by simp⟩
  uniq := by simp

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

instance : Listed (S.I {♡}) := ⟨[⟨♡, by simp⟩], by simp, by simp⟩
instance S.listed (p : RPol[F,N,𝒮]) : Listed (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    inferInstanceAs (Listed (S.I {♡}))
  | wnk_rpol {dup} => ⟨[⟨♡, by simp⟩, ⟨♣, by simp⟩], by simp; grind, by rintro ⟨_, (h | h | h)⟩ <;> simp_all⟩
  | wnk_rpol {~_ ⨀ ~p₁} => S.listed p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁*} => letI := S.listed p₁; Listed.instSum

variable [DecidableEq 𝒮]

abbrev η₁ {X : Type} [DecidableEq X] (i : X) : X → 𝒮 :=
  fun i' ↦ if i = i' then 1 else 0
abbrev η₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] (i : X) (j : Y) : Matrix X Y 𝒮 :=
  fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def ι (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η₂ () ⟨♡, rfl⟩
  | wnk_rpol {dup} => η₂ () ⟨♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~p₂} => ι[ι p₁, 0]
  | wnk_rpol {~p₁*} => ι[0, fun () ↦ 1]

def 𝒞.left_to_unit {X : Type} [DecidableEq X] (m : Matrix (S.I {♡}) X 𝒮) : Matrix 𝟙 X 𝒮 :=
  fun () x ↦ m ⟨♡, rfl⟩ x
def 𝒞.left_to_heart {X : Type} [DecidableEq X] (m : (Matrix 𝟙 X 𝒮)) : Matrix (S.I {♡}) X 𝒮 :=
  fun ⟨♡, _⟩ x ↦ m () x

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem 𝒞.left_to_unit_apply {X : Type} [DecidableEq X] (m : Matrix (S.I {♡}) X 𝒮) (x) (y) :
    𝒞.left_to_unit m x y = m ⟨♡, rfl⟩ y := rfl
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem 𝒞.left_to_heart_apply {X : Type} [DecidableEq X] (m : Matrix 𝟙 X 𝒮) (x) (y) :
    𝒞.left_to_heart m x y = m () y := by simp [left_to_heart]; split; rfl

def 𝒞.transpose {X Y : Type} [DecidableEq X] [DecidableEq Y] (m : (X × Y) →₀ 𝒮) : (Y × X) →₀ 𝒮 :=
  ⟨(m.support.image (fun (y, x) ↦ (x, y))), (fun (y, x) ↦ m (x, y)), (by simp)⟩

variable [WeightedNetKAT.Star 𝒮]
variable [WeightedNetKAT.LawfulStar 𝒲[Pk[F,N],Pk[F,N],𝒮]]

open scoped RightActions

def box {X} [DecidableEq X] [Fintype X]
    (l : Matrix 𝟙 X 𝒮) (r : Matrix Pk[F,N] Pk[F,N] (Matrix X 𝟙 𝒮)) :
    𝒲[Pk[F,N],Pk[F,N],𝒮] := fun α β ↦ (l * r α β).down

infixr:50 " ⊠ " => box

def 𝒪 (p : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p) 𝟙 𝒮) := fun α β ↦
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
    𝒪[
      𝒪 p₁ α β <• 𝒪_heart p₁ α β,
      ↑(𝒪_heart p₁ α β)
    ]
where
      𝒪_heart (p₁ : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] 𝒮 := (ι p₁ ⊠ 𝒪 p₁)^*

def δ (p : RPol[F,N,𝒮]) : 𝒲[Pk[F,N],Pk[F,N],𝒲[S p,S p,𝒮]] := fun α β ↦
  match p with
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
    -- let x : Matrix 𝟙 (S p₁) (Matrix Pk[F,N] Pk[F,N] 𝒮) := (ι p₁).map Matrix.up * (δ p₁).unfold
    -- let y : Matrix 𝟙 (S p₁) (Matrix Pk[F,N] Pk[F,N] 𝒮) := Matrix.up (𝒪_heart p₁) * x
    -- let z : Matrix 𝟙 (S p₁) 𝒮 := y.unfold α β
    -- let a :=
    --   𝒪 p₁ α β * (𝒪.𝒪_heart p₁ α β • ι p₁ * δ p₁ α β)
    -- have : AddCommMonoid (𝒲[S p₁, 𝟙, 𝒮]) := inferInstance
    -- let b : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, 𝟙, 𝒮]] :=
    --   a * 𝒪 p₁
    -- let y : Matrix 𝟙 (S p₁) (Matrix Pk[F,N] Pk[F,N] 𝒮) :=
    --     Matrix.up (𝒪.𝒪_heart p₁) * (ι p₁).map Matrix.up * (δ p₁).unfold
    -- let z : Matrix 𝟙 (S p₁) 𝒮 := y.unfold α β
    δ[[δ' p₁ α β, 0],
      [(𝒪.𝒪_heart p₁ α β • ι p₁ * δ p₁ α β).coe_unique_left, 0]]
where δ' (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) := δ p₁ α β + 𝒪 p₁ α β * (𝒪.𝒪_heart p₁ α β • ι p₁ * δ p₁ α β)

theorem δ.asdjhas (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) :
    let y : Matrix 𝟙 (S p₁) (Matrix Pk[F,N] Pk[F,N] 𝒮) := Matrix.up (𝒪.𝒪_heart p₁) * (ι p₁).map Matrix.up * (δ p₁).unfold;
    let z : Matrix 𝟙 (S p₁) 𝒮 := y.unfold α β;
    (z.coe_unique_left : Matrix (S.I {♡}) (S p₁) 𝒮) =
    (𝒪.𝒪_heart p₁ α β • (ι p₁ * δ p₁ α β)).coe_unique_left := by
  simp
  ext s s'
  unfold Matrix.up Matrix.unfold
  simp [Matrix.mul_apply]
  simp [Finset.mul_sum]
  simp [Matrix.sum_apply]
  simp [Matrix.mul_apply]
  simp [Finset.sum_mul]
  congr with c


  sorry

example {a : Prop} : ¬¬a ↔ a := by exact not_not

def RPol.wnka (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] where
  ι := ι p
  δ := δ p
  𝒪 := 𝒪 p

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem RPol.wnka_ι (p : RPol[F,N,𝒮]) : p.wnka.ι = ι p := rfl
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem RPol.wnka_δ (p : RPol[F,N,𝒮]) : p.wnka.δ = δ p := rfl
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp] theorem RPol.wnka_𝒪 (p : RPol[F,N,𝒮]) : p.wnka.𝒪 = 𝒪 p := rfl

def big_wprod {X : Type} [Fintype X] [DecidableEq X] (l : List ((X × X) →₀ 𝒮)) : (X × X) →₀ 𝒮 :=
  l.foldl (· * ·) 1

def WNKA.compute' {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    Matrix Q Q 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => 1
  | α::α'::s => 𝒜.δ α α' * 𝒜.compute' (α' :: s)

def WNKA.compute'_right {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) {α α'} :
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

def WNKA.compute {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    Matrix Q 𝟙 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => fun _ ↦ 1
  | [α, α'] => 𝒜.𝒪 α α'
  | α::α'::s => 𝒜.δ α α' * 𝒜.compute (α' :: s)

def WNKA.compute_pair {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α' α'' : Pk[F,N]) :
    𝒜.compute (A ++ [α', α'']) = (𝒜.compute' (A ++ [α']) * 𝒜.𝒪 α' α'') := by
  induction A with
  | nil => grind [List.nil_append, compute, compute', Matrix.one_mul]
  | cons α₀ A ih =>
    rcases A with _ | ⟨α₁, A⟩
    · grind [List.nil_append, List.append_nil, List.cons_append, compute, compute', mul_one]
    · grind only [List.append_eq_nil_iff, List.cons_append, → List.eq_nil_of_append_eq_nil,
        compute', Matrix.mul_assoc, compute]

def WNKA.compute_pair' {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α₀ α' α'' : Pk[F,N]) :
    𝒜.compute (α₀ :: (A ++ [α', α''])) = (𝒜.compute' (α₀ :: (A ++ [α'])) * 𝒜.𝒪 α' α'') := by
  rw [← List.cons_append, WNKA.compute_pair]; rfl

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem WNKA.compute_eq_of {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) (h𝒪 : 𝒜.𝒪 = 𝒜'.𝒪) :
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
theorem WNKA.compute'_eq_of {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) :
    𝒜.compute' s = 𝒜'.compute' s := by
  induction s with
  | nil => simp [compute']
  | cons x s ih =>
    induction s with
    | nil => simp [compute']
    | cons y s ih =>
      unfold compute'
      simp [ih, hδ]

def WNKA.sem {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨(fun x ↦ (𝒜.ι * 𝒜.compute x.pks) () ()), SetCoe.countable _⟩

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
@[simp]
theorem asdasd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [Fintype X] [Fintype Y] (x : X) (y : Y) (m : Matrix Y Z 𝒮) :
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem ι_wProd_𝒪 {A B : Type} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    {X : Matrix 𝟙 A 𝒮} {Y : Matrix 𝟙 B 𝒮} {Z : Matrix A 𝟙 𝒮} {W : Matrix B 𝟙 𝒮} :
    (ι[X, Y] * 𝒪[Z, W]) = (X * Z) + (Y * W) := by
  ext i j
  simp [Matrix.mul_apply, S.ι, S.𝒪]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem ι_wProd_δ {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix 𝟙 A 𝒮} {Y : Matrix 𝟙 B 𝒮}
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
theorem ι_wProd_δ' {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix 𝟙 A 𝒮} {Y : Matrix 𝟙 B 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (ι[X, Y] * δ[[Z, W], [U, V]]) = ι[X * Z + Y * U, X * W + Y * V] := by
  ext _ a
  simp [Matrix.mul_apply, S.ι, S.δ]
  rcases a with c | d <;> simp

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
theorem δ_wProd_δ {A B C D E F : Type}
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
theorem δ_wProd_𝒪 {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {X : Matrix C 𝟙 𝒮} {Y : Matrix D 𝟙 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (δ[[Z, W], [U, V]] * 𝒪[X, Y]) = 𝒪[Z * X + W * Y, U * X + V * Y] := by
  ext a _
  simp [Matrix.mul_apply, S.𝒪, S.δ]
  rcases a with c | d <;> simp

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] in
@[simp]
theorem S.δ_identity {A B : Type} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B] :
    (δ[[1,0],[0,1]] : Matrix (A ⊕ B) (A ⊕ B) 𝒮) = 1 := by
  ext ab₁ ab₂
  rcases ab₁ with a₁ | b₁ <;> rcases ab₂ with a₂ | b₂ <;> simp [S.δ, Matrix.one_apply]

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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem RPol.wnka_sem_pair (p : RPol[F,N,𝒮]) (α γ : Pk[F,N]) :
    p.wnka.sem (α, [], γ) = (ι p * 𝒪 p α γ) () () := rfl

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
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
omit [DecidableEq 𝒮] in
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
    simp [G, GS.mk, GS.ofPks, ι, 𝒪]
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

omit [DecidableEq 𝒮] in
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
    · ext; simp [δ]
    · ext; simp only [𝒪]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
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

omit [DecidableEq 𝒮] in
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
        nth_rw 1 [← Matrix.mul_assoc]
        rw [Matrix.mul_apply]
        simp
        congr! 3
        induction A using List.reverseRecOn with
        | nil => simp at hn
        | append_singleton A α₁ ih =>
          simp at hn
          simp [List.take_append, List.getElem_append]
          split_ifs
          · have : n + 1 - A.length = 0 := by omega
            grind
          · have : n + 1 - A.length = 1 := by omega
            simp_all [WNKA.compute_pair']
    · simp [List.take_append, WNKA.compute_pair', ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp
      congr

-- δ[[δ p α₄ α₃ * δ p α₃ α₂ * δ p α₂ α₁ * δ p α₁ α₀,                                             0],
--   [𝒞.left_to_heart (δ.𝒪_heart α₄ α₃ p * ι p) * δ p α₄ α₃ * δ p α₃ α₂ * δ p α₂ α₁ * δ p α₁ α₀, 0]]

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

structure Str (F N : Type) where
  xs : List Pk[F,N]

notation "Str[" F "," N "]" => Str F N

instance : GetElem Str[F,N] ℕ Str[F,N] (fun _ _ ↦ true) where
  getElem m n _ := ⟨m.xs.take n⟩

def Str.x (s : Str[F,N]) (i : ℕ) : Str[F,N] := ⟨s.xs.take i⟩
def Str.y (s : Str[F,N]) (i : ℕ) : Str[F,N] := ⟨s.xs.drop i⟩

@[coe] def Str.coe (s : Str[F,N]) : List Pk[F,N] := s.xs
instance : Coe Str[F,N] (List Pk[F,N]) := ⟨Str.coe⟩

def Str.length (s : Str[F,N]) := s.xs.length

-- instance :  Str[F,N] where

noncomputable def M' (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ G p ⟨α, xᵢ, β⟩

noncomputable def N' (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ G p ⟨α, xᵢ, β⟩

omit [DecidableEq 𝒮] [Star 𝒮] in
theorem G.star_apply (p₁ : RPol[F,N,𝒮]) (α : Pk[F,N]) (s : Str[F,N]) (β : Pk[F,N]) :
      ((G p₁.Iter) : _ →c 𝒮) (α, s, β)
    = (G RPol.Skip) (α, s, β) +
        (∑ γ, (G p₁) (α, [], γ) * (G p₁.Iter) (γ, s, β)) +
          ∑ i ∈ Finset.range s.length,
            (M' p₁ (s.x (i + 1)) * M' p₁.Iter (s.y (i + 1))) α β := by
            -- ∑ γ,
            --   (G p₁) (GS.splitAtJoined (α, xₙ, β) (1 + n) γ).1 *
            --     (G p₁.Iter) (GS.splitAtJoined (α, xₙ, β) (1 + n) γ).2) := by
    -- = (G RPol.Skip) (α, xₙ, β) +
    --     (∑ γ, (G p₁) (α, [], γ) * (G p₁.Iter) (γ, xₙ, β) +
    --       ∑ n ∈ Finset.range xₙ.length,
    --         ∑ γ,
    --           (G p₁) (GS.splitAtJoined (α, xₙ, β) (1 + n) γ).1 *
    --             (G p₁.Iter) (GS.splitAtJoined (α, xₙ, β) (1 + n) γ).2) := by
  unfold M'
  simp [G]
  rw [ωSum_nat_eq_succ]
  simp
  conv => left; right; arg 1; ext x; rw [G]
  sorry
  -- simp [G.concat_apply]
  -- nth_rw 2 [add_comm]
  -- simp [Finset.sum_range_add]
  -- conv => left; right; arg 1; ext x; left; arg 2; ext y; rw [GS.splitAtJoined]
  -- simp [ωSum_add]
  -- simp [G]
  -- simp [Matrix.mul_apply]
  -- simp [← ωSum_mul_left, ωSum_sum_comm]
  -- simp [ωSum_mul_left]
  -- rw [add_assoc]
  -- congr
  -- ext n
  -- congr with γ
  -- congr
  -- · simp [GS.splitAtJoined, Str.x]
  --   rw [add_comm]
  --   congr
  -- · simp [GS.splitAtJoined, Str.y]
  --   ext
  --   rw [add_comm]
  --   congr

omit [DecidableEq 𝒮] [Star 𝒮] in
theorem G.star_apply' {p₁ : RPol[F,N,𝒮]} {s : GS[F,N]} :
      ((G p₁.Iter) : _ →c 𝒮) s
    = (G RPol.Skip) s +
        (∑ γ, (G p₁) (s.1, [], γ) * (G p₁.Iter) (γ, s.2.1, s.2.2)) +
          ∑ i ∈ Finset.range s.2.1.length,
            (M' p₁ (s.2.1.take (i + 1)) * M' p₁.Iter (s.2.1.drop (i + 1))) s.1 s.2.2 := by
  obtain ⟨α, s, β⟩ := s
  convert G.star_apply p₁ α ⟨s⟩ β

noncomputable def Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ p.wnka.sem ⟨α, xᵢ, β⟩

@[simp]
theorem Q_empty (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) :
    Q p₁.Iter {} α β = (ι p₁ ⊠ 𝒪 p₁)^* α β := by
  simp [Q, ι, 𝒪]
  rw [ι_wProd_𝒪]
  simp [Matrix.mul_apply, 𝒪.𝒪_heart]

theorem M_unroll_empty (p₁ : RPol[F,N,𝒮]) : 1 + M' p₁ [] * M' p₁.Iter [] = M' p₁.Iter [] := by
  unfold M'
  simp [G, Matrix.mul_apply]
  ext α β
  rw [ωSum_nat_eq_succ]
  simp [G]
  simp [Matrix.one_apply]
  if α = β then
    subst_eqs
    simp_all [GS.mk]
    congr
    simp [Matrix.mul_apply, ← ωSum_mul_left, ← ωSum_sum_comm]
    congr with n
    simp [WeightedConcat.concat]
    simp [← ωSum_prod']
    rw [← ωSum_fintype]
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨x, hx⟩, hx'⟩, hx''⟩ ↦ x.snd.snd)
    · intro ⟨⟨x, hx⟩, hx'⟩
      simp_all only [Subtype.forall, Function.mem_support, ne_eq, ite_eq_right_iff,
        Classical.not_imp, Subtype.mk.injEq, and_imp, Prod.forall, Prod.mk.injEq,
        Countsupp.mem_support_iff]
      simp_all only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
      grind
    · intro γ hγ
      simp_all only [Function.mem_support, ne_eq, Set.mem_range, Subtype.exists, ite_eq_right_iff,
        Classical.not_imp, exists_prop, Prod.exists, exists_and_right, Countsupp.mem_support_iff]
      use (α, [], γ)
      simp_all
      constructor
      · contrapose! hγ; simp [hγ]
      · use (γ, [], α)
        simp_all
        contrapose! hγ; simp [hγ]
    · simp
      intros
      split at *
      simp_all
      rename_i h
      obtain ⟨⟨_⟩, h⟩ := h
      rw [Prod.eq_iff_fst_eq_snd_eq] at h
      simp at h
      obtain ⟨⟨_⟩, ⟨⟨_⟩, ⟨_⟩⟩, ⟨_⟩⟩ := h
      congr
  else
    simp_all [GS.mk]
    split_ifs
    · grind
    · simp_all
      simp [Matrix.mul_apply, ← ωSum_mul_left, ← ωSum_sum_comm]
      congr with n
      simp [WeightedConcat.concat]
      simp [← ωSum_prod']
      rw [← ωSum_fintype]
      apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hx''⟩ ↦ x.2.2)
      · intro ⟨⟨x, hx⟩, hx'⟩
        simp_all only [Subtype.forall, Function.mem_support, ne_eq, ite_eq_right_iff,
          Classical.not_imp, Subtype.mk.injEq, and_imp, Prod.forall, Prod.mk.injEq,
          Countsupp.mem_support_iff]
        simp_all only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
        grind
      · intro γ hγ
        simp only [Set.mem_range, Subtype.exists, Function.mem_support, ne_eq, ite_eq_right_iff,
          Classical.not_imp, exists_prop, Prod.exists, exists_and_right, Countsupp.mem_support_iff]
        simp only [Function.mem_support, ne_eq] at hγ
        use (α, [], γ)
        simp
        constructor
        · contrapose! hγ; simp [hγ]
        · use (γ, [], β)
          simp_all; contrapose! hγ; simp [hγ]
      · simp
        intros
        split at *
        simp_all
        rename_i h
        obtain ⟨⟨_⟩, h⟩ := h
        rw [Prod.eq_iff_fst_eq_snd_eq] at h
        simp at h
        obtain ⟨⟨_⟩, ⟨⟨_⟩, ⟨_⟩⟩, ⟨_⟩⟩ := h
        congr

theorem M_unroll_cons (p₁ : RPol[F,N,𝒮]) (α₀) (s) : M' p₁.Iter (α₀ :: s) = M' p₁ [] * M' p₁.Iter s + sorry := by
  unfold M'
  ext α β
  -- have := G.star_apply (p₁:=p₁) (α:=α) (s:=⟨α₀::s⟩) (β:=β)
  convert G.star_apply (p₁:=p₁) (α:=α) (s:=⟨α₀::s⟩) (β:=β)
  symm
  simp [Str.length]
  simp [Matrix.mul_apply]
  nth_rw 3 [add_comm]
  simp [Finset.sum_range_add]
  nth_rw 2 [add_comm]
  rw [add_assoc]
  congr! 3
  simp [G]
  rw [ωSum_nat_eq_succ]
  simp
  sorry
  sorry
  -- induction s with
  -- | nil => exact M_unroll_empty p₁
  -- | cons α₀ s ih =>
  --   unfold M' at ih ⊢
  --   ext α β
  --   simp [G]
  --   rw [ωSum_nat_eq_succ]
  --   simp [G]
  --   sorry


def fp (p₁ : RPol[F,N,𝒮]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) : Prop := Z = 1 + M' p₁ [] * Z

theorem box_eq_M'_of_empty (p₁ : RPol[F,N,𝒮]) : (ι p₁ ⊠ 𝒪 p₁) = M' p₁ [] := by
  ext α β
  simp [box, Matrix.down, M']
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  have h01 : ¬(0 : 𝒮) = 1 := by grind
  induction p₁ generalizing α β with
  | Skip => simp [ι, 𝒪, G, GS.mk]; split_ifs <;> simp_all; grind
  | Drop => simp [ι, 𝒪, G]
  | Test => simp [ι, 𝒪, G, GS.mk]; split_ifs <;> simp_all; grind
  | Mod => simp [ι, 𝒪, G, GS.mk]; split_ifs <;> simp_all; grind
  | Dup => simp [ι, 𝒪, G, GS.mk]; split_ifs <;> simp_all <;> grind
  | Seq p₁ p₂ ih₁ ih₂ =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp
    simp [Matrix.mul_sum, ← Matrix.mul_assoc]
    -- sorry
    -- TODO: this should work but we need lawful star
    rw [G.concat_apply]
    simp [GS.splitAtJoined]
    simp [← ih₁, ← ih₂]
    conv =>
      left
      arg 2
      ext x
      rw [Matrix.mul_assoc]
    simp [Matrix.sum_apply]
    simp [Matrix.mul_apply]
  | Iter p ih =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp [𝒪.𝒪_heart]
    simp [Matrix.mul_apply]
    sorry
    -- TODO: this should work but we need lawful star
    -- simp [LawfulStar.star_eq_sum]
    -- simp [G.iter]
    -- congr with n
    -- induction n generalizing α β with
    -- | zero => simp [G, GS, G.ofPk, Matrix.one_apply, GS.mk]
    -- | succ n ih' =>
    --   simp only [Function.iterate_succ', Function.comp_apply]
    --   simp [pow_succ']
    --   simp [Matrix.mul_apply]
    --   simp [ih']; clear ih'
    --   rw [G.concat_apply]
    --   simp [GS.splitAtJoined]
    --   simp [← ih]
    --   rfl
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp [← ih₁, ← ih₂]
  | Weight w p ih =>
    simp [ι, 𝒪, G]
    simp [← ih]

theorem 𝒪_heart_fp (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp p₁ f} (𝒪.𝒪_heart p₁) := by
  constructor
  · simp [fp, 𝒪.𝒪_heart, LawfulStar.star_eq_sum, ← Matrix.ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    congr! with n
    rw [pow_succ', box_eq_M'_of_empty]
  · intro g hg
    simp [fp] at hg
    symm at hg
    simp [𝒪.𝒪_heart, LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, DFunLike.coe]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [add_comm, Finset.sum_range_add]
      conv => left; right; arg 2; ext; rw [add_comm]
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, pow_succ', ← Finset.mul_sum]
      apply le_trans _ hg.le
      gcongr
      rw [box_eq_M'_of_empty]

theorem box_star_fp (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp p₁ f} (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := 𝒪_heart_fp p₁
  simpa [𝒪.𝒪_heart]

theorem M_fp (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp p₁ f} (M' p₁ [])^* := by
  constructor
  · simp [fp]
    simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    simp [pow_succ']
  · intro g hg
    simp [fp] at hg
    symm at hg
    simp [LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, DFunLike.coe]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [add_comm, Finset.sum_range_add]
      conv => left; right; arg 2; ext; rw [add_comm]
      simp [pow_succ', ← Finset.mul_sum]
      apply le_trans _ hg.le
      gcongr

theorem Q_fp (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp p₁ f} (Q p₁ [])^* := by
  constructor
  · simp [fp]
    simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    simp
    congr! with n
    simp [pow_succ']
    congr
    rw [← box_eq_M'_of_empty]
    rfl
  · intro g hg
    simp [fp] at hg
    symm at hg
    simp [LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, DFunLike.coe]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [add_comm]
      simp [Finset.sum_range_add]
      conv => left; right; arg 2; ext; rw [add_comm]
      simp [pow_succ', ← Finset.mul_sum]
      apply le_trans _ hg.le
      gcongr
      rw [← box_eq_M'_of_empty]
      rfl

-- theorem Q_fp' (p₁ : RPol[F,N,𝒮]) (x : List Pk[F,N]) : IsLeast {f | fp p₁ f} (Q p₁ x)^* := by
--   induction x with
--   | nil => exact Q_fp p₁
--   | cons α₀ x ih =>
--     constructor
--     · simp [fp]
--       simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
--       obtain ⟨ih₁, ih₂⟩ := ih
--       simp [fp] at ih₁; symm at ih₁
--       -- simp [fp] at ih₂; symm at ih₂
--       simp [ωSum_mul_left]
--       simp [LawfulStar.star_eq_sum, ωSum_mul_left] at ih₁
--       rw [ωSum_nat_eq_succ]
--       simp
--       congr! with n
--       congr
--       sorry
--     · intro g hg
--       simp [fp] at hg
--       symm at hg
--       simp [LawfulStar.star_eq_sum]
--       rw [ωSum_nat_eq_ωSup]
--       simp only [ωSup_le_iff, DFunLike.coe]
--       intro i
--       induction i with
--       | zero => simp
--       | succ i ih' =>
--         rw [add_comm, Finset.sum_range_add]
--         simp only [Finset.range_one, Finset.sum_singleton, pow_zero]
--         conv => left; right; arg 2; ext; rw [add_comm]
--         simp [pow_succ', ← Finset.mul_sum]
--         obtain ⟨ih₁, ih₂⟩ := ih
--         simp [fp] at ih₁; symm at ih₁
--         simp [fp] at ih₂
--         simp [mem_lowerBounds] at ih₂
--         have := ih₂ g (Eq.symm hg)
--         simp only [LawfulStar.star_eq_sum, ωSum_nat_eq_ωSup, ωSup_le_iff, DFunLike.coe] at this
--         apply le_trans _ hg.le
--         gcongr
--       sorry

theorem M_empty_star_eq_heart (p₁ : RPol[F,N,𝒮]) : (M' p₁ [])^* = (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := (IsLeast.unique (𝒪_heart_fp p₁) (M_fp p₁)).symm
  simpa [𝒪.𝒪_heart]

theorem Q_star_eq_box (p₁ : RPol[F,N,𝒮]) : (Q p₁ [])^* = (ι p₁ ⊠ 𝒪 p₁)^* :=
  IsLeast.unique (Q_fp p₁) (box_star_fp p₁)

theorem box_star_iter (p₁ : RPol[F,N,𝒮]) : (ι p₁ ⊠ 𝒪 p₁)^* = 1 + (ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := 𝒪_heart_fp p₁ |>.left
  simp [fp, 𝒪.𝒪_heart] at this
  rw [← box_eq_M'_of_empty] at this
  assumption

def RPol.upper_left (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) : Matrix (S p) (S p) 𝒮 :=
  match A with
  | [] | [_] => 1
  | α::α'::A => δ.δ' p α α' * p.upper_left (α' :: A)

-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
-- theorem RPol.wnka_seq_δ [Encodable F] [Encodable N] (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) :
--       wnk_rpol {~p*}.wnka.compute' A =
--     match A with
--     | [] | [_] => 1
--     | α₀::α₁::A =>
--       δ[[p.upper_left (α₀::α₁::A),0],[𝒞.left_to_heart (Matrix.up (δ.𝒪_heart p α₀ α₁) * ι p) * p.upper_left (α₀::α₁::A),0]]
--   := by
--   induction A with
--   | nil => simp [WNKA.compute']
--   | cons α₀ A ih =>
--     simp only [S.I, upper_left]
--     induction A with
--     | nil => simp [WNKA.compute']
--     | cons α₁ A ih' =>
--       simp only [WNKA.compute', wnka_δ, δ, S.I]
--       rw [ih]; clear ih ih'
--       simp only [S.I]
--       split
--       · simp_all
--       · simp_all [RPol.upper_left]
--         simp [Matrix.up, Matrix.unfold, Matrix.coe_unique_left]
--         -- unfold Matrix.up Matrix.unfold Matrix.coe_unique_left
--         -- simp
--         simp [Matrix.mul_apply]
--       · simp_all [RPol.upper_left]
--         simp [← Matrix.mul_assoc]
--         rename_i α₂ A h
--         obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
--         rw [δ_wProd_δ]
--         simp [← Matrix.mul_assoc]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] in
theorem RPol.wnka_seq_δ [Encodable F] [Encodable N] (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) :
      wnk_rpol {~p*}.wnka.compute' A =
    match A with
    | [] | [_] => 1
    | α₀::α₁::A =>
      δ[[p.upper_left (α₀::α₁::A),0],
        [Matrix.of (fun (_ : S.I ↑{♡}) (b : S p) ↦ (Matrix.up (𝒪.𝒪_heart p) * ((ι p).map Matrix.up * (δ p).unfold) : Matrix 𝟙 (S p) (Matrix Pk[F,N] Pk[F,N] 𝒮)) () b α₀ α₁) * p.upper_left (α₁::A),0]]
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
        rename_i h
        obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
        simp [Matrix.of]
        congr!
        simp [Matrix.mul_apply, Equiv.refl]
        simp only [DFunLike.coe, EquivLike.coe]
        simp [Matrix.sum_apply, Matrix.mul_apply]
        simp [Finset.mul_sum, Finset.sum_mul]
        simp [← mul_assoc]
        sorry
        -- nth_rw 2 [Finset.sum_comm]
        -- congr with s
        -- rw [Finset.sum_comm]
      · simp_all [RPol.upper_left]
        simp [← Matrix.mul_assoc]
        rename_i α₂ A h
        obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
        rw [δ_wProd_δ]
        simp [← Matrix.mul_assoc]
        congr
        sorry

@[simp]
theorem G.skip_eq_one' {α β : Pk[F,N]} : G RPol.Skip ⟨α, [], β⟩ = M' (𝒮:=𝒮) (F:=F) (N:=N) RPol.Skip [] α β := by
  rfl
theorem G.skip_eq_one {α β : Pk[F,N]} {x} : G (𝒮:=𝒮) RPol.Skip ⟨α, x, β⟩ = if x.length = 0 ∧ α = β then 1 else 0 := by
  split_ifs
  · simp_all [G, GS.mk]
  · simp_all [G, GS.mk]
    grind
-- theorem G.skip_eq_one {α β : Pk[F,N]} : G RPol.Skip ⟨α, [], β⟩ = M' (𝒮:=𝒮) (F:=F) (N:=N) RPol.Skip [] := by
  -- ext x y
  -- simp [M']
  -- if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  -- have : ¬(0 : 𝒮) = 1 := by grind
  -- if α = β then
  --   subst_eqs
  --   simp [G, GS.mk, M', Matrix.one_apply]
  --   if x = y then
  --     subst_eqs
  --     simp
  --   else
  --     simp_all
  --     grind
  -- else
  --   simp [G, GS.mk, M', Matrix.one_apply]
  --   if x = y then
  --     subst_eqs
  --     simp_all
  --     split_ifs
  --     · grind
  --     · simp_all


theorem Q_iter_eq_G (p₁ : RPol[F,N,𝒮]) (x : List Pk[F,N]) :
    Q p₁.Iter x = fun α β ↦ G p₁.Iter ⟨α, x, β⟩ := by
  induction x with
  | nil => sorry
  | cons α₀ x ih =>
    sorry
    -- conv => right; ext a b; rw [G.star_apply']
    -- simp

theorem Q_iter_eq (p₁ : RPol[F,N,𝒮]) {n : ℕ} (x : List.Vector Pk[F,N] n) :
    Q p₁.Iter x.toList = ∑ i ∈ Finset.range n, M' p₁ (x.take i).toList * Q p₁.Iter (x.drop i).toList := by
  induction x with
  | nil =>
    simp
    sorry
  | cons ih =>
    rename_i n' α₀ x
    simp_all

    sorry
  --   simp_all
  --   obtain ⟨x, hx⟩ := x
  --   simp_all
  --   have : x.toList = [] := by simp_all
  --   simp_all
  --   subst_eqs
  --   unfold Q
  --   ext α β
  --   simp [ι, 𝒪]
  --   rw [ι_wProd_𝒪]
  --   simp
  --   sorry
  -- | succ n ih =>
  --   simp_all

attribute [-simp] Function.iterate_succ in
theorem RPol.wnka_sem
    [Encodable F] [Encodable N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]
    [i : LawfulStar 𝒮] (p : RPol[F,N,𝒮]) :
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
    sorry
    -- apply wnka_sem_eq_of'
    -- intro A hA αn
    -- simp_all only

    -- intro A α β
    -- simp [RPol.wnka_seq_δ]
    -- rcases A with _ | ⟨α₀, A⟩
    -- · simp_all
    --   sorry
    -- · rcases A with _ | ⟨α₁, A⟩
    --   · simp_all
    --     sorry
    --   · simp_all [ι, 𝒪]
    --     rw [ι_wProd_δ']
    --     simp
    --     rw [ι_wProd_𝒪]
    --     simp
    --     simp [𝒪.𝒪_heart]
    --     rw [Matrix.mul_assoc]
    --     nth_rw 1 [Matrix.mul_apply]
    --     simp
    --     nth_rw 1 [box_star_iter]
    --     simp [Matrix.add_mul]

    --     have : ∀ (f g : (S.I ↑{♡}) → S p₁ → 𝒮),
    --         Matrix.of (fun a b ↦ f a b + g a b) = Matrix.of f + Matrix.of g := by
    --       intro f g
    --       symm
    --       apply Matrix.of_add_of
    --     simp only [S.I] at this
    --     simp only [this, -Matrix.of_add_of]
    --     simp [-Matrix.of_add_of, Matrix.add_mul]
    --     simp [add_mul]
    --     let n := 1
    --     calc
    --       ((Matrix.of fun a b ↦ ((Matrix.up 1 : 𝒲[𝟙, 𝟙, 𝒲[Pk[F,N], Pk[F,N], 𝒮]]) * ((ι p₁).map Matrix.up * (δ p₁).unfold)) () b α₀ α₁) *
    --                     p₁.upper_left (α₁ :: (A ++ [α])) *
    --                   𝒪 p₁ α β)
    --                 ⟨♡, ⋯⟩ () *
    --               (ι p₁ ⊠ 𝒪 p₁)^* α β +
    --             ((Matrix.of fun a b ↦
    --                       (Matrix.up ((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^*) *
    --                           ((ι p₁).map Matrix.up * (δ p₁).unfold))
    --                         () b α₀ α₁) *
    --                     p₁.upper_left (α₁ :: (A ++ [α])) *
    --                   𝒪 p₁ α β)
    --                 ⟨♡, ⋯⟩ () *
    --               (ι p₁ ⊠ 𝒪 p₁)^* α β =
    --           (G wnk_rpol {~p₁*}) (GS.ofPks (α₀ :: α₁ :: (A ++ [α, β])) ⋯) :=
    --         by sorry





          -- _ = ∑ i ∈ Finset.range n, M' p₁ (A.take i) * Q p₁.Iter (A.drop i) := sorry
          -- _ = (G wnk_rpol {~p₁*}) (GS.ofPks (α₀ :: α₁ :: (A ++ [α, β])) sorry) := sorry
    --     rw [Matrix.mul_apply]
    --     simp
    --     rw [Matrix.mul_apply']
    --     simp

    --     rw [← Matrix.of_add_of]
    --     simp [Equiv.refl]
    --     simp only [DFunLike.coe, EquivLike.coe]
    --     simp
    --     simp [box_eq_M'_of_empty]
    --     rw [G.star_apply']
    --     simp [GS.ofPks, GS.mk, List.dropLast_cons_of_ne_nil]
    --     simp [← ih]
    --     simp

    --     -- nth_rw 2 [box_star_iter]
    --     -- simp [mul_add]
    --     -- rw [Matrix.mul_assoc]
    --     -- nth_rw 1 [Matrix.mul_apply]
    --     -- nth_rw 1 [Matrix.mul_apply]
    --     -- simp
    --     -- simp [box_eq_M'_of_empty]
    --     -- rw [G.star_apply']
    --     -- simp [GS.ofPks, GS.mk, List.dropLast_cons_of_ne_nil]
    --     -- simp [← ih]
    --     -- simp

    --     -- simp [Matrix.mul_apply]
    --     simp [𝒪.𝒪_heart, LawfulStar.star_eq_sum]
    --     simp [G, GS.ofPks]
    --     simp [G.iter]
    --     simp [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply, ← ωSum_mul_right, ← ωSum_mul_left]
    --     simp [Matrix.of]
    --     simp [Equiv.refl]
    --     simp only [DFunLike.coe, EquivLike.coe]
    --     rw [Matrix.mul_assoc]
    --     rw [Matrix.mul_apply]
    --     simp
    --     simp [← Matrix.mul_assoc]
    --     simp [← Matrix.ωSum_mul_right, Matrix.of_ωSum']
    --     simp [Matrix.mul_assoc]
    --     rw [← Matrix.ωSum_mul_right]
    --     simp [← ωSum_mul_right]
    --     conv =>
    --       left
    --       arg 1
    --       ext x
    --       arg 1
    --       ext y
    --       rw [Matrix.mul_apply]
    --     simp [ωSum_mul_right]
    --     simp [ωSum_mul_left]
    --     unfold WeightedConcat.concat
    --     simp [instWeightedConcatCountsuppGS]


    -- induction A with
    -- | nil =>
    --   simp [WNKA.compute']
    --   simp [ι]
    --   simp [𝒪, 𝒪.𝒪_heart]
    --   rw [ι_wProd_𝒪]
    --   simp [Matrix.mul_apply]
    --   simp [G, G.iter, GS.ofPks, GS.mk]
    --   simp [LawfulStar.star_eq_sum]
    --   sorry
    -- | cons α₀ A ih =>
    --   clear ih
    --   induction A with
    --   | nil => sorry
    --   | cons α₁ A ih =>
    --     clear ih
    --     simp [WNKA.compute', δ]
    --     induction A with
    --     | nil => sorry
    --     | cons α₂ A ih =>
    --       clear ih
    --       simp [WNKA.compute', δ]
    --       induction A with
    --       | nil => sorry
    --       | cons α₃ A ih =>
    --         clear ih
    --         simp [WNKA.compute', δ]
    --         simp [Matrix.mul_assoc]
    --         nth_rw 2 [← Matrix.mul_assoc]
    --         simp [δ_wProd_δ]
    --         nth_rw 2 [← Matrix.mul_assoc]
    --         simp [δ_wProd_δ]

    -- -- simp [RPol.wnka_seq_δ]
    -- -- simp [G, GS.ofPks, GS.mk, ← List.tail_dropLast, List.head_append]
    -- -- simp [G.iter]
    -- -- simp [G]
    -- -- intro A α α'
    -- -- if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    -- -- simp [RPol.upper_left]
    -- -- rcases A with _ | ⟨α₀, A⟩
    -- -- · simp [ι, 𝒪]
    -- --   rw [ι_wProd_𝒪]
    -- --   simp
    -- --   simp [Matrix.mul_apply]
    -- --   simp [𝒪.𝒪_heart]
    -- --   sorry
    -- --   -- have : @Finset.card (𝟙 × S.I {♡}) (Finsupp.support (1 : 𝟙 × S.I {♡} →₀ 𝒮)) = 1 := by
    -- --   --   refine Finset.card_eq_one.mpr ?_
    -- --   --   simp
    -- --   --   use ()
    -- --   --   ext ⟨_, ⟨_, _, _⟩⟩
    -- --   --   simp_all
    -- --   -- simp only [this, Nat.cast_one, one_mul]; clear this
    -- --   -- congr with n
    -- --   -- induction n with
    -- --   -- | zero =>
    -- --   --   simp [𝒞.pow, GS.mk, h10]
    -- --   --   sorry
    -- --   -- | succ n ih =>
    -- --   --   simp only [Function.iterate_succ', Function.comp_apply]
    -- --   --   simp [𝒞.pow]
    -- --   --   nth_rw 1 [Matrix.mul_apply]
    -- --   --   rw [instWeightedProductFinsuppProdOfDecidableEq]
    -- --   --   simp
    -- --   --   rw [ih]
    -- --   --   nth_rw 2 [WeightedConcat.concat]
    -- --   --   nth_rw 2 [instWeightedConcatCountsuppGS]
    -- --   --   simp
    -- --   --   sorry
    -- --     -- simp
    -- --     -- have : ∀ x, @Finset.card (𝟙 × 𝟙) x = if x = ∅ then 0 else 1 := by
    -- --     --   intro x
    -- --     --   split_ifs with h
    -- --     --   · simp_all
    -- --     --   · refine Finset.card_eq_one.mpr ?_
    -- --     --     simp
    -- --     --     use (), ()
    -- --     --     ext ⟨_, _⟩
    -- --     --     simp_all
    -- --     --     sorry
    -- --     -- simp [this]; clear this
    -- --     -- split_ifs with h
    -- --     -- · sorry
    -- --     -- · sorry





    -- --   -- sorry
    -- -- · rcases A with _ | ⟨α₁, A⟩
    -- --   · simp
    -- --     sorry
    -- --   · simp
    -- --     simp [ι]
    -- --     rw [ι_wProd_δ']
    -- --     simp [𝒪]
    -- --     rw [ι_wProd_𝒪]
    -- --     simp
    -- --     simp [← Matrix.mul_assoc, 𝒪.𝒪_heart, δ.𝒪_heart]
    -- --     sorry


end WeightedNetKAT
