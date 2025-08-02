import WeightedNetKAT.Language
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Star
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Action.Opposite

open OmegaCompletePartialOrder
open scoped RightActions

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
def down_up {A B α : Type} [AddCommMonoid α] [Unique A] [Unique B] (a : α) :
    (Matrix.up a : Matrix A B α).down = a := by simp [down, up]
@[simp]
def up_down {A B α : Type} [AddCommMonoid α] [Unique A] [Unique B] (m : Matrix A B α) :
    (Matrix.up m.down : Matrix A B α) = m := by simp [down]; ext; simp; congr <;> apply Unique.default_eq

@[simp]
def down_sum {ι A B α : Type} [AddCommMonoid α] [Unique A] [Unique B] (f : ι → Matrix A B α) (S : Finset ι) :
    (∑ x ∈ S, f x).down = ∑ x ∈ S, (f x).down := by
  simp [down, Matrix.sum_apply]
@[simp]
def down_add {A B α : Type} [AddCommMonoid α] [Unique A] [Unique B] (m m' : Matrix A B α) :
    (m + m').down = m.down + m'.down := by
  simp [down]
@[simp]
def down_mul {A B C α : Type} [NonUnitalSemiring α] [Unique A] [Unique B] [Unique C] (m : Matrix A B α) (m' : Matrix B C α) :
    (m * m').down = m.down * m'.down := by
  simp [down, Matrix.mul_apply]
@[simp]
def down_mul_right {A B α : Type} [NonUnitalSemiring α] [Unique A] [Unique B] (m : Matrix A B α) (s : α) :
    (m <• s).down = m.down * s := by
  simp [down]
@[simp]
def down_zero {A B α : Type} [AddCommMonoid α] [Unique A] [Unique B] :
    (0 : Matrix A B α).down = 0 := by
  simp [down]
@[simp]
def down_smul_left {A B α : Type} [NonUnitalSemiring α] [Unique A] [Unique B] (m : Matrix A B α) (r : α) :
    (r •> m).down = r •> m.down := by
  simp [down]
@[simp]
def down_smul_right {A B α : Type} [NonUnitalSemiring α] [Unique A] [Unique B] (m : Matrix A B α) (r : α) :
    (m <• r).down = m.down <• r := by
  simp [down]

@[simp]
theorem up_add {A B α : Type} [AddCommMonoid α] (a b : α) : Matrix.up (A:=A) (B:=B) (a + b) = ↑a + ↑b := rfl

def coe_unique_left {A A' B α : Type} [Unique A] [Unique A'] (m : Matrix A B α) : Matrix A' B α :=
  fun _ b ↦ m default b

theorem coe_unique_left_fun {A A' B α : Type} [Unique A] [Unique A'] (f : A → B → α) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) (fun a b ↦ f a b) = fun _ b ↦ f default b := rfl
@[simp]
theorem coe_unique_left_apply {A A' B α : Type} [Unique A] [Unique A'] (f : A → B → α) (a : A') (b : B) :
    coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) f a b = f default b := by
  simp [coe_unique_left]
@[simp]
theorem coe_unique_left_coe_unique_left {A A' A'' B α : Type} [Unique A] [Unique A'] [Unique A''] (f : A → B → α) :
    coe_unique_left (A:=A') (A':=A'') (B:=B) (α:=α) (coe_unique_left (A:=A) (A':=A') (B:=B) (α:=α) f) = coe_unique_left (A:=A) (A':=A'') (B:=B) (α:=α) f := by
  ext; simp
@[simp]
theorem coe_unique_left_idem {A B α : Type} [Unique A] (f : A → B → α) :
    coe_unique_left (A:=A) (A':=A) (B:=B) (α:=α) f = f := by
  ext; simp; congr; apply Unique.default_eq
@[simp]
theorem coe_unique_left_mul {A A' B C α : Type} [Unique A] [Unique A'] [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    [AddCommMonoid α] [Mul α]
    (f : Matrix A B α) (g : Matrix B C α) :
    coe_unique_left (A:=A) (A':=A') (B:=C) (α:=α) (f * g) = coe_unique_left f * g  := by
  ext a c
  simp [Matrix.mul_apply]

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

-- def box {X} [DecidableEq X] [Fintype X]
--     (l : Matrix 𝟙 X 𝒮) (r : Matrix Pk[F,N] Pk[F,N] (Matrix X 𝟙 𝒮)) :
--     𝒲[Pk[F,N],Pk[F,N],𝒮] := fun α β ↦ (l * r α β).down

def box {X} [DecidableEq X] [Fintype X] {Q : Type} [Mul Q] [AddCommMonoid Q] {Z : Type} [DecidableEq Z] [Fintype Z] [Unique Z]
    (l : 𝒲[Z, X, Q]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[X, Z, Q]]) :
    𝒲[Pk[F,N],Pk[F,N],Q] :=
  fun α β ↦ (l * r α β).down -- <-------

infixr:50 " ⊠ " => box

def fox {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    (l : 𝒲[A, B, Q]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[B, C, Q]]) :
    𝒲[Pk[F,N], Pk[F,N], 𝒲[A, C, Q]] :=
  fun α β ↦ l * r α β -- <-------

infixr:50 " ⊡ " => fox

def sox {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    (l : 𝒲[Pk[F,N], Pk[F,N], Q]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]]) :
    𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]] :=
  fun α β ↦ ∑ m, l α m • r m β

infixr:50 " ⊟ " => sox

omit [Encodable F] [Listed F] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] in
theorem add_sox {A B : Type} {Q : Type} [NonUnitalSemiring Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    (l l' : 𝒲[Pk[F,N], Pk[F,N], Q]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]]) :
    ((l + l') ⊟ r) = (l ⊟ r) + (l' ⊟ r) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, add_mul, Finset.sum_add_distrib]

omit [Encodable F] [Listed F] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] in
theorem mul_sox {A B : Type} {Q : Type} [NonUnitalSemiring Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    (l l' : 𝒲[Pk[F,N], Pk[F,N], Q]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]]) :
    ((l * l') ⊟ r) = (l ⊟ (l' ⊟ r)) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

omit [Encodable F] [Listed F] [Encodable N] [Listed N] [Inhabited N] in
@[simp]
theorem one_sox {A B : Type} {Q : Type} [Semiring Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B]
    (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]]) :
    ((1 : 𝒲[Pk[F,N], Pk[F,N], Q]) ⊟ r) = r := by
  ext α β a b
  simp [sox, Matrix.one_apply]

def crox {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [DecidableEq A] [Fintype A] [DecidableEq B] [Fintype B] [DecidableEq C] [Fintype C]
    (l : 𝒲[Pk[F,N], Pk[F,N], 𝒲[A, B, Q]]) (r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[B, C, Q]]) :
    𝒲[Pk[F,N], Pk[F,N], 𝒲[A, C, Q]] :=
  fun α β ↦ ∑ m, l α m * r m β -- <-------
  -- fun α β ↦ ∑ m, l α m * r m β -- <-------

infixr:50 " ⊞ " => crox

mutual

def 𝒪_heart (p₁ : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] 𝒮 := (ι p₁ ⊠ 𝒪 p₁)^*

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
      -- NOTE: this differs from the paper!!!!!
      -- 𝒪 p₁ α β <• 𝒪_heart p₁ α β,
      ∑ γ, 𝒪 p₁ α γ <• 𝒪_heart p₁ γ β,
      𝒪_heart p₁ α β
    ]

end

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
    -- let q : 𝒲[Pk[F,N], Pk[F,N], 𝒲[𝟙, S p₁, 𝒮]] := fun a b ↦ ∑ γ, 𝒪_heart p₁ a γ • ι p₁ * δ p₁ γ b
    -- let y : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S.I {♡}, S p₁, 𝒮]] := q.map (·.coe_unique_left)
    -- let g : 𝒲[Pk[F,N], Pk[F,N], 𝒮] := 𝒪_heart p₁
    -- let y : 𝒲[Pk[F,N], Pk[F,N], 𝒲[𝟙, S p₁, 𝒮]] := (ι p₁ ⊡ δ p₁)
    -- let q :=

    -- let y : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S.I {♡}, S p₁, 𝒮]] := fun i j x b ↦ ∑ x, (𝒪_heart p₁) i x * (ι p₁ * (δ p₁) x j) PUnit.unit b
    -- let y : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S.I {♡}, S p₁, 𝒮]] := fun i j x b ↦ ∑ m, g i m * y m j x b
    -- let q : 𝒲[Pk[F,N], Pk[F,N], 𝒲[𝟙, S p₁, 𝒮]] := (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁)
    -- let z : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, 𝟙, 𝒮]] := 𝒪 p₁
    -- let r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, S p₁, 𝒮]] := 𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁
    -- let δ' := δ p₁ + 𝒪 p₁ * (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁)
    δ[[δ' p₁ α β, 0],
      [((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α β).coe_unique_left, 0]]
where δ' (p₁ : RPol[F,N,𝒮]) := δ p₁ + (𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁)
-- where δ' (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) := δ p₁ α β + 𝒪 p₁ α β * (𝒪_heart p₁ α β • ι p₁ * δ p₁ α β)

example {p₁ : RPol[F,N,𝒮]} {α β} : (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α β = ∑ x, (ι p₁ ⊠ 𝒪 p₁)^* α x •> (ι p₁ * δ p₁ x β) := by
  simp [sox, fox, 𝒪_heart]
-- example {p₁ : RPol[F,N,𝒮]} {α β} : δ.δ' p₁ α β = sorry := by
--   simp [δ.δ', sox, fox, crox, Matrix.mul_sum]

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

noncomputable def N'_ij (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) (i : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  M' p (xᵢ.take i) * M' p.Iter (xᵢ.drop i)

noncomputable def N' (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  ∑ i ∈ Finset.range xᵢ.length, N'_ij p xᵢ (i + 1)

omit [DecidableEq 𝒮] [Star 𝒮] in
theorem G.star_apply (p₁ : RPol[F,N,𝒮]) (α : Pk[F,N]) (s : Str[F,N]) (β : Pk[F,N]) :
      ((G p₁.Iter) : _ →c 𝒮) (α, s, β)
    = (G RPol.Skip) (α, s, β) +
        (∑ γ, (G p₁) (α, [], γ) * (G p₁.Iter) (γ, s, β)) +
          ∑ i ∈ Finset.range s.length,
            (M' p₁ (s.x (i + 1)) * M' p₁.Iter (s.y (i + 1))) α β := by
  unfold M'
  simp [G]
  rw [ωSum_nat_eq_succ]
  simp
  conv => left; right; arg 1; ext x; rw [G]
  simp [G.concat_apply]
  nth_rw 2 [add_comm]
  simp [Finset.sum_range_add]
  conv => left; right; arg 1; ext x; left; arg 2; ext y; rw [GS.splitAtJoined]
  simp [ωSum_add]
  simp [G]
  simp [Matrix.mul_apply]
  simp [← ωSum_mul_left, ωSum_sum_comm]
  simp [ωSum_mul_left]
  rw [add_assoc]
  congr
  ext n
  congr with γ
  congr
  · simp [GS.splitAtJoined, Str.x]
    rw [add_comm]
    congr
  · simp [GS.splitAtJoined, Str.y]
    ext
    rw [add_comm]
    congr

omit [DecidableEq 𝒮] [Star 𝒮] in
theorem G.star_apply' (p₁ : RPol[F,N,𝒮]) (s : GS[F,N]) :
      ((G p₁.Iter) : _ →c 𝒮) s
    = (G RPol.Skip) s +
        (∑ γ, (G p₁) (s.1, [], γ) * (G p₁.Iter) (γ, s.2.1, s.2.2)) +
          ∑ i ∈ Finset.range s.2.1.length,
            (M' p₁ (s.2.1.take (i + 1)) * M' p₁.Iter (s.2.1.drop (i + 1))) s.1 s.2.2 := by
  obtain ⟨α, s, β⟩ := s
  convert G.star_apply p₁ α ⟨s⟩ β

omit [DecidableEq 𝒮] [Star 𝒮] in
theorem M'.iter_eq (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) :
    M' p₁.Iter xₙ =
      if xₙ = [] then
        1 + M' p₁ [] * M' p₁.Iter xₙ
      else
        N' p₁ xₙ + M' p₁ [] * M' p₁.Iter xₙ := by
  split_ifs
  · subst_eqs
    unfold M'
    ext α β
    convert G.star_apply p₁ α ⟨[]⟩ β
    simp [Matrix.add_apply, Str.length]
    congr
    · simp [G, GS.mk, Matrix.one_apply]; split_ifs with _ h
      · rfl
      · subst_eqs; contrapose! h; use α; rfl
      · grind
      · rfl
  · conv => left; unfold M'
    ext α β
    convert G.star_apply p₁ α ⟨xₙ⟩ β
    simp
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    rw [add_comm]
    have : G (F:=F) (N:=N) (𝒮:=𝒮) RPol.Skip (α, ↑({ xs := xₙ } : Str _ _), β) = 0 := by
      simp [G, h10, GS.mk]; intro x hx; obtain ⟨_⟩ := hx; contradiction
    simp [this]; clear this
    rw [Matrix.mul_apply]
    congr
    rw [N']
    simp [Str.length, Str.x, Matrix.sum_apply, Str.coe, N'_ij]
    congr

def fp₀ (p₁ : RPol[F,N,𝒮]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  Z = 1 + M' p₁ [] * Z
noncomputable def eq₁ (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  N' p₁ xₙ + M' p₁ [] * Z
def fp₁ (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  Z = N' p₁ xₙ + M' p₁ [] * Z

noncomputable def Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ p.wnka.sem ⟨α, xᵢ, β⟩

noncomputable def N'Q_ij (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) (i : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  Q p (xᵢ.take i) * Q p.Iter (xᵢ.drop i)

noncomputable def N'Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  ∑ i ∈ Finset.range xᵢ.length, N'Q_ij p xᵢ (i + 1)

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
    simp [𝒪_heart]
    simp [Matrix.mul_apply]
    simp [LawfulStar.star_eq_sum]
    simp [G.iter]
    congr with n
    induction n generalizing α β with
    | zero => simp [G, GS, G.ofPk, Matrix.one_apply, GS.mk]
    | succ n ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      simp [pow_succ']
      simp [Matrix.mul_apply]
      simp [ih']; clear ih'
      rw [G.concat_apply]
      simp [GS.splitAtJoined]
      simp [← ih]
      rfl
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp [← ih₁, ← ih₂]
  | Weight w p ih =>
    simp [ι, 𝒪, G]
    simp [← ih]

theorem 𝒪_heart_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (𝒪_heart p₁) := by
  constructor
  · simp [fp₀, 𝒪_heart, LawfulStar.star_eq_sum, ← Matrix.ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    congr! with n
    rw [pow_succ', box_eq_M'_of_empty]
  · intro g hg
    simp [fp₀] at hg
    symm at hg
    simp [𝒪_heart, LawfulStar.star_eq_sum]
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

theorem box_star_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := 𝒪_heart_fp₀ p₁
  simpa [𝒪_heart]

theorem M_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (M' p₁ [])^* := by
  constructor
  · simp [fp₀]
    simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    simp [pow_succ']
  · intro g hg
    simp [fp₀] at hg
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

theorem Q_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (Q p₁ [])^* := by
  constructor
  · simp [fp₀]
    simp [LawfulStar.star_eq_sum, ← ωSum_mul_left]
    rw [ωSum_nat_eq_succ]
    simp
    congr! with n
    simp [pow_succ']
    congr
    rw [← box_eq_M'_of_empty]
    rfl
  · intro g hg
    simp [fp₀] at hg
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

theorem M_empty_star_eq_heart (p₁ : RPol[F,N,𝒮]) : (M' p₁ [])^* = (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := (IsLeast.unique (𝒪_heart_fp₀ p₁) (M_fp₀ p₁)).symm
  simpa [𝒪_heart]

theorem Q_star_eq_box (p₁ : RPol[F,N,𝒮]) : (Q p₁ [])^* = (ι p₁ ⊠ 𝒪 p₁)^* :=
  IsLeast.unique (Q_fp₀ p₁) (box_star_fp₀ p₁)

theorem box_star_iter (p₁ : RPol[F,N,𝒮]) : (ι p₁ ⊠ 𝒪 p₁)^* = 1 + (ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := 𝒪_heart_fp₀ p₁ |>.left
  simp [fp₀, 𝒪_heart] at this
  rw [← box_eq_M'_of_empty] at this
  assumption

def RPol.upper_left (p : RPol[F,N,𝒮]) (A : List Pk[F,N]) : Matrix (S p) (S p) 𝒮 :=
  match A with
  | [] | [_] => 1
  | α::α'::A => δ.δ' p α α' * p.upper_left (α' :: A)

@[simp]
theorem G.skip_eq_one' {α β : Pk[F,N]} : G RPol.Skip ⟨α, [], β⟩ = M' (𝒮:=𝒮) (F:=F) (N:=N) RPol.Skip [] α β := by
  rfl
theorem G.skip_eq_one {α β : Pk[F,N]} {x} : G (𝒮:=𝒮) RPol.Skip ⟨α, x, β⟩ = if x.length = 0 ∧ α = β then 1 else 0 := by
  split_ifs
  · simp_all [G, GS.mk]
  · simp_all [G, GS.mk]
    grind

theorem fp₀_M' (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (M' p₁.Iter []) := by
  constructor
  · simp [fp₀]
    nth_rw 1 [M'.iter_eq]
    simp
  · simp [fp₀]
    intro g hg
    simp at hg; symm at hg
    intro α β
    simp [M', G, ωSum_nat_eq_ωSup]
    simp only [DFunLike.coe]
    intro i
    induction i generalizing α with
    | zero =>
      apply le_trans (b:=0)
      · rfl
      · simp
    | succ i ih =>
      rw [add_comm]
      simp [Finset.sum_range_add]
      have : ∀ {X Y} [Zero Y] (c : Countsupp X Y) (x :X), c.toFun x = c x := by intros; rfl
      simp [this]
      rw [← hg]
      simp
      gcongr
      · simp only [M', G, G.ofPk, GS.mk, Matrix.one_apply]
        simp only [Countsupp.coe_mk]
        apply le_of_eq
        split_ifs <;> grind
      · simp [add_comm]
        simp [G]
        simp [G.concat_apply, GS.splitAtJoined, Matrix.mul_apply]
        rw [Finset.sum_comm]
        gcongr with α' hα'
        simp [← Finset.mul_sum]
        gcongr
        · rfl
        · apply le_trans _ (ih α')
          simp [this]
omit [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem fp₁_M' (p₁ : RPol[F,N,𝒮]) (xₙ) (hxₙ : xₙ ≠ []) : IsLeast {f | fp₁ p₁ xₙ f} (M' p₁.Iter xₙ) := by
  constructor
  · simp [fp₁]
    nth_rw 1 [M'.iter_eq]
    simp [hxₙ]
  · intro g hg
    simp only [fp₁, Set.mem_setOf_eq] at hg; symm at hg
    intro α β
    simp [M', G, ωSum_nat_eq_ωSup]
    have : ∀ {X Y} [Zero Y] (c : Countsupp X Y) (x :X), c.toFun x = c x := by intros; rfl
    simp only [DFunLike.coe]
    simp [this]
    intro i
    induction i generalizing α with
    | zero => simp
    | succ i ih =>
      rw [Finset.sum_range_succ']
      nth_rw 1 [add_comm]
      simp [G, GS.mk]
      split_ifs
      · grind
      simp_all
      rw [← hg]
      simp
      simp [G.concat_apply, GS.splitAtJoined]
      rw [Finset.sum_comm]
      rw [Finset.sum_range_succ']
      gcongr
      · simp [N', Matrix.sum_apply]
        gcongr with n hn
        simp [N'_ij]
        simp [Matrix.mul_apply, M', G, ← ωSum_mul_left]
        rw [← ωSum_sum_comm]
        exact le_ωSum_of_finset (Finset.range i)
      · simp
        simp [Matrix.mul_apply]
        rw [Finset.sum_comm]
        gcongr with α'
        simp [← Finset.mul_sum]
        gcongr
        · rfl
        · apply ih

@[simp]
theorem Q_empty (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) :
    Q p₁.Iter [] α β = (ι p₁ ⊠ 𝒪 p₁)^* α β := by
  simp [Q, ι, 𝒪]
  rw [ι_wProd_𝒪]
  simp [Matrix.mul_apply, 𝒪_heart]

theorem fp₀_Q (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (Q p₁.Iter []) := by
  have : Q p₁.Iter [] = (ι p₁ ⊠  𝒪 p₁)^* := by
    unfold Q
    ext α β
    simp [ι, 𝒪]
    rw [ι_wProd_𝒪]
    simp [𝒪_heart, Matrix.mul_apply]
  simp [this]; clear this
  constructor
  · simp [fp₀]
    nth_rw 1 [box_star_iter]
    congr
    exact box_eq_M'_of_empty p₁
  · intro g hg
    simp only [fp₀, Set.mem_setOf_eq] at hg; symm at hg
    rw [← box_eq_M'_of_empty] at hg
    simp [LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, DFunLike.coe]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.sum_range_succ']
      simp
      rw [add_comm]
      rw [← hg]
      gcongr
      simp [pow_succ', ← Finset.mul_sum]
      gcongr

theorem Q_empty_eq_M'_empty (p₁ : RPol[F,N,𝒮]) : Q p₁.Iter [] = M' p₁.Iter [] :=
  IsLeast.unique (fp₀_Q p₁) (fp₀_M' p₁)

-- def xδ {p₁ : RPol[F,N,𝒮]} (d : Pk[F,N] → Pk[F,N] → 𝒲[S p₁, S p₁, 𝒮]) (xs : List Pk[F,N]) : 𝒲[S p₁, S p₁, 𝒮] :=
def xδ {X : Type} [DecidableEq X] [Fintype X] (d : Pk[F,N] → Pk[F,N] → 𝒲[X, X, 𝒮]) (xs : List Pk[F,N]) : 𝒲[X, X, 𝒮] :=
  match xs with
  | [] | [_] => 1
  | α::α'::xs => d α α' * xδ d (α'::xs)

omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_idk {p₁ : RPol[F,N,𝒮]} {α α₀ : Pk[F,N]} {xₙ : List Pk[F,N]} :
      (xδ (δ p₁.Iter) (α :: α₀ :: xₙ) : 𝒲[S wnk_rpol {~p₁*}, S wnk_rpol {~p₁*}, 𝒮])
    = δ[[xδ (δ.δ' p₁) (α :: α₀ :: xₙ),0],
        [(((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀) * (xδ (δ.δ' p₁) (α₀::xₙ))).coe_unique_left,0]] := by
  induction xₙ generalizing α α₀ with
  | nil => simp only [xδ, δ, S.I, 𝒪_heart, mul_one, Matrix.mul_one]
  | cons α₁ xₙ ih => rw [xδ, ih, δ, δ_wProd_δ]; simp [xδ]

omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_idk' {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} :
      (xδ (δ p₁.Iter) (α :: xₙ) : 𝒲[S wnk_rpol {~p₁*}, S wnk_rpol {~p₁*}, 𝒮])
    = δ[[xδ (δ.δ' p₁) (α :: xₙ),0],
        [if xₙ = [] then 0 else (((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α xₙ.head!) * (xδ (δ.δ' p₁) xₙ)).coe_unique_left,if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp only [xδ, S.I, ↓reduceIte, S.δ_identity]
  | cons α₁ xₙ ih => rw [xδ, ih, δ, δ_wProd_δ]; simp [xδ]

omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_as_sum {p : RPol[F,N,𝒮]} {xₙ} {α'} :
      xδ (δ.δ' p) (xₙ ++ [α'])
    = xδ (δ p) (xₙ ++ [α']) +
      ∑ n ∈ Finset.range (xₙ.length),
          xδ (δ p) ((xₙ ++ [α']).take (n + 1))
        * (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p) xₙ[n]! (xₙ ++ [α'])[n + 1]!
        * xδ (δ p + (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p)) ((xₙ ++ [α']).drop (n + 1)) := by
  rcases xₙ with _ | ⟨α₁, xₙ⟩
  · simp [xδ]
  induction xₙ generalizing α₁ with
  | nil => simp [xδ, δ.δ']
  | cons α₂ xₙ ih =>
    simp [δ.δ', xδ] at ih ⊢
    rw [ih]
    simp [add_mul, mul_add, add_assoc]
    congr
    simp [Finset.mul_sum, ← Finset.sum_add_distrib]
    nth_rw 2 [Finset.sum_range_succ']
    simp [xδ]
    rw [ih]; clear ih
    simp only [mul_add]
    rw [add_comm]
    nth_rw 8 [add_comm]
    simp [add_assoc, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.wnka_sem_case (p₁ : RPol[F,N,𝒮]) {γ α' β} {xₙ} :
      p₁.wnka.sem (γ, (xₙ ++ [α']), β)
    = (ι p₁ * xδ (δ p₁) (γ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β).down := by
  simp [WNKA.sem, Matrix.down, Matrix.mul_assoc]
  congr! 1
  simp [GS.pks]
  simp only [← List.cons_append]
  rw [WNKA.compute_pair]
  simp
  congr
  generalize (γ :: (xₙ ++ [α'])) = A
  induction A with
  | nil => simp [WNKA.compute', xδ]
  | cons x A =>
    induction A with
    | nil => simp [WNKA.compute', xδ]
    | cons x A => simp_all [WNKA.compute', xδ]

omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.wnka_sem_case' (p₁ : RPol[F,N,𝒮]) {α β} {xₙ} :
      p₁.wnka.sem (α, xₙ, β)
    = (ι p₁ * xδ (δ p₁) (α :: xₙ) * 𝒪 p₁ (xₙ.getLastD α) β).down := by
  simp [WNKA.sem, Matrix.down, Matrix.mul_assoc]
  congr! 1
  simp [GS.pks]
  simp only [← List.cons_append]
  induction xₙ using List.reverseRecOn with
  | nil => simp [WNKA.compute, xδ]
  | append_singleton xₙ α' ih =>
    simp
    rw [← List.cons_append]
    rw [WNKA.compute_pair]
    simp
    congr
    generalize (α :: (xₙ ++ [α'])) = A
    induction A with
    | nil => simp [WNKA.compute', xδ]
    | cons x A =>
      induction A with
      | nil => simp [WNKA.compute', xδ]
      | cons x A => simp_all [WNKA.compute', xδ]

omit [Fintype F] [DecidableEq F] [Encodable F] [Listed F] [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Matrix.smul_apply' (r : 𝒮) (A : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) (i j : Pk[F,N]) :
    (A <• r) i j = (A i j) •> r := rfl

omit [Fintype F] [DecidableEq F] [Encodable F] [Listed F] [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem Finset.sum_smul' {X Y : Type} [DecidableEq X] [Fintype X] [DecidableEq Y] [Fintype Y] {ι : Type} [DecidableEq ι] (f : ι → 𝒮) (S : Finset ι) (r : 𝒲[X, Y, 𝒮]) :
    (∑ x ∈ S, f x) •> r = (∑ x ∈ S, f x •> r) := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all
    ext α β
    simp_all [add_mul, Finset.sum_mul, Matrix.sum_apply]

omit [Fintype F] [DecidableEq F] [Encodable F] [Listed F] [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem Matrix.sum_smul' {X Y : Type} [DecidableEq X] [Fintype X] [DecidableEq Y] [Fintype Y] {ι : Type} [DecidableEq ι] (f : ι → 𝒲[X,Y,𝒮]) (S : Finset ι) (r : 𝒮) :
    (∑ x ∈ S, f x) <• r = (∑ x ∈ S, f x <• r) := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all

omit [Fintype F] [DecidableEq F] [Encodable F] [Listed F] [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem one_mul_coe_unique_left {p₁ : RPol[F,N,𝒮]} {y : 𝒲[𝟙, S p₁, 𝒮]} :
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (fun _ ↦ 1 : 𝟙 → S.I {♡} → 𝒮) y.coe_unique_left = y := by
  ext
  simp [Matrix.mul_apply]

omit [Fintype F] [DecidableEq F] [Encodable F] [Listed F] [Fintype N] [DecidableEq N] [Encodable N] [Listed N] [Inhabited N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq 𝒮] [Star 𝒮] [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem ι_add_zero_mul {p₁ : RPol[F,N,𝒮]} {a b : 𝒲[𝟙, S p₁, 𝒮]} {c : 𝒲[S wnk_rpol {~p₁*}, S wnk_rpol {~p₁*}, 𝒮]} :
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (ι[a + b, 0] : 𝒲[𝟙, S p₁ ⊕ (↑{♡} : Set _), 𝒮]) c
    = Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul ι[a, 0] c + Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul ι[b, 0] c := by
  unfold S.ι
  simp
  ext
  simp [Matrix.mul_apply, right_distrib, Finset.sum_add_distrib]

set_option maxHeartbeats 500000 in
theorem fp₁_Q_is_fp (p₁ : RPol 𝒮) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) :
    Q wnk_rpol {~p₁*} xₙ = N'Q p₁ xₙ + Q p₁ [] * Q wnk_rpol {~p₁*} xₙ := by
  induction xₙ using List.reverseRecOn with
  | nil => contradiction
  | append_singleton xₙ α' ih =>
    induction xₙ with
    | nil =>
      clear ih hxₙ -- these are not applicable when xₙ is empty
      simp
      conv => left; unfold Q
      ext α β
      simp [RPol.wnka_sem_case', ι, 𝒪, δ, xδ]
      rw [ι_wProd_δ', ι_wProd_𝒪]
      simp
      rw [one_mul_coe_unique_left]
      nth_rw 1 [𝒪_heart]
      nth_rw 1 [box_star_iter]
      rw [add_sox]
      simp [Matrix.add_mul, fox, N'Q, N'Q_ij]
      congr
      · unfold Q
        simp
        simp [ι, 𝒪]
        conv => right; arg 2; ext a b; rw [ι_wProd_𝒪]
        simp [RPol.wnka_sem_case', xδ, Matrix.mul_apply, 𝒪_heart, Matrix.mul_sum]
      · unfold Q
        simp [RPol.wnka_sem_case', ι, 𝒪, xδ, δ]
        conv => right; arg 2; ext s t; rw [ι_wProd_δ', ι_wProd_𝒪, one_mul_coe_unique_left]
        simp
        rw [Matrix.mul_apply]
        simp [Matrix.mul_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr with γ
        conv => right; arg 2; ext; rw [← mul_assoc]
        simp [← Finset.sum_mul]
        congr
        generalize (ι p₁ ⊡ δ p₁) = s
        rw [mul_sox, sox]
        simp [Matrix.sum_mul, box, 𝒪_heart]
    | cons α₁ xₙ ih' =>
      clear ih' hxₙ ih
      conv => left; unfold Q
      simp only [RPol.wnka_sem_case]
      ext α β
      simp [ι, 𝒪, δ, xδ, ← Matrix.mul_assoc]
      rw [ι_wProd_δ']
      simp
      rw [one_mul_coe_unique_left]
      nth_rw 1 [𝒪_heart]
      nth_rw 1 [box_star_iter]
      rw [add_sox]
      simp [fox]
      rw [ι_add_zero_mul]
      simp [Matrix.add_mul]
      congr
      · simp [N'Q, N'Q_ij]
        rw [xδ_idk', ι_wProd_δ', ι_wProd_𝒪]
        simp
        rw [← List.cons_append, xδ_as_sum]
        simp
        nth_rw 2 [Finset.sum_range_succ]
        simp [Matrix.mul_add, Matrix.add_mul]
        nth_rw 3 [Matrix.mul_sum]
        simp [Matrix.sum_mul, Matrix.sum_apply]
        nth_rw 4 [add_comm]
        congr! 2 with n hn
        · unfold Q
          simp [RPol.wnka_sem_case', xδ, ι, 𝒪]
          have : List.take (xₙ.length + 1) (xₙ ++ [α']) = (xₙ ++ [α']) := by simp
          simp [this]; clear this
          conv => right; arg 2; ext α β; rw [ι_wProd_𝒪]
          rw [Matrix.mul_apply]
          have : Matrix.down (fun (x : 𝟙) ↦ (1 : S.I {♡} → 𝒮)) = 1 := rfl
          simp [List.getLast?_cons, Matrix.mul_sum, ← Matrix.mul_assoc, this]
        · unfold Q
          simp [Matrix.mul_apply, Matrix.mul_sum, RPol.wnka_sem_case', ι, xδ, ← Matrix.mul_assoc, Matrix.mul_sum, 𝒪]
          simp at hn
          have : ¬xₙ.length + 1 ≤ n := by omega
          -- TODO: try to use xδ_idk' ealier in the proof!
          generalize ι p₁ * δ p₁ α α₁ * xδ (δ p₁) (α₁ :: List.take n (xₙ ++ [α'])) = A
          simp [List.getLast?_drop, this, List.getLast?_cons]
          simp [crox, Matrix.mul_sum, Matrix.sum_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          congr with γ
          simp [← Matrix.mul_assoc]
          nth_rw 1 [Matrix.mul_assoc]
          simp_all only [not_le, List.length_cons, getElem?_pos, Option.getD_some,
            List.length_append, List.length_nil, zero_add]
          conv => left; arg 2; ext; rw [← Matrix.down_mul_right]
          rw [← Matrix.down_mul_right, ← Matrix.down_sum]
          congr
          simp [← Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_sum]
          congr
          ext S _
          rw [Matrix.mul_apply]
          simp
          congr
          · grind
          have : ¬xₙ.length + 1 ≤ n := by omega
          simp [Matrix.down, xδ_idk', ← Matrix.mul_assoc, ι_wProd_δ', ι_wProd_𝒪, this]
          rw [one_mul_coe_unique_left]
          grind [List.head!_eq_head?, List.head?_drop, δ.δ']
      · rw [Matrix.mul_apply]
        simp [Q, RPol.wnka_sem_case', ι, 𝒪, List.getLast?_cons, xδ, δ, ← Matrix.mul_assoc, ι_wProd_δ']
        conv => right; arg 2; ext; rw [one_mul_coe_unique_left, ← Matrix.down_mul]
        simp [-Matrix.down_mul, ← Matrix.mul_assoc, ← Matrix.down_sum]
        simp [-Matrix.down_sum, ← Matrix.sum_mul]
        congr
        rw [mul_sox]
        nth_rw 1 [sox]
        ext _ γ
        simp [S.ι, Matrix.sum_apply, box, 𝒪_heart, Matrix.mul_apply]
        rcases γ with _ | γ
        · simp; congr
        · grind [Sum.elim_inr, mul_zero, Finset.sum_const_zero]

theorem fp₁_Q_is_fp' (p₁ : RPol 𝒮) (h : Q p₁ = M' p₁) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) (ih : ∀ (y : List Pk[F,N]), y.length < xₙ.length → y ≠ [] → M' wnk_rpol {~p₁*} y = Q wnk_rpol {~p₁*} y) :
    Q wnk_rpol {~p₁*} xₙ = M' p₁ [] * Q wnk_rpol {~p₁*} xₙ + N' p₁ xₙ := by
  nth_rw 1 [fp₁_Q_is_fp _ _ hxₙ]
  rw [add_comm, h]
  congr
  have N'_eq_N'Q : N' p₁ xₙ = N'Q p₁ xₙ := by
    simp only [N', N'Q]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [N'_ij, N'Q_ij, h]
    grind [Q_empty_eq_M'_empty, List.drop_eq_nil_iff]
  rw [N'_eq_N'Q]

omit [DecidableEq 𝒮] in
theorem LawfulStar.star_eq_one_add_mul [LawfulStar 𝒮] {s : 𝒮} : s^* = 1 + s * s^* := by
  simp [star_eq_sum]
  nth_rw 1 [ωSum_nat_eq_succ]
  simp [pow_succ', ωSum_mul_left]
omit [DecidableEq 𝒮] in
theorem LawfulStar.star_eq_one_add_mul' [LawfulStar 𝒮] {s : 𝒮} : s^* = 1 + s^* * s := by
  simp [star_eq_sum]
  nth_rw 1 [ωSum_nat_eq_succ]
  simp [pow_succ, ωSum_mul_right]

omit [DecidableEq 𝒮] in
theorem fp₁_M'_is_fp'' (p₁ : RPol 𝒮) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) :
    M' wnk_rpol {~p₁*} xₙ = (M' p₁ [])^* * N' p₁ xₙ := by
  have ⟨h₁, h₂⟩ := fp₁_M' p₁ xₙ hxₙ
  simp [fp₁, lowerBounds] at h₁ h₂
  apply le_antisymm
  · apply h₂
    nth_rw 1 [LawfulStar.star_eq_one_add_mul]
    simp [add_mul, mul_assoc]
  · simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
    rw [ωSum_nat_eq_ωSup]
    simp
    intro i
    simp only [DFunLike.coe]
    induction i with
    | zero => simp
    | succ i ih' =>
      simp [Finset.sum_range_succ']
      rw [h₁, add_comm]
      gcongr
      simp [pow_succ', Matrix.mul_assoc, ← Matrix.mul_sum]
      gcongr

theorem le_ωSup_iff {s : Chain 𝒮} {a : 𝒮} : a ≤ ωSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  sorry
  -- simp [ωSup, le_sSup_iff, upperBounds]


theorem fp₁_Q_is_fp'' (p₁ : RPol 𝒮) (h : Q p₁ = M' p₁) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) (ih : ∀ (y : List Pk[F,N]), y.length < xₙ.length → y ≠ [] → M' wnk_rpol {~p₁*} y = Q wnk_rpol {~p₁*} y) :
    Q wnk_rpol {~p₁*} xₙ = (M' p₁ [])^* * N' p₁ xₙ := by
  -- rw [fp₁_Q_is_fp' p₁ h _ hxₙ ih]

  have : ∀ n, (eq₁ p₁ xₙ)^[n] (Q wnk_rpol {~p₁*} xₙ) = (Q wnk_rpol {~p₁*} xₙ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih']
      simp [eq₁]
      nth_rw 2 [fp₁_Q_is_fp' p₁ h xₙ hxₙ ih]
      simp [add_comm]

  -- have : ∀ n, (eq₁ p₁ xₙ)^[n] ⊥ ≤ (Q wnk_rpol {~p₁*} xₙ) := by
  --   intro n
  --   induction n with
  --   | zero => simp
  --   | succ n ih =>

  --     apply le_trans _ ih
  --     simp

  -- have : ωSup ⟨fun n ↦ (eq₁ p₁ xₙ)^[n] (Q wnk_rpol {~p₁*} xₙ), sorry⟩ = (Q wnk_rpol {~p₁*} xₙ) := by
  --   simp [this]

  -- rw [← this]
  -- simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
  -- rw [ωSum_nat_eq_ωSup]
  -- apply le_antisymm
  -- · simp [DFunLike.coe]
  --   intro n
  --   induction n with
  --   | zero =>
  --     simp [Finset.sum_range_succ]
  --     sorry
  --   | succ n ih =>
  --     simp only [Function.iterate_succ', Function.comp_apply]
  --     rw []



  apply le_antisymm
  ·
    -- simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
    -- rw [fp₁_Q_is_fp' p₁ h xₙ hxₙ ih]
    -- rw [ωSum_nat_eq_succ]
    -- simp
    -- rw [add_comm]
    -- gcongr
    -- simp [pow_succ', ωSum_mul_left, mul_assoc]
    -- gcongr
    -- simp [ωSum_nat_eq_ωSup]
    -- apply le_ωSup_iff.mpr
    -- intro b hb
    -- simp_all [DFunLike.coe]

    rw [← box_eq_M'_of_empty]
    have ih₁' : Q p₁ = M' p₁ := by ext x α αb; simp [Q]; rw [← h]; rfl
    have N'_eq_N'Q : N' p₁ xₙ = N'Q p₁ xₙ := by
      simp only [N', N'Q]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [N'_ij, N'Q_ij, ih₁']
      grind [Q_empty_eq_M'_empty, List.drop_eq_nil_iff]
    simp [N'_eq_N'Q]
    clear ih₁' N'_eq_N'Q
    induction xₙ using List.reverseRecOn with
    | nil => contradiction
    | append_singleton xₙ α₀ ih' =>
      induction xₙ generalizing α₀ with
      | nil =>
        intro α β
        simp [Q, RPol.wnka_sem_case', ι, δ, 𝒪, xδ, N'Q, N'Q_ij]
        rw [ι_wProd_δ', ι_wProd_𝒪]
        simp [𝒪_heart]
        rw [one_mul_coe_unique_left]
        simp [← Matrix.mul_assoc]
        rw [Matrix.mul_apply]
        simp [Matrix.mul_sum]
        gcongr with γ
        rw [Matrix.mul_apply]
        simp [Q, RPol.wnka_sem_case', xδ, sox, fox, Matrix.sum_mul]
      | cons α₁ xₘ ih'' =>
        intro α β
        simp [Q, RPol.wnka_sem_case', ι, δ, 𝒪, xδ, N'Q, N'Q_ij, ← Matrix.mul_assoc, xδ_idk']
        rw [ι_wProd_δ', ι_wProd_δ', ι_wProd_𝒪]
        simp
        rw [one_mul_coe_unique_left]
        simp [List.getLast?_cons]
        rw [← List.cons_append, xδ_as_sum]
        simp [mul_add, Matrix.mul_add, Matrix.add_mul]
        nth_rw 2 [Finset.sum_range_succ]
        simp [left_distrib]
        nth_rw 4 [add_comm]
        gcongr
        · have : List.take (xₘ.length + 1) (xₘ ++ [α₀]) = (xₘ ++ [α₀]) := by simp
          simp [this]
          simp [← Matrix.mul_assoc]
          sorry
        · simp [Matrix.mul_sum, Matrix.sum_apply, Matrix.sum_mul, Finset.sum_mul]
          sorry
      -- simp_all only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true,
      --   List.length_append, List.length_cons, List.length_nil, zero_add]
      -- simp [N'Q, N'Q_ij] at ih' ⊢
      -- rw [Finset.sum_range_succ']
      -- simp [mul_add]
      -- -- have := LawfulStar.
      -- -- rw [fp₁_Q_is_fp' p₁ h _ _]
      -- -- · simp
      -- --   sorry
      -- -- · simp; exact ih
      -- -- · simp
      -- sorry

  · simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
    rw [ωSum_nat_eq_ωSup]
    simp
    intro i
    simp only [DFunLike.coe]
    induction i with
    | zero => simp
    | succ i ih' =>
      simp [Finset.sum_range_succ']
      rw [fp₁_Q_is_fp' p₁ h _ hxₙ ih]
      gcongr
      simp [pow_succ', Matrix.mul_assoc, ← Matrix.mul_sum]
      gcongr
  -- -- have ⟨h₁, h₂⟩ := fp₁_M' p₁ xₙ hxₙ
  -- -- simp [fp₁, lowerBounds] at h₁ h₂
  -- -- symm at h₁
  -- -- rw [add_comm]
  -- -- rw [LawfulStar.star_eq_one_add_mul]
  -- -- simp [add_mul]
  -- -- rw [add_comm]

  -- induction xₙ with
  -- | nil => contradiction
  -- | cons α₀ xₙ ih' =>
  --   rw [fp₁_Q_is_fp' p₁ h _ (by simp) ih]
  --   rw [← h]
  --   rw [LawfulStar.star_eq_one_add_mul]
  --   simp [add_mul]
  --   rw [add_comm, mul_assoc]
  --   congr! 2

  -- -- NOTE: This is one iteration!
  -- rw [fp₁_Q_is_fp' p₁ h xₙ hxₙ ih]
  -- rw [← h]
  -- rw [LawfulStar.star_eq_one_add_mul]
  -- simp [add_mul]
  -- rw [add_comm, mul_assoc]
  -- congr! 2

  -- rw [LawfulStar.]
  -- rw [@M_empty_star_eq_heart]
  -- rw [@box_star_iter]
  -- simp [Matrix.add_mul]
  -- congr! 1
  -- rw [← @Q_star_eq_box]
  -- rw [h]

  -- nth_rw 1 [fp₁_Q_is_fp _ _ hxₙ]
  -- rw [add_comm, h]
  -- congr
  -- have N'_eq_N'Q : N' p₁ xₙ = N'Q p₁ xₙ := by
  --   simp only [N', N'Q]
  --   refine Finset.sum_congr rfl fun i hi ↦ ?_
  --   simp only [N'_ij, N'Q_ij, h]
  --   grind [Q_empty_eq_M'_empty, List.drop_eq_nil_iff]
  -- rw [N'_eq_N'Q]

set_option maxHeartbeats 500000 in
theorem fp₁_Q (p₁ : RPol[F,N,𝒮]) (ih₁ : p₁.wnka.sem = G p₁) (xₙ) (hxₙ : xₙ ≠ []) : IsLeast {f | fp₁ p₁ xₙ f} (Q p₁.Iter xₙ) := by
  induction xₙ using Nat.strongRecMeasure List.length; next xₙ ihₙ =>
  replace ihₙ : ∀ (y : List Pk[F,N]), y.length < xₙ.length → y ≠ [] → M' wnk_rpol {~p₁*} y = Q wnk_rpol {~p₁*} y := by
    intro y hy hy'
    symm
    apply IsLeast.unique (ihₙ y hy hy') (fp₁_M' _ _ hy')
  have ih₁' : Q p₁ = M' p₁ := by ext x α αb; simp [Q]; rw [ih₁]; rfl
  have N'_eq_N'Q : N' p₁ xₙ = N'Q p₁ xₙ := by
    simp only [N', N'Q]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [N'_ij, N'Q_ij, ih₁']
    grind [Q_empty_eq_M'_empty, List.drop_eq_nil_iff]
  constructor
  · simp only [fp₁, Set.mem_setOf_eq]
    rw [← ih₁', N'_eq_N'Q, ← fp₁_Q_is_fp p₁ xₙ hxₙ]
  · simp only [lowerBounds, fp₁, Set.mem_setOf_eq]
    intro A hA
    have ⟨h₁, h₂⟩ := fp₁_M' p₁ xₙ hxₙ
    simp [fp₁, lowerBounds] at h₁ h₂
    have := h₂ hA
    apply le_trans _ this; clear! A
    clear h₁ h₂
    induction xₙ using List.reverseRecOn with
    | nil => contradiction
    | append_singleton xₙ  α' ih =>
      rw [fp₁_Q_is_fp _ _ hxₙ]
      induction xₙ with
      | nil =>
        sorry
      | cons =>
        sorry

    -- replace hA : N'Q p₁ xₙ + (ι p₁ ⊠ 𝒪 p₁) * A = A := by
    --   symm; unfold M' at hA; simp [← ih₁] at hA; simp [N'_eq_N'Q] at hA; exact hA



    -- induction xₙ using List.reverseRecOn with
    -- | nil => contradiction
    -- | append_singleton xₙ  α' ih =>
    --   induction xₙ with
    --   | nil =>
    --     clear ih
    --     symm at hA
    --     simp [box_eq_M'_of_empty, ← ih₁'] at hA
    --     intro α β
    --     simp [Q, RPol.wnka_sem_case', ι, δ, 𝒪, xδ]
    --     rw [ι_wProd_δ', ι_wProd_𝒪]
    --     simp
    --     rw [one_mul_coe_unique_left]
    --     rw [hA]
    --     simp
    --     simp [N'Q, N'Q_ij]
    --     simp [Matrix.mul_apply]
    --     simp [𝒪_heart, Matrix.mul_sum, ← Finset.sum_add_distrib]
    --     simp [Q, RPol.wnka_sem_case', xδ]
    --     simp [sox, fox]
    --     gcongr with γ
    --     nth_rw 2 [LawfulStar.star_eq_one_add_mul]
    --     simp [Matrix.mul_add, left_distrib, Finset.sum_mul, Matrix.sum_mul]
    --     rw [add_comm]
    --     gcongr
    --     ·
    --       sorry
    --     · simp [Matrix.one_apply]
    --       split_ifs
    --       · subst_eqs
    --         sorry
    --       · simp





    --     -- rw [fp₁_Q_is_fp _ _ hxₙ]
    --     -- simp
    --     -- rw [hA]
    --     -- simp
    --     -- gcongr
    --     -- rw [ih₁']
    --     -- simp [Matrix.mul_apply]
    --     -- gcongr with γ
    --     -- rw [fp₁_Q_is_fp _ _ (by simp)]
    --     -- simp
    --     -- rw [hA]
    --     -- simp
    --     -- gcongr
    --     -- rw [ih₁']
    --     -- simp [Matrix.mul_apply]
    --     -- gcongr with γ'



    --     simp [Q, RPol.wnka_sem_case', ι, δ, 𝒪, xδ]
    --     rw [ι_wProd_δ', ι_wProd_𝒪]
    --     simp
    --     rw [one_mul_coe_unique_left]
    --     rw [hA]
    --     simp [N'Q, N'Q_ij, Matrix.add_apply, 𝒪_heart]
    --     simp at *
    --     unfold Q
    --     simp [RPol.wnka_sem_case', ι, δ, 𝒪, xδ]
    --     conv =>
    --       right
    --       arg 1
    --       arg 2
    --       ext _ _
    --       rw [ι_wProd_𝒪]
    --     simp

    --     sorry

    --   | cons α₀ xₙ ih =>
    --     sorry

          -- simp [δ.δ']
          -- -- conv =>
          -- --   right
          -- --   arg 2; ext
          -- --   rw [ihₙ' _ (by simp; omega) (by simp)]
          -- sorry
  --       ·
  --         rw [Matrix.mul_apply]
  --         simp [Q, RPol.wnka_sem_case', ι, 𝒪]
  --         simp [List.getLast?_cons]
  --         simp [xδ]
  --         simp [δ]
  --         simp [← Matrix.mul_assoc]
  --         simp [ι_wProd_δ']
  --         conv => right; arg 2; ext; rw [one_mul_coe_unique_left]
  --         rw [mul_sox]
  --         conv => right; arg 2; ext; rw [← Matrix.down_mul]
  --         simp [-Matrix.down_mul, ← Matrix.mul_assoc]
  --         rw [← Matrix.down_sum]
  --         simp [-Matrix.down_sum, ← Matrix.sum_mul]
  --         congr
  --         nth_rw 1 [sox]
  --         ext _ γ
  --         rcases γ with _ | γ
  --         · simp [S.ι, Matrix.sum_apply, box, 𝒪_heart, Matrix.mul_apply]
  --           congr
  --         · simp [S.ι, Matrix.sum_apply, box, 𝒪_heart, Matrix.mul_apply]

  --       -- simp at ih'
  --       -- simp [N', N'_ij, ← ih₁', ← Q_empty_eq_M'_empty]


  --     conv => left; unfold Q
  --     ext α β
  --     simp only [Matrix.add_apply]
  --     simp only [List.length_append, List.length_cons, List.length_nil, zero_add, ne_eq] at ihₙ ihₙ'
  --     simp [RPol.wnka_sem_case]
  --     simp [ι]
  --     simp [𝒪]
  --     rcases xₙ with _ | ⟨α₁, xₙ⟩
  --     · simp [xδ, δ]
  --       rw [ι_wProd_δ']
  --       simp
  --       rw [one_mul_coe_unique_left]
  --       rw [ι_wProd_𝒪]
  --       simp
  --       simp [N', N'_ij]
  --       simp [← Q_empty_eq_M'_empty, ← ih₁']
  --       -- simp [𝒪_heart]
  --       simp [sox]
  --       simp [fox]
  --       simp [Matrix.mul_apply]
  --       simp [← Finset.sum_add_distrib]
  --       simp [Q, RPol.wnka_sem_case']
  --       simp [𝒪, ι, δ, xδ]
  --       conv =>
  --         right
  --         arg 2
  --         ext x
  --         rw [ι_wProd_δ']
  --         rw [ι_wProd_𝒪]
  --       simp
  --       conv =>
  --         right
  --         arg 2
  --         ext
  --         rw [one_mul_coe_unique_left]
  --       -- simp [𝒪_heart]
  --       simp
  --       sorry
  --     · sorry


  --   conv => left; unfold Q
  --   ext α β
  --   simp only [Matrix.add_apply]
  --   induction xₙ using List.reverseRecOn with
  --   | nil => contradiction
  --   | append_singleton xₙ α' ih =>
  --     clear ih
  --     simp only [List.length_append, List.length_cons, List.length_nil, zero_add, ne_eq] at ihₙ ihₙ'
  --     have : N' p₁ (xₙ ++ [α']) α β = N'Q p₁ (xₙ ++ [α']) α β:= by
  --       simp [N', N'Q, Matrix.sum_apply]
  --       refine Finset.sum_congr rfl ?_
  --       intro i hi
  --       simp at hi
  --       simp [N'_ij, N'Q_ij, ih₁']
  --       if i = xₙ.length then
  --         subst_eqs
  --         simp [Q_empty_eq_M'_empty]
  --       else
  --         rw [ihₙ']
  --         · simp; omega
  --         · simp; omega
  --     simp [this]

  --     simp [RPol.wnka_sem_case]
  --     rcases xₙ with _ | ⟨α₁, xₙ⟩
  --     · simp_all only [List.nil_append, ne_eq, List.cons_ne_self, not_false_eq_true]
  --       simp only [ι, S.I, xδ, δ, mul_one, 𝒪, Matrix.mul_assoc]
  --       rw [δ_wProd_𝒪, ι_wProd_𝒪]
  --       simp
  --       simp [← ih₁']
  --       simp [N'Q, N'Q_ij]
  --       sorry
  --     simp [xδ_idk, ι, xδ, 𝒪]
  --     rw [ι_wProd_δ', ι_wProd_𝒪]
  --     simp
  --     have : ∀ (x : 𝒲[S.I ↑{♡}, S p₁, 𝒮]), Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (fun x ↦ 1 : 𝟙 → S.I {♡} → 𝒮) x = x.coe_unique_left := by
  --       simp
  --       intro x
  --       ext
  --       simp [Matrix.mul_apply]
  --     simp [this]
  --     simp [𝒪_heart]
  --     nth_rw 1 [box_star_iter]
  --     simp [add_sox]
  --     simp [Matrix.add_mul, add_mul]
  --     congr
  --     ·
  --       -- let y := 𝒪_heart p₁
  --       -- let x := ι p₁ ⊡ δ p₁
  --       -- let z := y x
  --       -- let q := xδ sorry xₙ

  --       calc _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ γ,
  --               ((ι p₁ ⊡ δ p₁) α α₁ * xδ (δ p₁) (α₁ :: xₙ.take i) * 𝒪 p₁ (α₁ :: xₙ)[i]! γ *
  --                 (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) γ (xₙ ++ [α'])[i+1]! * xδ (δ.δ' p₁) (xₙ.drop (i + 1) ++ [α']) * (𝒪 p₁ α' β <• 𝒪_heart p₁ α' β)).down := by
  --             simp
  --             sorry
  --           _ = _ := by
  --             simp [N'Q, N'Q_ij, Matrix.sum_apply]
  --             simp [Matrix.mul_apply]
  --             simp [Q]
  --             simp [RPol.wnka_sem_case']
  --             clear this ihₙ' ihₙ hxₙ
  --             clear this
  --             induction xₙ with
  --             | nil =>
  --               simp [Finset.sum_range_succ, xδ]
  --               simp [fox]
  --               simp [sox]
  --               simp [fox]
  --               simp [ι, δ, 𝒪]
  --               conv => right; left; arg 2; ext; rw [ι_wProd_δ', ι_wProd_𝒪]
  --               conv => right; right; arg 2; ext; rw [ι_wProd_𝒪]
  --               simp
  --               simp [← Finset.sum_add_distrib]
  --               congr with γ
  --               simp [fox, sox, Matrix.mul_apply]
  --               sorry
  --             | cons α₂ xₙ ih =>
  --               simp
  --               nth_rw 2 [Finset.sum_range_succ']
  --               simp
  --               sorry
  --             -- apply Finset.sum_congr (by simp)
  --             -- intro i hi
  --             -- simp only [Finset.mem_range] at hi
  --             -- congr with γ
  --             -- simp [xδ]
  --             -- simp [List.getLast?_cons]
  --             -- simp [List.getLast?_take]
  --             -- simp [𝒪]
  --             -- split_ifs
  --             -- · subst_eqs
  --             --   simp
  --             --   sorry
  --             -- · simp
  --             --   sorry



  --       have :
  --             xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α']))
  --           = if xₙ = [] then xδ (δ.δ' p₁) [α₁, α'] else ∑ i ∈ Finset.range (xₙ.length + 1), ∑ γ,
  --               let l := xₙ.take i
  --               let r := xₙ.drop i
  --               xδ (δ.δ' p₁) (α₁ :: l ++ [γ]) * xδ (δ.δ' p₁) (γ :: r ++ [α']) := by
  --         simp
  --         clear this ihₙ' ihₙ hxₙ
  --         clear this
  --         induction xₙ generalizing α₁ with
  --         | nil =>
  --           simp [xδ]
  --         | cons α₀ xₙ ih =>
  --           simp [xδ]; rw [ih]
  --           simp
  --           split_ifs
  --           · subst_eqs
  --             simp [Finset.sum_range_succ]
  --             simp [xδ]
  --             ext i j
  --             simp [Matrix.mul_apply]

  --           sorry

  --       simp [N'Q, N'Q_ij, Matrix.sum_apply]
  --       simp [Matrix.mul_apply]
  --       simp [Q]
  --       simp [RPol.wnka_sem_case']


  --       simp [List.getLast?_cons, List.getLast?_take]

  --       have : ∀ x, ((if x = 0 then none else some ((xₙ ++ [α'])[x - 1]?.getD α')).getD α₁) =
  --           (if x = 0 then α₁ else ((xₙ ++ [α'])[x - 1]?.getD α'))  := by
  --         grind
  --       simp [this]; clear this

  --       rw [Finset.sum_range_succ']
  --       simp [xδ]


  --       rw [Finset.sum_range_succ]
  --       simp
  --       have : List.take (xₙ.length + 1) (xₙ ++ [α']) = xₙ ++ [α'] := by simp
  --       simp [this]
  --       rw [add_comm]
  --       conv => right; left; arg 2; ext; right; simp [xδ, ι, 𝒪]; rw [ι_wProd_𝒪]
  --       simp

  --       have : ∀ x,
  --         (@HMul.hMul 𝒲[𝟙, S.I ↑{♡}, 𝒮] 𝒲[S.I ↑{♡}, 𝟙, 𝒮] 𝒲[𝟙, 𝟙, 𝒮] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (fun x ↦ 1) (𝒪_heart p₁ x β) : 𝒲[𝟙, 𝟙, 𝒮]) = (𝒪_heart p₁ x β) := by
  --           intro; ext
  --           simp [Matrix.mul_apply]
  --       simp [this]
  --       simp [𝒪_heart]

  --       have :
  --           ∑ x, (ι p₁ * xδ (δ p₁) (α :: α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' x).down * (ι p₁ ⊠ 𝒪 p₁)^* x β
  --         = ((ι p₁ * xδ (δ p₁) (α :: α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α') ⊞ (ι p₁ ⊠ 𝒪 p₁)^*) β := sorry

  --       calc
  --         ((ι p₁ ⊡ δ p₁) α α₁ * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β).down *
  --               (ι p₁ ⊠ 𝒪 p₁)^* α' β =
  --             ∑ x ∈ Finset.range (xₙ.length + 1 + 1),
  --               3 * ∑ x_1,
  --                 (ι p₁ * xδ (δ p₁) (α :: α₁ :: List.take x (xₙ ++ [α'])) *
  --                       𝒪 p₁ ((α₁ :: List.take x (xₙ ++ [α'])).getLast?.getD α) x_1).down *
  --                   (ι wnk_rpol {~p₁*} * xδ (δ wnk_rpol {~p₁*}) (x_1 :: List.drop x (xₙ ++ [α'])) *
  --                       𝒪 wnk_rpol {~p₁*} ((List.drop x (xₙ ++ [α'])).getLast?.getD x_1) β).down := by
  --           sorry
  --         _ = _ := by
  --           apply Finset.sum_congr (by simp)
  --           intro i hi
  --           simp at hi
  --           simp [xδ_idk']
  --           simp [ι, xδ, 𝒪, 𝒪_heart]
  --           conv => right; arg 2; ext; rw [ι_wProd_δ', ι_wProd_𝒪]
  --           simp [Finset.mul_sum]
  --           congr with γ
  --           split_ifs
  --           · have : i = xₙ.length + 1 := by omega
  --             subst_eqs
  --             simp
  --             simp_all [xδ]
  --             have : List.take (xₙ.length + 1) (xₙ ++ [α']) = (xₙ ++ [α']) := by simp
  --             simp [this]
  --             simp [List.getLast?]
  --             sorry
  --           · simp
  --             have hi0 : (i - xₙ.length) = 0 := by omega
  --             simp [hi0, List.take_append]
  --             have : ¬xₙ.length + 1 ≤ i := by omega
  --             simp [List.getLast?_drop, this]
  --             simp [List.head!]
  --             split
  --             · simp_all; omega
  --             · simp [List.drop_append, hi0]
  --               simp_all
  --               sorry
  --       simp only [← List.cons_append]
  --       simp [ι, xδ, 𝒪, 𝒪_heart]

  --       simp [xδ_idk']
  --       conv =>
  --         right
  --         arg 2; ext; arg 2; ext
  --         rw [ι_wProd_δ', ι_wProd_𝒪]
  --       simp
  --       calc
  --         ((ι p₁ ⊡ δ p₁) α α₁ * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β).down *
  --               (ι p₁ ⊠ 𝒪 p₁)^* α' β =
  --             ∑ x ∈ Finset.range (xₙ.length + 1 + 1),
  --               ∑ x_1,
  --                 (ι p₁ * (δ p₁ α α₁ * xδ (δ p₁) (α₁ :: List.take x (xₙ ++ [α']))) *
  --                       𝒪 p₁ ((α₁ :: List.take x (xₙ ++ [α'])).getLast?.getD α) x_1).down *
  --                   ((((Matrix.of fun x ↦ 1) *
  --                             if xₙ.length + 1 ≤ x then 0
  --                             else
  --                               ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) x_1
  --                                     (List.drop x (xₙ ++ [α'])).head!).coe_unique_left *
  --                                 xδ (δ.δ' p₁) (List.drop x (xₙ ++ [α']))) *
  --                           𝒪 p₁ ((List.drop x (xₙ ++ [α'])).getLast?.getD x_1) β).down *
  --                       (ι p₁ ⊠ 𝒪 p₁)^* ((List.drop x (xₙ ++ [α'])).getLast?.getD x_1) β +
  --                     (((Matrix.of fun x ↦ 1) * if xₙ.length + 1 ≤ x then 1 else 0) *
  --                         ((ι p₁ ⊠ 𝒪 p₁)^* ((List.drop x (xₙ ++ [α'])).getLast?.getD x_1)
  --                             β)).down) := by sorry
  --         _ = _ := by
  --           sorry

  --       calc
  --         ((ι p₁ ⊡ δ p₁) α α₁ * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β).down * (ι p₁ ⊠ 𝒪 p₁)^* α' β
  --         = ∑ x ∈ Finset.range (xₙ.length + 1 + 1), ∑ j, Q p₁ (α₁ :: List.take x (xₙ ++ [α'])) α j * Q wnk_rpol {~p₁*} (List.drop x (xₙ ++ [α'])) j β := by
  --           simp [Q]
  --           sorry
  --         _ = ∑ x ∈ Finset.range (xₙ.length + 1 + 1), ∑ j, Q p₁ (α₁ :: List.take x (xₙ ++ [α'])) α j * Q wnk_rpol {~p₁*} (List.drop x (xₙ ++ [α'])) j β := by
  --           sorry

  --       simp [Q]
  --       rw [Finset.sum_eq_single (xₙ.length + 1)]
  --       ·
  --         have h₁ : List.take (xₙ.length + 1) (xₙ ++ [α']) = (xₙ ++ [α']) := by simp
  --         have h₂ : List.take xₙ.length (xₙ ++ [α']) = (xₙ) := by simp
  --         simp [h₁, h₂]
  --         simp only [← List.cons_append]
  --         simp only [RPol.wnka_sem_case]



  --       sorry

  --       have :
  --             xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α']))
  --           = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ γ,
  --               xδ (δ p₁) ((α₁ :: xₙ).take (i + 1)) * 𝒪 p₁ (α₁ :: xₙ)[i]! γ * (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) γ (α₁ :: xₙ ++ [α'])[i + 1]! * xδ (δ.δ' p₁) (xₙ.drop (i + 1) ++ [α']) := by
  --               -- xδ (δ p₁) ((α₁ :: xₙ.take i) ++ [γ]) * 𝒪 p₁ sorry γ * (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) γ sorry * xδ (δ.δ' p₁) (γ :: (xₙ.drop i ++ [α'])) := by
  --               -- xδ (δ p₁) ((α₁ :: xₙ.take i) ++ [γ]) * xδ (𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) (γ :: (xₙ.drop i ++ [α'])) := by
  --         clear this ihₙ' ihₙ hxₙ
  --         clear this
  --         induction xₙ generalizing α₁ α' with
  --         | nil =>
  --           simp
  --           simp [xδ, δ.δ']
  --           simp [crox, sox, fox, Matrix.sum_mul, Matrix.mul_sum]
  --         | cons α₂ xₙ ih =>
  --           simp
  --           simp [xδ]
  --           rw [ih]
  --           simp [Finset.mul_sum]

  --           ext α β
  --           simp [Matrix.mul_apply]
  --           simp [δ.δ']
  --           simp [Matrix.sum_apply]
  --           rw [Finset.sum_comm]
  --           congr! 1
  --           simp [add_mul, Finset.sum_add_distrib]
  --           simp [crox, sox, fox, Matrix.sum_mul, Matrix.mul_sum]
  --           rw [ih]
  --           simp [Matrix.add_mul]
  --           sorry



  --       rw [this]; clear this
  --       simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  --       simp [N'Q, N'Q_ij, Matrix.sum_apply]
  --       simp [Matrix.mul_apply]
  --       apply Finset.sum_congr (by simp)
  --       intro i hi
  --       simp at hi
  --       simp [Q]
  --       if i = xₙ.length + 1 then
  --         subst_eqs
  --         simp [hi]
  --         have : List.take (xₙ.length + 1) (xₙ ++ [α']) = (xₙ ++ [α']) := by simp
  --         simp [this]
  --         rw [← List.cons_append]
  --         simp [-List.cons_append, -List.cons_append_fun, RPol.wnka_sem_case]
  --         simp [𝒪, ι]
  --         conv => right; right; ext; rw [ι_wProd_𝒪]
  --         simp [𝒪_heart]
  --         simp [Matrix.mul_apply]
  --         simp [xδ, fox, ← Matrix.mul_assoc]

  --       else
  --         sorry


  --       simp only [List.cons_append, ι, S.I, 𝒪]
  --       rw [xδ_idk]
  --       rw [ι_wProd_δ', ι_wProd_𝒪]
  --       simp [𝒪_heart, ← Matrix.mul_assoc]
  --       sorry
  --     · simp [mul_sox]
  --       nth_rw 1 [sox]
  --       simp [Finset.sum_mul, Matrix.sum_mul]
  --       rw [Matrix.mul_apply]
  --       congr with γ
  --       simp [mul_assoc]
  --       congr! 1
  --       simp [Q]
  --       rw [← List.cons_append, RPol.wnka_sem_case]
  --       simp only [List.cons_append, ι, S.I, 𝒪]
  --       rw [xδ_idk]
  --       rw [ι_wProd_δ', ι_wProd_𝒪]
  --       simp [𝒪_heart, ← Matrix.mul_assoc]
  --       congr! 4
  --       ext
  --       simp [Matrix.mul_apply]


  --     -- simp [← Matrix.mul_smul, sox]
  --     -- calc
  --     --     ((∑ m, 𝒪_heart p₁ α m •> (ι p₁ ⊡ δ p₁) m α₁) * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β <• 𝒪_heart p₁ α' β).down
  --     --   = ∑ m, ((𝒪_heart p₁ α m •> (ι p₁ ⊡ δ p₁) m α₁) * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β <• 𝒪_heart p₁ α' β).down := by
  --     --       simp [Matrix.sum_mul, Matrix.sum_smul']
  --     -- _ = N'Q p₁ (α₁ :: (xₙ ++ [α'])) α β + (Q p₁ [] * Q wnk_rpol {~p₁*} (α₁ :: (xₙ ++ [α']))) α β := by
  --     --     simp [𝒪_heart]
  --     --     nth_rw 2 [box_star_iter]
  --     --     simp
  --     --     simp [add_smul, Finset.sum_add_distrib]
  --     --     rw [add_comm]
  --     --     congr
  --     --     · sorry
  --     --     · ext γ
  --     --       simp
  --     --       sorry

  --     -- simp [ι]

  --     -- simp
  --     -- calc
  --     --   wnk_rpol {~p₁*}.wnka.sem (α, α₁ :: (xₙ ++ [α']), β) =
  --     --       (ι wnk_rpol {~p₁*} * xδ (δ p₁.Iter) (α :: α₁ :: (xₙ ++ [α'])) * 𝒪 wnk_rpol {~p₁*} α' β).down := by
  --     --     simp [RPol.wnka_sem_case]
  --     --   _ = ((Matrix.of fun x b ↦ (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ PUnit.unit b) * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β).down * 𝒪_heart p₁ α' β := by
  --     --   -- _ = ((𝒪_heart p₁ α α₁ • ι p₁ * δ p₁ α α₁) * ((xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α']))) * 𝒪 p₁ α' β <• 𝒪_heart p₁ α' β)).down := by
  --     --     rw [xδ_idk]
  --     --     simp [ι, 𝒪]
  --     --     rw [ι_wProd_δ]
  --     --     simp
  --     --     conv => left; arg 1; arg 1; arg 1; unfold S.ι
  --     --     simp
  --     --     simp [Matrix.add_mul]
  --     --     rw [ι_wProd_𝒪]
  --     --     simp
  --     --     conv => left; arg 1; arg 1; simp [Matrix.instHMulOfFintypeOfMulOfAddCommMonoid]
  --     --     simp [Matrix.down]
  --     --     rw [Matrix.mul_assoc]
  --     --     rw [Matrix.mul_apply]
  --     --     simp
  --     --     congr
  --     --     -- simp [← Matrix.mul_assoc]
  --     --     -- generalize 𝒪_heart p₁ α α₁ = X
  --     --     -- generalize (ι p₁ * δ p₁ α α₁ * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α']))) = Y
  --     --     -- generalize 𝒪 p₁ α' β = Z
  --     --     -- simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  --     --   _ = N'Q p₁ (α₁ :: (xₙ ++ [α'])) α β + (Q p₁ [] * Q wnk_rpol {~p₁*} (α₁ :: (xₙ ++ [α']))) α β := by
  --     --     simp [𝒪_heart]
  --     --     nth_rw 1 [box_star_iter]
  --     --     simp [add_sox]

  --     --     have Matrix.of_add_of' : ∀ (f g : (S.I ↑{♡}) → S p₁ → 𝒮),
  --     --         Matrix.of (fun a b ↦ f a b + g a b) = Matrix.of f + Matrix.of g := by
  --     --       intro f g
  --     --       symm
  --     --       apply Matrix.of_add_of
  --     --     simp at Matrix.of_add_of'
  --     --     simp [Matrix.of_add_of']; clear Matrix.of_add_of'
  --     --     simp [← Matrix.of_add_of]
  --     --     simp only [Matrix.add_mul]
  --     --     simp [Matrix.down]
  --     --     simp only [add_mul]
  --     --     symm at ih₁'
  --     --     congr
  --     --     · simp [N'Q, N'Q_ij]
  --     --       simp_all only [List.cons_append, ne_eq, reduceCtorEq, not_false_eq_true]
  --     --       simp_all only [List.length_cons]

  --     --       simp [Matrix.sum_apply]
  --     --       rw [add_comm, Finset.sum_range_add]
  --     --       simp
  --     --     ·
  --     --       sorry






  --           -- nth_rw 2 [Matrix.mul_apply]
  --           -- simp [Matrix.of, Equiv.refl]
  --           -- simp only [DFunLike.coe, EquivLike.coe]
  --           -- simp only [id_eq]
  --           -- have : ((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁) = ((ι p₁ ⊠ 𝒪 p₁) ⊟ ((ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁)) := by
  --           --   ext α β u s
  --           --   simp [sox, fox, Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  --           --   conv => left; arg 2; ext; rw [Finset.sum_comm]
  --           --   conv => left; rw [Finset.sum_comm]
  --           -- simp [this]
  --           -- nth_rw 1 [sox]
  --           -- have :
  --           --       (fun (a : S.I ↑{♡}) ↦ (∑ m, (ι p₁ ⊠ 𝒪 p₁) α m •> ((ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁) m α₁) PUnit.unit)
  --           --     = ∑ m, ((fun (a : S.I ↑{♡}) (b) ↦ ((ι p₁ ⊠ 𝒪 p₁) α m •> ((ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁) m α₁) PUnit.unit b) : 𝒲[S.I ↑{♡}, S p₁, 𝒮]) := by
  --           --   sorry
  --           -- simp only [S.I] at this; simp only [this, Matrix.smul_apply, smul_eq_mul]
  --           -- have :
  --           --   ((∑ x, Matrix.of fun (a : S.I ↑{♡}) b ↦ (ι p₁ ⊠ 𝒪 p₁) α x * ((ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁) x α₁ PUnit.unit b : 𝒲[S.I ↑{♡}, S p₁, 𝒮]) *
  --           --     xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β) =
  --           --   ∑ x, ((Matrix.of fun (a : S.I ↑{♡}) b ↦ (ι p₁ ⊠ 𝒪 p₁) α x * ((ι p₁ ⊠ 𝒪 p₁)^* ⊟ ι p₁ ⊡ δ p₁) x α₁ PUnit.unit b : 𝒲[S.I ↑{♡}, S p₁, 𝒮]) *
  --           --     xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * 𝒪 p₁ α' β) <• (ι p₁ ⊠ 𝒪 p₁)^* α' β := sorry
  --           -- conv at this => left; simp [Matrix.of, Equiv.refl]
  --           -- conv at this => left; simp only [DFunLike.coe, EquivLike.coe]
  --           -- simp only [id_eq] at this; simp only [this]; clear this
  --           -- simp [Matrix.sum_apply, Finset.sum_mul]
  --           -- congr with γ
  --           -- simp [Matrix.mul_assoc, mul_assoc]
  --           -- congr! 1
  --           -- simp [Q]
  --           -- simp [RPol.wnka_sem_case]
  --           -- simp [ι, 𝒪, xδ, δ, ← Matrix.mul_assoc]
  --           -- rw [ι_wProd_δ']
  --           -- simp [Matrix.down]
  --           -- simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, S.ι, S.𝒪, 𝒪_heart]
  --           -- apply Finset.sum_bij_ne_zero (fun a _ _ ↦ .inl a)
  --           -- · simp
  --           -- · simp
  --           --   grind
  --           -- · simp
  --           --   intro s₁ s₂ h
  --           --   rcases s₁ with s₁ | s₁
  --           --   · use s₁
  --           --     simp
  --           --     use s₂
  --           --     simp at h
  --           --     contrapose! h
  --           --     rw [← h]; clear h
  --           --     simp [mul_assoc]
  --           --     congr! 1
  --           --     · sorry
  --           --     · sorry
  --           --   use s₂
  --           --   simp
  --           --   sorry
  --           -- · simp
  --           --   sorry

  --           -- simp [Q]
  --           -- simp [sox, fox, Finset.sum_apply]
  --           -- have :
  --           --       (fun (a : S.I ↑{♡}) ↦ ∑ c, (((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^*) α c •> (ι p₁ * δ p₁ c α₁)) PUnit.unit)
  --           --     = ∑ c, (fun (a : S.I ↑{♡}) ↦ (((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^*) α c •> (ι p₁ * δ p₁ c α₁)) PUnit.unit) := by
  --           --   ext
  --           --   simp
  --           -- simp only [S.I] at this; simp only [this]; clear this
  --           -- have :
  --           --       (∑ x, Matrix.of fun (a : S.I ↑{♡}) ↦ (((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^*) α x •> (ι p₁ * δ p₁ x α₁)) PUnit.unit) *
  --           --         xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) =
  --           --       (∑ x, (Matrix.of fun (a : S.I ↑{♡}) ↦ (((ι p₁ ⊠ 𝒪 p₁) * (ι p₁ ⊠ 𝒪 p₁)^*) α x •> (ι p₁ * δ p₁ x α₁)) PUnit.unit) * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])))
  --           --          := sorry
  --           -- simp [Matrix.of, Equiv.refl] at this
  --           -- simp only [DFunLike.coe, EquivLike.coe] at this
  --           -- simp only [id_eq] at this; simp only [this]; clear this
  --           -- simp [Matrix.sum_mul, Matrix.sum_apply, Finset.sum_mul]
  --           -- congr with γ
  --           -- simp [RPol.wnka_sem_case]
  --           -- simp [ι, 𝒪, xδ, δ]
  --           -- simp [← Matrix.mul_assoc]
  --           -- rw [ι_wProd_δ']
  --           -- simp [box, S.ι, Matrix.down, fox, sox, 𝒪_heart, δ]
  --           -- nth_rw 2 [Matrix.mul_apply]
  --           -- simp [box]
  --           -- simp [Matrix.down]
  --           -- simp [Finset.sum_smul']
  --           -- simp [Matrix.sum_apply, Finset.sum_apply]
  --           -- have :
  --           --       (fun (a : S.I ↑{♡}) ↦ (∑ x, ((ι p₁ * 𝒪 p₁ α x) PUnit.unit PUnit.unit * (ι p₁ ⊠ 𝒪 p₁)^* x γ) •> (ι p₁ * δ p₁ γ α₁)) PUnit.unit)
  --           --     = ((∑ x, fun (a : S.I ↑{♡}) ↦ ((ι p₁ * 𝒪 p₁ α x) PUnit.unit PUnit.unit * (ι p₁ ⊠ 𝒪 p₁)^* x γ) •> (ι p₁ * δ p₁ γ α₁) PUnit.unit) : 𝒲[S.I {♡}, S p₁, 𝒮]) := sorry
  --           -- simp at this; simp [this]; clear this


  --           -- simp [Matrix.sum_mul, Matrix.sum_apply, Finset.sum_mul]

  --           -- simp [Finset.sum_mul]
  --           -- simp [Matrix.mul_assoc]
  --           -- conv =>
  --           --   left
  --           --   arg 1


  --           -- simp [Finset.mul_sum, Finset.sum_mul]
  --           -- simp [Finset.mul_sum, Finset.sum_mul, S.ι, S.𝒪, Sum.elim, Matrix.mul_apply, ← mul_assoc, sox, 𝒪_heart, Matrix.sum_mul, Matrix.mul_sum, box, Matrix.down]

  --           -- simp only [← List.cons_append]
  --           -- rw [WNKA.compute_pair]
  --           -- sorry
  --           -- congr with γ
  --           -- simp only [Finset.sum_mul]
  --           -- simp

  --           -- --

  --           -- have : ∀ i, (ι p₁ ⊠ 𝒪 p₁) α i = p₁.wnka.sem ⟨α, [], i⟩ := by intro i; rfl
  --           -- simp only [this]
  --           -- rw [ih₁]
  --           -- nth_rw 2 [Matrix.mul_apply]
  --           -- congr with γ
  --           -- simp only [mul_assoc]
  --           -- congr! 1
  --           -- · exact congrFun (congrArg DFunLike.coe (id (Eq.symm ih₁))) (α, [], γ)
  --           -- · sorry
  --           -- simp only [← mul_assoc]
  --           -- symm
  --           -- simp [Q]
  --           -- sorry
  -- ·
  --   induction xₙ with
  --   | nil => contradiction
  --   | cons α₀ xₙ ih =>
  --     simp_all
  --     intro g hg
  --     simp only [fp₁, Set.mem_setOf_eq] at hg; symm at hg
  --     intro α β
  --     simp [Q, WNKA.sem, GS.pks]
  --     sorry

theorem M'_eq_Q (p₁ : RPol[F,N,𝒮]) (ih : p₁.wnka.sem = G p₁) : M' p₁.Iter = Q p₁.Iter := by
  funext xₙ
  induction xₙ using Nat.strongRecMeasure List.length; next xₙ ihₙ =>
  induction xₙ with
  | nil => exact IsLeast.unique (fp₀_M' p₁) (fp₀_Q p₁)
  | cons α₀ xₙ ih₀ =>
    rw [fp₁_M'_is_fp'' p₁ (α₀ :: xₙ) (by simp)]
    have ih' : Q p₁ = M' p₁ := by ext x α αb; simp [Q]; rw [ih]; rfl
    rw [fp₁_Q_is_fp'' p₁ ih' (α₀ :: xₙ) (by simp)]
    exact fun y a _ ↦ ihₙ y a

attribute [-simp] Function.iterate_succ in
theorem RPol.wnka_sem (p : RPol[F,N,𝒮]) : (RPol.wnka p).sem = G p := by
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
    ext ⟨α, xₙ, β⟩
    exact congrFun₃ (M'_eq_Q p₁ ih) xₙ α β |>.symm

    -- exact congrFun₂ (Q_eq_M'_star p₁ xₙ) α β


    -- -- sorry
    -- apply wnka_sem_eq_of
    -- -- intro A hA αn
    -- simp_all only

    -- intro A α β
    -- simp [RPol.wnka_iter_δ]
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
    --     simp [𝒪_heart]
    --     rw [Matrix.mul_assoc]
    --     nth_rw 1 [Matrix.mul_apply]
    --     simp
    --     nth_rw 1 [box_star_iter]
    --     simp [add_mul]
    --     rw [Matrix.mul_apply]
    --     simp [add_mul, Finset.sum_mul, Finset.sum_add_distrib]

    --     rw [G.star_apply']
    --     simp [GS.ofPks, GS.mk, List.dropLast]


    --     simp [Matrix.add_mul]
    --     simp [-Matrix.of_add_of, Matrix.add_mul]

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
    --     simp [𝒪_heart, LawfulStar.star_eq_sum]
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
    --   simp [𝒪, 𝒪_heart]
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

    -- -- simp [RPol.wnka_iter_δ]
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
    -- --   simp [𝒪_heart]
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
    -- --     simp [← Matrix.mul_assoc, 𝒪_heart, δ.𝒪_heart]
    -- --     sorry

theorem the_complete_theorem [LawfulStar 𝒮] (p : Pol[F,N,𝒮]) (π) (h) :
    p.sem ⟨π, []⟩ h = p.toRPol.wnka.sem (π, h.2.reverse, h.1) := by
  rw [← Pol.toRol_sem_eq_sem, RPol.sem_G, RPol.wnka_sem]
  simp [GS.sem_eq]
  if h₀ : (G p.toRPol) (π, h.2.reverse, h.1) = 0 then
    simp [h₀]
    intro s hs
    split_ifs
    · simp_all [GS.H]
      rintro ⟨_⟩
      subst_eqs
      simp_all
    · simp_all
  else
    rw [ωSum_eq_single ⟨(π, h.2.reverse, h.1), h₀⟩]
    · simp [GS.H]
    · simp_all
      rintro ⟨g₀, g, g₁⟩ hg h
      simp_all [GS.H]
      rw [Prod.eq_iff_fst_eq_snd_eq] at h
      simp_all
      split_ifs
      · simp_all
        grind
      · simp

end WeightedNetKAT
