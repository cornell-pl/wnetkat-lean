import WeightedNetKAT.Language
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Star
import WeightedNetKAT.MatrixStar
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.ComputableSemiring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Topology.Order.ScottTopology

open OmegaCompletePartialOrder
open scoped RightActions

namespace List

section

variable {α : Type*} (l : List α)

def rep : ℕ → List α
  | 0 => []
  | n+1 => l ++ rep n

@[simp] theorem repeat_zero : l.rep 0 = [] := rfl
@[simp] theorem repeat_one : l.rep 1 = l := by simp [rep]
@[simp] theorem repeat_succ {n : ℕ} : l.rep (n + 1) = l ++ l.rep n := rfl

end

@[simp]
theorem take_length_succ {α : Type} (A : List α) : take (A.length + 1) A = A := by
  simp only [take_eq_self_iff, le_add_iff_nonneg_right, zero_le]

end List

open WeightingNotation

namespace WeightedNetKAT

variable {F : Type} [Listed F] [DecidableEq F]
variable {N : Type} [Listed N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

scoped notation "𝟙" => Unit

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝒪 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F N 𝒮 Q: Type)
    [Semiring 𝒮] [Listed F]
where
  /-- `ι` is the initial weightings. -/
  ι : 𝒲[𝟙,Q,𝒮]
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F,N]) → 𝒲[Q,Q,𝒮]
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : (α β : Pk[F,N]) → 𝒲[Q,𝟙,𝒮]
notation "WNKA[" F "," N "," 𝒮 "," Q "]" => WNKA F N 𝒮 Q

/-- An efficient version of [`WNKA`] that uses explicit matrices. -/
structure EWNKA (F N 𝒮 Q: Type)
    [Semiring 𝒮]
    [Listed F] [Listed N] [DecidableEq N]
    [Listed Q]
where
  /-- `ι` is the initial weightings. -/
  ι : E𝒲[𝟙,Q,𝒮]
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : E𝒲[Pk[F,N], Pk[F,N], E𝒲[Q,Q,𝒮]]
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : E𝒲[Pk[F,N], Pk[F,N], E𝒲[Q,𝟙,𝒮]]
notation "EWNKA[" F "," N "," 𝒮 "," Q "]" => EWNKA F N 𝒮 Q

inductive StateSpace where
  | Heart
  | Club
deriving DecidableEq, Fintype

notation "♡" => StateSpace.Heart
notation "♣" => StateSpace.Club

@[grind, simp]
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
def S.Eι {X Y : Type} [Listed X] [Listed Y] : (EMatrix 𝟙 X 𝒮) → (EMatrix 𝟙 Y 𝒮) → (EMatrix 𝟙 (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "Eι[" a "," b"]" => S.Eι a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[grind, simp]
theorem S.Eι_eq_ι {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix 𝟙 X 𝒮} {m₂ : EMatrix 𝟙 Y 𝒮} {i} {j} :
    Eι[m₁, m₂] i j = ι m₁.asMatrix m₂.asMatrix i j := by
  simp [Eι, ι]

def S.𝒪 {X Y : Type} : (Matrix X 𝟙 𝒮) → (Matrix Y 𝟙 𝒮) → (Matrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "𝒪[" a "," b"]" => S.𝒪 a b
def S.E𝒪_lambda {X Y : Type} [Listed X] [Listed Y] : (EMatrix X 𝟙 𝒮) → (EMatrix Y 𝟙 𝒮) → (EMatrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "E𝒪_lambda[" a "," b"]" => S.E𝒪_lambda a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem S.E𝒪_lambda_eq_𝒪 {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix X 𝟙 𝒮} {m₂ : EMatrix Y 𝟙 𝒮} {i} {j} :
    E𝒪_lambda m₁ m₂ i j = 𝒪 m₁.asMatrix m₂.asMatrix i j := by
  simp [E𝒪_lambda, 𝒪]

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
-- @[simp]
theorem S.E𝒪_lambda_eq_𝒪' {X Y : Type} [Listed X] [Listed Y] {m₁ : Matrix X 𝟙 𝒮} {m₂ : Matrix Y 𝟙 𝒮} {i} {j} :
    𝒪 m₁ m₂ i j = E𝒪_lambda (EMatrix.ofMatrix m₁) (EMatrix.ofMatrix m₂) i j := by
  simp [E𝒪_lambda, 𝒪]

section delta

variable {X Y Z W : Type}

attribute [grind] Prod.map Function.Injective in
def S.δ :
    (Matrix X Y 𝒮) →
    (Matrix X W 𝒮) →
    (Matrix Z Y 𝒮) →
    (Matrix Z W 𝒮) →
    (Matrix (X ⊕ Z) (Y ⊕ W) 𝒮) :=
  fun mxy mxw mzy mzw ↦
    (fun xz yw ↦
      xz.elim (fun x ↦ yw.elim (mxy x ·) (mxw x ·))
              (fun z ↦ yw.elim (mzy z ·) (mzw z ·)))

variable [Listed X] [Listed Y] [Listed Z] [Listed W]

notation "δ[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.δ a b c d
attribute [grind] Prod.map Function.Injective in
def S.Eδ_delta :
    (EMatrix X Y 𝒮) →
    (EMatrix X W 𝒮) →
    (EMatrix Z Y 𝒮) →
    (EMatrix Z W 𝒮) →
    (EMatrix (X ⊕ Z) (Y ⊕ W) 𝒮) :=
  fun mxy mxw mzy mzw ↦
    .ofFnSlow (fun xz yw ↦
      xz.elim (fun x ↦ yw.elim (mxy x ·) (mxw x ·))
              (fun z ↦ yw.elim (mzy z ·) (mzw z ·)))

notation "Eδ_delta[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.Eδ_delta a b c d

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem S.Eδ_delta_eq_δ
    (mxy : EMatrix X Y 𝒮)
    (mxw : EMatrix X W 𝒮)
    (mzy : EMatrix Z Y 𝒮)
    (mzw : EMatrix Z W 𝒮)
    {i} {j} :
    Eδ_delta mxy mxw mzy mzw i j = δ mxy.asMatrix mxw.asMatrix mzy.asMatrix mzw.asMatrix i j := by
  simp [Eδ_delta, δ]

end delta

instance : Fintype (S.I {♡}) := ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
instance : Unique (S.I {♡}) where
  default := ⟨♡, by simp⟩
  uniq := by simp
instance S.listed_I_heart : Listed (S.I {♡}) where
  array := #[⟨♡, by simp⟩]
  nodup := by simp
  complete := by simp
  encode _ := 0
  encode_prop := by simp
  encode_len := by simp
instance : Listed (@Set.Elem StateSpace {♡}) := S.listed_I_heart

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

instance S.listed (p : RPol[F,N,𝒮]) : Listed (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    inferInstanceAs (Listed (S.I {♡}))
  | wnk_rpol {dup} => Listed.ofArray #[⟨♡, by simp⟩, ⟨♣, by simp⟩] (by simp) (by rintro ⟨_, (h | h | h)⟩ <;> simp_all)
  | wnk_rpol {~_ ⨀ ~p₁} => S.listed p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁*} => letI := S.listed p₁; Listed.instSum

abbrev η₁ {X : Type} [DecidableEq X] (i : X) : X → 𝒮 :=
  fun i' ↦ if i = i' then 1 else 0
abbrev η₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] (i : X) (j : Y) : Matrix X Y 𝒮 :=
  fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0
abbrev Eη₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] [Listed X] [Listed Y] (i : X) (j : Y) : EMatrix X Y 𝒮 :=
  let i := Listed.encode i; let j := Listed.encode j;
  .ofFn fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def ι (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η₂ () ⟨♡, rfl⟩
  | wnk_rpol {dup} => η₂ () ⟨♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁ |>.concrete
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂] |>.concrete
  | wnk_rpol {~p₁ ; ~p₂} => ι[ι p₁, 0] |>.concrete
  | wnk_rpol {~p₁*} => ι[0, fun () ↦ 1] |>.concrete

def Eι (p : RPol[F,N,𝒮]) : EMatrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    Eη₂ () ⟨♡, rfl⟩
  | wnk_rpol {dup} => Eη₂ () ⟨♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • Eι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => Eι[Eι p₁, Eι p₂]
  | wnk_rpol {~p₁ ; ~p₂} => Eι[Eι p₁, 0]
  | wnk_rpol {~p₁*} => Eι[0, .ofFn fun 0 ↦ 1]

def 𝒞.left_to_unit {X : Type} (m : Matrix (S.I {♡}) X 𝒮) : Matrix 𝟙 X 𝒮 :=
  fun () x ↦ m ⟨♡, rfl⟩ x
def 𝒞.left_to_heart {X : Type} (m : (Matrix 𝟙 X 𝒮)) : Matrix (S.I {♡}) X 𝒮 :=
  fun ⟨♡, _⟩ x ↦ m () x

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem 𝒞.left_to_unit_apply {X : Type} (m : Matrix (S.I {♡}) X 𝒮) (x) (y) :
    𝒞.left_to_unit m x y = m ⟨♡, rfl⟩ y := rfl
omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem 𝒞.left_to_heart_apply {X : Type} (m : Matrix 𝟙 X 𝒮) (x) (y) :
    𝒞.left_to_heart m x y = m () y := by simp [left_to_heart]; split; rfl

def 𝒞.transpose {X Y : Type} (m : (X × Y) →₀ 𝒮) : (Y × X) →₀ 𝒮 :=
  ⟨(m.support.map ⟨fun (y, x) ↦ (x, y), by grind⟩), (fun (y, x) ↦ m (x, y)), (by simp)⟩

variable [Star 𝒮]

section

variable {Pk : Type} [Listed Pk] [Fintype Pk]

def box {X} [Fintype X] {Q : Type} [Mul Q] [AddCommMonoid Q] {Z : Type} [Fintype Z] [Unique Z]
    (l : 𝒲[Z, X, Q]) (r : 𝒲[Pk, Pk, 𝒲[X, Z, Q]]) :
    𝒲[Pk,Pk,Q] :=
  fun α β ↦ (l * r α β).down

infixr:50 " ⊠ " => box

def fox {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B] [Fintype C]
    (l : 𝒲[A, B, Q]) (r : 𝒲[Pk, Pk, 𝒲[B, C, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, C, Q]] :=
  fun α β ↦ l * r α β

infixr:50 " ⊡ " => fox

def sox {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B]
    (l : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, B, Q]] :=
  fun α β ↦ (Listed.array.map fun m ↦ l α m •> r m β).sum

infixr:50 " ⊟ " => sox

def sox' {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B]
    (l : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) (r : 𝒲[Pk, Pk, Q]) :
    𝒲[Pk, Pk, 𝒲[A, B, Q]] :=
  fun α β ↦ (Listed.array.map fun m ↦ l α m <• r m β).sum

infixr:50 " ⊟' " => sox'

@[simp]
theorem Listed.array_sum_eq_finset_sum {α ι : Type} [Listed ι] [Fintype ι] [AddCommMonoid α] (f : ι → α) :
    (Listed.array.map f).sum = ∑ x, f x := by
  classical
  rw [← @Array.sum_eq_sum_toList]
  simp [← List.sum_toFinset (f:=f) Listed.nodup, Fintype.sum_subset]

theorem add_sox {A B : Type} {Q : Type} [NonUnitalSemiring Q]
    [Fintype A] [Fintype B]
    (l l' : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((l + l') ⊟ r) = (l ⊟ r) + (l' ⊟ r) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, add_mul, Finset.sum_add_distrib]

theorem mul_sox {A B : Type} {Q : Type} [NonUnitalSemiring Q]
    [Fintype A] [Fintype B]
    (l l' : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((l * l') ⊟ r) = (l ⊟ (l' ⊟ r)) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

variable [DecidableEq Pk]

@[simp]
theorem one_sox {A B : Type} {Q : Type} [Semiring Q]
    [Fintype A] [Fintype B]
    (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((1 : 𝒲[Pk, Pk, Q]) ⊟ r) = r := by
  ext α β a b
  simp [sox, Matrix.one_apply]

def crox {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B] [DecidableEq C] [Fintype C]
    (l : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) (r : 𝒲[Pk, Pk, 𝒲[B, C, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, C, Q]] :=
  fun α β ↦ (Listed.array.map fun m ↦ l α m * r m β).sum

infixr:50 " ⊞ " => crox

end

variable [DecidableEq N]

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
      (𝒪 p₁ ⊟' 𝒪_heart p₁) α β,
      𝒪_heart p₁ α β
    ]

end

instance : Unique (Fin (Listed.size 𝟙)) where
  uniq := by intro ⟨a, ha⟩; have : Listed.size 𝟙 = 1 := rfl; grind

def E𝒪_lambda [DecidableEq F] (p : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] (EMatrix (S p) 𝟙 𝒮) :=
  match _ : p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} => .ofFn fun α β ↦ if α = β then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {@test ~γ} =>
    let γ := Listed.encode γ
    .ofFn fun α β ↦ if α = β ∧ β = γ then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {@mod ~π} => let π := Listed.encode π; .ofFn fun α β ↦ if β = π then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {dup} => let v := Eη₂ ⟨♣, by simp⟩ (); .ofFn fun α β ↦ if α = β then v else 0
  | wnk_rpol {~_ ⨀ ~p₁} => let 𝒪₁ := E𝒪_lambda p₁; .ofFn fun α β ↦ 𝒪₁.getN α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
    let 𝒪₁ := E𝒪_lambda p₁
    let 𝒪₂ := E𝒪_lambda p₂
    .ofFn fun α β ↦ E𝒪_lambda[𝒪₁.getN α β, 𝒪₂.getN α β]
  -- | wnk_rpol {~p₁ ; ~p₂} => E𝒪_lambda[∑ γ, ((E𝒪_lambda p₁).get α γ * Eι p₂ * (E𝒪_lambda p₂).get γ β), (E𝒪_lambda p₂).get α β]
  | wnk_rpol {~p₁ ; ~p₂} =>
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNatMatrix₂
    let M₂ := E𝒪_lambda p₂ |>.asNatMatrix₂
    let M₃ := Eι p₂ |>.asNatMatrix
    .ofFn fun α β ↦
      E𝒪_lambda[(Listed.array.map fun γ ↦ (𝒪₁ α γ * M₃ * M₂ γ β)).sum |> EMatrix.ofNatMatrix, M₂ α β |> EMatrix.ofNatMatrix]
  | wnk_rpol {~p₁*} =>
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNatMatrix
    let M₂ :=
      let ι₁ := EMatrix.asNatMatrix (Eι p₁)
      let 𝒪₁ := EMatrix.asNatMatrix₂ (E𝒪_lambda p₁)
      let X := EMatrix.ofNatMatrix (ι₁ ⊠ 𝒪₁) |>.asNMatrix
      let Y : N𝒲[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮] := X^*
      Y
    .ofFn fun α β ↦
      E𝒪_lambda[
        (Listed.array.map fun γ ↦ 𝒪₁ α γ <• M₂ γ β).sum,
        .ofFn fun _ _ ↦ M₂ α β
      ]

def E𝒪_heart (p₁ : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] 𝒮 :=
  let ι₁ := EMatrix.asNatMatrix (Eι p₁)
  let 𝒪₁ := EMatrix.asNatMatrix₂ (E𝒪_lambda p₁)
  let X := EMatrix.ofNatMatrix (ι₁ ⊠ 𝒪₁) |>.asNMatrix
  let Y : N𝒲[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮] := X^*
  Y

omit [DecidableEq F] [Listed N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] in
@[simp]
theorem Eι_eq_ι {p : RPol[F,N,𝒮]} : Eι p = EMatrix.ofMatrix (ι p) := by
  classical
  induction p
  next =>
    ext i j
    simp [ι, Eι, η₂, Listed.encode]
    rcases j with j | j
    · simp
    · rename_i h; simp at h
  next =>
    ext i j
    simp [ι, Eι, η₂, Listed.encode]
    rcases j with j | j
    · simp
    · rename_i h; simp at h
  next =>
    ext i j
    simp [ι, Eι, η₂, Listed.encode]
    rcases j with j | j
    · simp
    · rename_i h; simp at h
  next =>
    ext i j
    simp [ι, Eι, η₂, Listed.encode]
    rcases j with j | j
    · simp
    · rename_i h; simp at h
  next =>
    ext i j
    simp [ι, Eι, η₂]
  next p q ihp ihq =>
    ext i j
    simp [ι, Eι]
    have := S.Eι_eq_ι (m₁:=Eι p) (m₂:=0) (i:=i) (j:=j)
    simp only [EMatrix.zero_asMatrix] at this
    simp only [S.Eι_eq_ι] at this
    convert this
    · simp
    · simp [ihp]
  next p ih =>
    ext i j
    simp [ι, Eι, ih, HSMul.hSMul, SMul.smul]
  next p q ihp ihq =>
    ext i j
    simp [ι, Eι, ihp, ihq, S.Eι, S.ι]
  next p ih =>
    ext i j
    simp [ι, Eι, S.Eι, S.ι]

omit [OmegaCompletePartialOrder 𝒮] in
@[simp]
theorem E𝒪_lambda_eq_𝒪 {p : RPol[F,N,𝒮]} : E𝒪_lambda p = EMatrix.ofMatrix₂ (𝒪 p) := by
  classical
  induction p
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
    rw [EMatrix.instZero]
    simp only [OfNat.ofNat, EMatrix.ofNatMatrix, S, S.I, EMatrix.dfunlike_coe_NMatrix_ofFn]
    rfl
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
    split_ifs <;> simp
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
    split_ifs <;> simp
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
    split_ifs <;> simp
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
    split_ifs <;> simp
    simp [η₂]
  next p q ihp ihq =>
    ext α β i j
    simp [𝒪, E𝒪_lambda]
    simp_all
  next p ih =>
    ext
    simp [𝒪, E𝒪_lambda, ih]
  next p q ihp ihq =>
    ext
    simp [𝒪, E𝒪_lambda, ihp, ihq]
  next p ih =>
    ext α β i j
    simp [𝒪, E𝒪_lambda, ih, sox']
    rcases i with _ | _
    · simp [HSMul.hSMul, SMul.smul]
      congr!
      simp
      simp [𝒪_heart, Star.star]
      congr!
      · ext
        simp [EMatrix.asNMatrix, box]
        rfl
      · simp [𝒪_heart, Star.star]
        congr!
        ext
        simp [EMatrix.asNMatrix, box]
        rfl
    · simp
      simp [𝒪_heart, Star.star]
      simp [HSMul.hSMul, SMul.smul]
      congr! 4
      · simp
        congr!
        ext
        simp [EMatrix.asNMatrix, box]
        rfl
      · simp
        congr!
        ext
        simp [EMatrix.asNMatrix, box]
        rfl

def ι_aux (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p) 𝒮 := Eι p |>.asMatrix

@[csimp] theorem ι_csimp : @ι = @ι_aux := by
  funext p x _ _ _ _ _ p
  simp [ι_aux, Eι_eq_ι]

def 𝒪_aux (p : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p) 𝟙 𝒮) := E𝒪_lambda p |>.asMatrix₂

@[csimp] theorem 𝒪_csimp : @𝒪 = @𝒪_aux := by
  ext; simp [𝒪_aux, E𝒪_lambda_eq_𝒪]

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
    δ[[δ' p₁ α β, 0],
      [((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α β).coe_unique_left, 0]]
where δ' (p₁ : RPol[F,N,𝒮]) : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, S p₁, 𝒮]] := δ p₁ + (𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁)

instance : Unique (Fin (Listed.size 𝟙)) where
  default := ⟨0, by show 0 < 1; omega⟩
  uniq := by have : Listed.size 𝟙 = 1 := rfl; omega
instance : Unique (Fin (Listed.size (S.I {♡}))) where
  default := ⟨0, by show 0 < 1; omega⟩
  uniq := by have : Listed.size (S.I {♡}) = 1 := rfl; omega

def Eδ_delta (p : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] (EMatrix (S p) (S p) 𝒮) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} => .ofFn fun α β ↦
    0
  | wnk_rpol {dup} => .ofFn fun α β ↦ .ofFnSlow fun s ↦ if s.val = ♡ ∧ α = β then η₁ ⟨♣, by simp⟩ else 0
  | wnk_rpol {~_ ⨀ ~p₁} => Eδ_delta p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
    let δ₁ := Eδ_delta p₁
    let δ₂ := Eδ_delta p₂
    .ofFn fun α β ↦
      Eδ_delta[[δ₁.getN α β,    0],
        [0,           δ₂.getN α β]]
  | wnk_rpol {~p₁ ; ~p₂} =>
    let ι₂ := Eι p₂ |>.asNatMatrix
    let δ₁ := Eδ_delta p₁ |>.asNatMatrix
    let δ₂ := Eδ_delta p₂ |>.asNatMatrix₂
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNatMatrix₂
    .ofFn fun α β ↦
      Eδ_delta[[δ₁ α β,    EMatrix.ofNatMatrix (∑ γ, (𝒪₁ α γ * ι₂ * δ₂ γ β))],
        [0,           EMatrix.ofNatMatrix (δ₂ α β)]]
  | wnk_rpol {~p₁*} =>
    let ι₁ := Eι p₁ |>.asNatMatrix
    let δ₁ := Eδ_delta p₁ |>.asNatMatrix₂
    let 𝒪_heart₁ := E𝒪_heart p₁ |>.asNatMatrix
    let X := 𝒪_heart₁ ⊟ ι₁ ⊡ δ₁
    let Eδ' : E𝒲[Pk[F,N], Pk[F,N], E𝒲[S p₁, S p₁, 𝒮]] :=
      δ₁ + ((E𝒪_lambda p₁).asNatMatrix₂ ⊞ X) |> EMatrix.ofNatMatrix₂
    .ofFn fun α β ↦
      Eδ_delta[[Eδ'.getN α β, 0],
        [(X α β).coe_unique_left |> EMatrix.ofNatMatrix, 0]]

omit [OmegaCompletePartialOrder 𝒮] in
@[simp]
theorem E𝒪_heart_eq_𝒪_heart {p : RPol[F,N,𝒮]} : E𝒪_heart p = EMatrix.ofMatrix (𝒪_heart p) := by
  simp [E𝒪_heart, 𝒪_heart, Star.star]
  ext
  nth_rw 1 [EMatrix.get]
  congr
  ext
  simp [box]
  rfl

omit [OmegaCompletePartialOrder 𝒮] in
@[simp]
theorem Eδ_delta_eq_δ {p : RPol[F,N,𝒮]} : Eδ_delta p = EMatrix.ofMatrix₂ (δ p) := by
  classical
  induction p
  next => ext; simp [Eδ_delta, δ]; exact EMatrix.zero_apply
  next => ext; simp [Eδ_delta, δ]; exact EMatrix.zero_apply
  next => ext; simp [Eδ_delta, δ]; exact EMatrix.zero_apply
  next => ext; simp [Eδ_delta, δ]; exact EMatrix.zero_apply
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp_all [Eδ_delta, δ, S]; congr!; ext; simp
  next => ext; simp_all [Eδ_delta, δ, S]
  next => ext; simp_all [Eδ_delta, δ]
  next p ih =>
    ext α β i j; simp_all [Eδ_delta, δ, δ.δ']
    congr!
    · ext i' j'; simp_all
      simp [EMatrix.ofNatMatrix₂]
      simp [sox, fox, crox, Matrix.sum_apply, Matrix.mul_apply]
    · ext i j
      simp_all only [EMatrix.ofNatMatrix_asMatrix]
      simp [sox, fox, -Matrix.coe_unique_left_apply]
      apply EMatrix.sized_eq_of
      simp only [EMatrix.ofNatMatrix_sum, EMatrix.ofMatrix_get]
      simp only [EMatrix.get_eq_asMatrix, EMatrix.asMatrix_sum]
      congr!
      ext
      simp

def δ_aux (p : RPol[F,N,𝒮]) : 𝒲[Pk[F,N],Pk[F,N],𝒲[S p,S p,𝒮]] := Eδ_delta p |>.asMatrix₂

@[csimp] theorem δ_csimp : @δ = @δ_aux := by
  ext
  simp [δ_aux, Eδ_delta_eq_δ]

def RPol.wnka (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] := ⟨ι p, δ p, 𝒪 p⟩
def RPol.ewnka (p : RPol[F,N,𝒮]) : EWNKA[F,N,𝒮,S p] := ⟨Eι p, Eδ_delta p, E𝒪_lambda p⟩

section

variable {Q : Type} [Listed Q]
variable (𝒜 : WNKA[F,N,𝒮,Q]) (ℰ : EWNKA[F,N,𝒮,Q])

def WNKA.toEWNKA : EWNKA[F,N,𝒮,Q] where
  ι := EMatrix.ofMatrix 𝒜.ι
  δ := EMatrix.ofMatrix₂ 𝒜.δ
  𝒪 := EMatrix.ofMatrix₂ 𝒜.𝒪

def EWNKA.toWNKA : WNKA[F,N,𝒮,Q] where
  ι := EMatrix.asMatrix ℰ.ι
  δ := EMatrix.asMatrix₂ ℰ.δ
  𝒪 := EMatrix.asMatrix₂ ℰ.𝒪

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
@[simp] theorem WNKA.toWNKA_toEWNKA : 𝒜.toEWNKA.toWNKA = 𝒜 := by simp [WNKA.toEWNKA, EWNKA.toWNKA]; congr <;> ext <;> simp
omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
@[simp] theorem EWNKA.toEWNKA_toWNKA : ℰ.toWNKA.toEWNKA = ℰ := by simp [WNKA.toEWNKA, EWNKA.toWNKA]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.wnka_toEWNKA (p : RPol[F,N,𝒮]) : p.wnka.toEWNKA = p.ewnka := by
  simp [wnka, ewnka, WNKA.toEWNKA]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.ewnka_toWNKA (p : RPol[F,N,𝒮]) : p.ewnka.toWNKA = p.wnka := by
  simp [wnka, ewnka, EWNKA.toWNKA]
  constructor <;> ext <;> simp

def RPol.wnka_fast (p : RPol[F,N,𝒮]) := p.ewnka.toWNKA

@[csimp] theorem RPol.wnka_csimp : @RPol.wnka = @RPol.wnka_fast := by ext; simp [wnka_fast]

@[simp]
def EWNKA.toEWNKA_ι_apply {α β} : ℰ.toWNKA.ι α β = ℰ.ι α β := by
  simp [EWNKA.toWNKA]
@[simp]
def EWNKA.toEWNKA_δ_apply {α β} : ℰ.toWNKA.δ α β = (ℰ.δ α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl
@[simp]
def EWNKA.toEWNKA_𝒪_apply {α β} : ℰ.toWNKA.𝒪 α β = (ℰ.𝒪 α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl

end

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.wnka_ι (p : RPol[F,N,𝒮]) : p.wnka.ι = ι p := rfl
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.wnka_δ (p : RPol[F,N,𝒮]) : p.wnka.δ = δ p := rfl
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.wnka_𝒪 (p : RPol[F,N,𝒮]) : p.wnka.𝒪 = 𝒪 p := rfl

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

def WNKA.sem {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨(fun x ↦ (𝒜.ι * 𝒜.compute x.pks) () ()), SetCoe.countable _⟩

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
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

omit [DecidableEq F] [DecidableEq N] [Listed N] in
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

omit [DecidableEq F] [DecidableEq N] [Listed N] in
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
theorem ι_wProd_𝒪 {A B : Type} [Fintype A] [Fintype B]
    {X : Matrix 𝟙 A 𝒮} {Y : Matrix 𝟙 B 𝒮} {Z : Matrix A 𝟙 𝒮} {W : Matrix B 𝟙 𝒮} :
    (ι[X, Y] * 𝒪[Z, W]) = (X * Z) + (Y * W) := by
  ext i j
  simp [Matrix.mul_apply, S.ι, S.𝒪]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
theorem ι_wProd_δ {A B C D : Type} [Fintype A] [Fintype B]
    {X : Matrix 𝟙 A 𝒮} {Y : Matrix 𝟙 B 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (ι[X, Y] * δ[[Z, W], [U, V]]) = ι[X * Z + Y * U, X * W + Y * V] := by
  ext _ a
  simp [Matrix.mul_apply, S.ι, S.δ]
  rcases a with c | d <;> simp

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
theorem δ_wProd_δ {A B C D E F : Type} [Fintype C] [Fintype D]
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
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
theorem δ_wProd_𝒪 {A B C D : Type}
    [Fintype C] [Fintype D]
    {X : Matrix C 𝟙 𝒮} {Y : Matrix D 𝟙 𝒮}
    {Z : Matrix A C 𝒮} {W : Matrix A D 𝒮}
    {U : Matrix B C 𝒮} {V : Matrix B D 𝒮}
    :
    (δ[[Z, W], [U, V]] * 𝒪[X, Y]) = 𝒪[Z * X + W * Y, U * X + V * Y] := by
  ext a _
  simp [Matrix.mul_apply, S.𝒪, S.δ]
  rcases a with c | d <;> simp

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
@[simp]
theorem S.δ_identity {A B : Type} [DecidableEq A] [DecidableEq B] :
    (δ[[1,0],[0,1]] : Matrix (A ⊕ B) (A ⊕ B) 𝒮) = 1 := by
  ext ab₁ ab₂
  rcases ab₁ with a₁ | b₁ <;> rcases ab₂ with a₂ | b₂ <;> simp [S.δ, Matrix.one_apply]

def GS.ofPks (l : List Pk[F,N]) (h : 2 ≤ l.length) : GS[F,N] :=
  GS.mk (l.head (List.ne_nil_of_length_pos (by omega))) (l.drop 1).dropLast (l.getLast (List.ne_nil_of_length_pos (by omega)))

omit [DecidableEq F] [DecidableEq N] [Listed N] in
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

-- omit in
omit [DecidableEq F] [DecidableEq N] [Listed N] in
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem RPol.wnka_sem_pair (p : RPol[F,N,𝒮]) (α γ : Pk[F,N]) :
    p.wnka.sem (α, [], γ) = (ι p * 𝒪 p α γ) () () := by simp [wnka]; rfl

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
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
    simp only [wnka] at h₂
    exact h₂ A α α'

-- def xδ {p₁ : RPol[F,N,𝒮]} (d : Pk[F,N] → Pk[F,N] → 𝒲[S p₁, S p₁, 𝒮]) (xs : List Pk[F,N]) : 𝒲[S p₁, S p₁, 𝒮] :=
def xδ {X : Type} [DecidableEq X] [Fintype X] (d : Pk[F,N] → Pk[F,N] → 𝒲[X, X, 𝒮]) (xs : List Pk[F,N]) : 𝒲[X, X, 𝒮] :=
  match xs with
  | [] | [_] => 1
  | α::α'::xs => d α α' * xδ d (α'::xs)

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
variable [Inhabited Pk[F,N]] in
theorem xδ_δ_iter {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} :
      xδ (δ p₁.Iter) (α :: xₙ)
    = δ[[xδ (δ.δ' p₁) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α xₙ.head! * xδ (δ.δ' p₁) xₙ).coe_unique_left,if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp only [xδ, S.I, ↓reduceIte, S.δ_identity]
  | cons α₁ xₙ ih => rw [xδ, ih, δ, δ_wProd_δ]; simp [xδ]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem RPol.wnka_sem_case (p₁ : RPol[F,N,𝒮]) {α β} {xₙ} :
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

-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_drop :
    (RPol.wnka wnk_rpol {drop}).sem = G (wnk_rpol {drop} : RPol[F,N,𝒮]) := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪, Matrix.zero_apply]
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, List.nil_append,
      WNKA.compute, δ, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply]
-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_skip :
    (RPol.wnka wnk_rpol {skip}).sem = G (wnk_rpol {skip} : RPol[F,N,𝒮]) := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪]
    split_ifs with h₁ h₂ h₃ <;> subst_eqs <;> (try rfl) <;> grind only
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, δ, Matrix.zero_mul, Matrix.zero_apply,
      right_eq_ite_iff, forall_exists_index]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff, forall_exists_index]
    grind
-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_test {t} :
    (RPol.wnka wnk_rpol {@test ~t}).sem = G (wnk_rpol {@test ~t} : RPol[F,N,𝒮]) := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝒪, ι, GS.pks]
    split_ifs <;> (try rfl) <;> grind only
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, List.nil_append,
      WNKA.compute, δ, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
    grind
-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_mod {π} :
    (RPol.wnka wnk_rpol {@mod ~π}).sem = G (wnk_rpol {@mod ~π} : RPol[F,N,𝒮]) := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪]
    split_ifs with h₁ h₂ h₃ <;> subst_eqs <;> (try rfl) <;> grind only
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, List.nil_append,
      WNKA.compute, δ, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
    grind only
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
    grind only
-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_compute'_dup {A : List Pk[F,N]} :
      wnk_rpol {dup}.wnka.compute' (𝒮:=𝒮) A
    = match A with
      | [] | [_] => 1
      | [α, β] => if α = β then η₂ ⟨♡, by simp⟩ ⟨♣, by simp⟩ else 0
      | _ => 0
    := by
  induction A with
  | nil => grind [WNKA.compute']
  | cons α₁ A ih₁ =>
    induction A with
    | nil => grind [WNKA.compute']
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

-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
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
    split_ifs <;> try grind
    rfl
  next α₀ α₁ h =>
    have : A = [α₀] := by
      have := congrArg List.length h
      rcases A <;> grind [List.length_eq_zero_iff]
    subst_eqs
    simp [G, GS.mk, GS.ofPks]
    if α₀ = α then
      subst_eqs
      simp only [↓reduceIte, 𝒪]
      split_ifs
      · subst_eqs
        simp_all [ι, Matrix.mul_apply]
      · subst_eqs; grind
      · grind
      · simp only [Matrix.mul_zero, Matrix.zero_apply]
    else
      simp only [‹¬α₀ = α›, ↓reduceIte, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
      grind
  next h =>
    cases A
    · grind
    · simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, G, GS.mk, GS.ofPks,
      G.ofPk_apply, right_eq_ite_iff, forall_exists_index]
      grind

-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_add {p₁ p₂ : RPol[F,N,𝒮]} :
    wnk_rpol {~p₁ ⨁ ~p₂}.wnka.sem = p₁.wnka.sem + p₂.wnka.sem := by
  ext ⟨α, xₙ, β⟩
  simp only [wnka_sem_case, ι, List.getLastD_eq_getLast?, 𝒪, Countsupp.add_apply]
  generalize ι p₁ = ι₁
  generalize ι p₂ = ι₂
  induction xₙ using List.reverseRecOn generalizing ι₁ ι₂ with
  | nil =>
    simp [xδ, Matrix.down]
    rw [ι_wProd_𝒪]
    rfl
  | append_singleton xₙ α' ih =>
    clear ih
    simp [List.getLast?_cons]
    induction xₙ generalizing α ι₁ ι₂ with
    | nil => simp [xδ, δ]; rw [ι_wProd_δ, ι_wProd_𝒪]; simp
    | cons α₀ xₙ ih => simp [xδ, δ, ← Matrix.mul_assoc, ι_wProd_δ, ih]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem RPol.wnka_sem_weight {w} {p : RPol[F,N,𝒮]} :
    wnk_rpol {~w ⨀ ~p}.wnka.sem = (w * p.wnka.sem) := by
  ext ⟨α, xₙ, β⟩
  simp only [wnka_sem_case, ι, Matrix.concrete_id, id_eq, Matrix.smul_mul,
    List.getLastD_eq_getLast?, 𝒪, Matrix.down_smul_left, smul_eq_mul, Countsupp.hMul_apply_left]
  congr
  induction xₙ generalizing α with
  | nil => simp [xδ]
  | cons α₀ xₙ ih => simp [xδ, δ, ih]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
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
        grind [Matrix.mul_assoc]

-- omit [LawfulStar 𝒲[Pk[F,N], Pk[F,N], 𝒮]] in
theorem RPol.wnka_sem_seq {p₁ p₂ : RPol[F,N,𝒮]}
    (ih₁ : p₁.wnka.sem = G p₁) (ih₂ : p₂.wnka.sem = G p₂) :
    wnk_rpol {~p₁ ; ~p₂}.wnka.sem = G wnk_rpol {~p₁; ~p₂} := by
  apply wnka_sem_eq_of
  intro A α α'
  letI : Inhabited Pk[F,N] := ⟨α⟩
  simp only [ι, Matrix.concrete_id, id_eq, seq_wnka_compute'', List.length_append, List.length_cons,
    List.length_nil, zero_add, add_tsub_cancel_right, List.getElem!_eq_getElem?_getD, 𝒪, G,
    GS.ofPks, GS.mk, List.drop_one, ne_eq, reduceCtorEq, not_false_eq_true,
    List.getLast_append_of_ne_nil, List.cons_ne_self, List.getLast_cons, List.getLast_singleton,
    G.concat_apply, List.length_dropLast, List.length_tail, Nat.reduceAdd, Nat.add_one_sub_one,
    GS.splitAtJoined, List.splitAt_eq]
  simp only [← ih₁, ← ih₂]
  rw [ι_wProd_δ, ι_wProd_𝒪]
  nth_rw 2 [Finset.sum_comm]
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, ← Finset.sum_add_distrib]
  congr with γ
  simp [Finset.sum_range_add]
  rw [add_comm]
  rcases A with _ | ⟨α₀, A⟩
  · simp [WNKA.compute', ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
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
            simp only [List.take_succ_cons, List.take_nil, List.cons_append, List.nil_append,
              WNKA.compute_pair', wnka_𝒪, this]
    · simp [List.take_append, WNKA.compute_pair', ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      simp [wnka]
      rfl

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

noncomputable def M' (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ G p ⟨α, xᵢ, β⟩
syntax "M'⟦" cwnk_rpol "⟧" : term
macro_rules | `(M'⟦$p⟧) => `(M' wnk_rpol { $p })
open Lean Elab PrettyPrinter Delaborator Meta Command Term in
@[app_unexpander M']
def M'.unexpander : Unexpander
| `($_ $y) => do
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | y => `(cwnk_rpol|~$y)
  `(M'⟦$y⟧)
| _ => throw ()

noncomputable def N'_ij (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) (i : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  M' p (xᵢ.take i) * M'⟦~p*⟧ (xᵢ.drop i)

noncomputable def N' (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  ∑ i ∈ Finset.range xᵢ.length, N'_ij p xᵢ (i + 1)

omit [Star 𝒮] in
theorem G.star_apply (p₁ : RPol[F,N,𝒮]) (α : Pk[F,N]) (s) (β : Pk[F,N]) :
      (G⟦~p₁*⟧ : _ →c 𝒮) (α, s, β)
    = G⟦skip⟧ (α, s, β) +
        (∑ γ, (G p₁) (α, [], γ) * G⟦~p₁*⟧ (γ, s, β)) +
          ∑ i ∈ Finset.range s.length,
            (M'⟦~p₁⟧ (s.take (i + 1)) * M'⟦~p₁*⟧ (s.drop (i + 1))) α β := by
  unfold M'
  simp [G]
  rw [ωSum_nat_eq_succ]
  simp
  conv => left; right; arg 1; ext x; rw [G]
  simp [G.concat_apply]
  nth_rw 2 [add_comm]
  simp only [Finset.sum_range_add, Finset.range_one, Finset.sum_singleton]
  conv => left; right; arg 1; ext x; left; arg 2; ext y; rw [GS.splitAtJoined]
  simp only [G, ofPk_apply, List.splitAt_eq, List.take_zero, List.drop_zero, ωSum_add,
    ωSum_sum_comm, ωSum_mul_left, Matrix.mul_apply]
  rw [add_assoc]
  congr! 5
  · simp only [GS.splitAtJoined, List.splitAt_eq]
    rw [add_comm]
  · simp only [GS.splitAtJoined, List.splitAt_eq]
    rw [add_comm]

omit [Star 𝒮] in
theorem M'.iter_eq (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) :
    M'⟦~p₁*⟧ xₙ =
      if xₙ = [] then
        1 + M'⟦~p₁⟧ [] * M'⟦~p₁*⟧ xₙ
      else
        N' p₁ xₙ + M'⟦~p₁⟧ [] * M'⟦~p₁*⟧ xₙ := by
  split_ifs
  · subst_eqs
    unfold M'
    ext α β
    convert G.star_apply p₁ α [] β
    simp [Matrix.add_apply]
    congr
    simp [G, GS.mk, Matrix.one_apply]; split_ifs with _ h
    · rfl
    · subst_eqs; grind
    · grind
    · rfl
  · conv => left; unfold M'
    ext α β
    convert G.star_apply p₁ α xₙ β
    simp
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    rw [add_comm]
    have : G (F:=F) (N:=N) (𝒮:=𝒮) RPol.Skip (α, xₙ, β) = 0 := by
      simp [G, h10, GS.mk]; intro x hx; obtain ⟨_⟩ := hx; contradiction
    simp [this]; clear this
    rw [Matrix.mul_apply]
    congr
    rw [N']
    simp only [N'_ij, Matrix.sum_apply]

def fp₀ (p₁ : RPol[F,N,𝒮]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  Z = 1 + M'⟦~p₁⟧ [] * Z
noncomputable def eq₁ (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  N' p₁ xₙ + M'⟦~p₁⟧ [] * Z
def fp₁ (p₁ : RPol[F,N,𝒮]) (xₙ : List Pk[F,N]) (Z : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) :=
  Z = N' p₁ xₙ + M'⟦~p₁⟧ [] * Z

noncomputable def Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ p.wnka.sem ⟨α, xᵢ, β⟩
syntax "Q⟦" cwnk_rpol "⟧" : term
macro_rules | `(Q⟦$p⟧) => `(Q wnk_rpol { $p })
open Lean Elab PrettyPrinter Delaborator Meta Command Term in
@[app_unexpander Q]
def Q.unexpander : Unexpander
| `($_ $y) => do
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | y => `(cwnk_rpol|~$y)
  `(Q⟦$y⟧)
| _ => throw ()

noncomputable def N'Q_ij (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) (i : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  Q p (xᵢ.take i) * Q⟦~p*⟧ (xᵢ.drop i)

noncomputable def N'Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
  ∑ i ∈ Finset.range xᵢ.length, N'Q_ij p xᵢ (i + 1)

omit [Star 𝒮] in
theorem M_unroll_empty (p₁ : RPol[F,N,𝒮]) : 1 + M'⟦~p₁⟧ [] * M'⟦~p₁*⟧ [] = M'⟦~p₁*⟧ [] := by
  nth_rw 2 [M'.iter_eq]
  simp

variable [∀ n, LawfulStar (NMatrix n n 𝒮)]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem box_eq_M'_of_empty (p₁ : RPol[F,N,𝒮]) : (ι p₁ ⊠ 𝒪 p₁) = M'⟦~p₁⟧ [] := by
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
    simp [Matrix.mul_sum, ← Matrix.mul_assoc]
    rw [G.concat_apply]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.univ_unique, PUnit.default_eq_unit,
      Finset.sum_mul, mul_assoc, Finset.sum_singleton, List.length_nil, zero_add, Finset.range_one,
      GS.splitAtJoined, List.splitAt_eq, List.take_nil, List.drop_nil, ← ih₁, ← ih₂, Finset.mul_sum,
      Finset.sum_const, Finset.card_singleton, one_smul]
  | Iter p ih =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp [𝒪_heart, Matrix.mul_apply, LawfulStar.star_eq_sum, G.iter]
    congr with n
    induction n generalizing α β with
    | zero => simp [G, GS, G.ofPk, Matrix.one_apply, GS.mk]
    | succ n ih' =>
      simp only [Function.iterate_succ', Function.comp_apply]
      simp only [pow_succ', Matrix.mul_apply, ih']; clear ih'
      rw [G.concat_apply]
      simp [GS.splitAtJoined, ← ih]
      rfl
  | Add p₁ p₂ ih₁ ih₂ =>
    simp [ι, 𝒪, G]
    rw [ι_wProd_𝒪]
    simp [← ih₁, ← ih₂]
  | Weight w p ih =>
    simp [ι, 𝒪, G, ← ih]

theorem 𝒪_heart_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (𝒪_heart p₁) := by
  constructor
  · simp [fp₀, 𝒪_heart, LawfulStar.star_eq_sum, ← Matrix.ωSum_mul_left, box_eq_M'_of_empty]
    rw [ωSum_nat_eq_succ]
    simp [pow_succ']
  · intro g hg
    simp [fp₀] at hg
    symm at hg
    simp [𝒪_heart, LawfulStar.star_eq_sum, box_eq_M'_of_empty, ωSum_nat_eq_ωSup]
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      simp [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum]
      rw [add_comm, ← hg]
      gcongr

theorem box_star_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (ι p₁ ⊠ 𝒪 p₁)^* := by
  have := 𝒪_heart_fp₀ p₁
  simpa [𝒪_heart]

theorem M_fp₀ (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (M'⟦~p₁⟧ [])^* := by
  constructor
  · simp [fp₀, star_iter]
  · intro g hg
    simp [fp₀] at hg
    symm at hg
    simp [LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, Chain.mk_apply]
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
    unfold Q
    simp
    rfl
  · intro g hg
    simp [fp₀] at hg
    symm at hg
    simp [LawfulStar.star_eq_sum]
    rw [ωSum_nat_eq_ωSup]
    simp only [ωSup_le_iff, Chain.mk_apply]
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
      unfold Q
      simp
      rfl

theorem M_empty_star_eq_heart (p₁ : RPol[F,N,𝒮]) : (M'⟦~p₁⟧ [])^* = (ι p₁ ⊠ 𝒪 p₁)^* := by
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

omit [Star 𝒮] [∀ (n : ℕ), LawfulStar N𝒲[n, n, 𝒮]] in
theorem fp₀_M' (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (M'⟦~p₁*⟧ []) := by
  constructor
  · simp [fp₀]
    nth_rw 1 [M'.iter_eq]
    simp
  · simp [fp₀]
    intro g hg α β
    simp at hg; symm at hg
    simp [M', G, ωSum_nat_eq_ωSup]
    intro i
    induction i generalizing α with
    | zero =>
      apply le_trans (b:=0)
      · rfl
      · simp
    | succ i ih =>
      rw [Finset.sum_range_succ', ← hg]
      simp only [RPol.iter, Matrix.add_apply]
      rw [add_comm]
      gcongr
      · simp [G, Matrix.one_apply, GS.mk]; split_ifs <;> simp_all; grind
      · simp [G, G.concat_apply, GS.splitAtJoined, Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp [← Finset.mul_sum]
        gcongr with γ hγ
        · rfl
        · apply ih
omit [Star 𝒮] [∀ (n : ℕ), LawfulStar N𝒲[n, n, 𝒮]] in
theorem fp₁_M' (p₁ : RPol[F,N,𝒮]) (xₙ) (hxₙ : xₙ ≠ []) : IsLeast {f | fp₁ p₁ xₙ f} (M'⟦~p₁*⟧ xₙ) := by
  constructor
  · simp [fp₁]
    nth_rw 1 [M'.iter_eq]
    simp [hxₙ]
  · intro g hg
    simp only [fp₁, Set.mem_setOf_eq] at hg; symm at hg
    intro α β
    simp [M', G, ωSum_nat_eq_ωSup]
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

-- TODO: remove α β for a more general statement
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem Q_empty (p₁ : RPol[F,N,𝒮]) (α β : Pk[F,N]) :
    Q⟦~p₁*⟧ [] α β = (ι p₁ ⊠ 𝒪 p₁)^* α β := by
  simp [Q, S, S.I]
  -- TODO: this should simp by it self
  rw [RPol.wnka_sem_pair]
  simp only [S, S.I, ι, Matrix.concrete_id, id_eq, 𝒪]
  rw [ι_wProd_𝒪, 𝒪_heart]
  simp [Matrix.mul_apply]

theorem fp₀_Q (p₁ : RPol[F,N,𝒮]) : IsLeast {f | fp₀ p₁ f} (Q⟦~p₁*⟧ []) := by
  have : Q⟦~p₁*⟧ [] = (ι p₁ ⊠  𝒪 p₁)^* := by
    ext α β
    rw [Q_empty]
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
    simp only [ωSup_le_iff, Chain.mk_apply]
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

theorem Q_empty_eq_M'_empty (p₁ : RPol[F,N,𝒮]) : Q⟦~p₁*⟧ [] = M'⟦~p₁*⟧ [] :=
  IsLeast.unique (fp₀_Q p₁) (fp₀_M' p₁)

variable [Inhabited Pk[F,N]]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_δ'_as_sum_unfolded {p : RPol[F,N,𝒮]} {xₙ} {l r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p, S p, 𝒮]]} :
      xδ (l + r) xₙ
    = xδ l xₙ +
      ∑ n ∈ Finset.range (xₙ.length - 1),
          xδ l (xₙ.take (n + 1))
        * r xₙ[n]! xₙ[n + 1]!
        * xδ (l + r) (xₙ.drop (n + 1)) := by
  induction xₙ using List.reverseRecOn with
  | nil => simp [xδ]
  | append_singleton xₙ α' ih =>
    clear ih
    rcases xₙ with _ | ⟨α₁, xₙ⟩
    · simp [xδ]
    induction xₙ generalizing α₁ with
    | nil => simp [xδ]
    | cons α₂ xₙ ih =>
      simp [xδ] at ih ⊢
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_δ'_as_sum {p : RPol[F,N,𝒮]} {xₙ} {α'} :
      xδ (δ.δ' p) (xₙ ++ [α'])
    = xδ (δ p) (xₙ ++ [α']) +
      ∑ n ∈ Finset.range xₙ.length,
          xδ (δ p) ((xₙ ++ [α']).take (n + 1))
        * (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p) xₙ[n]! (xₙ ++ [α'])[n + 1]!
        * xδ (δ p + (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p)) ((xₙ ++ [α']).drop (n + 1)) := by
  rw [δ.δ', xδ_δ'_as_sum_unfolded]
  simp
  sorry

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem xδ_δ'_as_sum' {p : RPol[F,N,𝒮]} {xₙ} {α'} :
      xδ (δ.δ' p) (xₙ ++ [α'])
    = xδ (δ p) (xₙ ++ [α']) +
      ∑ n ∈ Finset.range xₙ.length,
          xδ (δ p) ((xₙ ++ [α']).take (n + 1))
        * (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p) xₙ[n]! (xₙ ++ [α'])[n + 1]!
        * xδ (δ p + (𝒪 p ⊞ 𝒪_heart p ⊟ ι p ⊡ δ p)) ((xₙ ++ [α']).drop (n + 1)) := by
  sorry

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
@[simp]
theorem Matrix.smul_apply' (r : 𝒮) (A : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) (i j : Pk[F,N]) :
    (A <• r) i j = (A i j) •> r := rfl

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
theorem Finset.sum_smul' {X Y : Type} [DecidableEq X] [Fintype X] [DecidableEq Y] [Fintype Y] {ι : Type} [DecidableEq ι] (f : ι → 𝒮) (S : Finset ι) (r : 𝒲[X, Y, 𝒮]) :
    (∑ x ∈ S, f x) •> r = (∑ x ∈ S, f x •> r) := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all
    ext α β
    simp_all [add_mul, Finset.sum_mul, Matrix.sum_apply]

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
theorem Matrix.sum_smul' {X Y : Type} [DecidableEq X] [Fintype X] [DecidableEq Y] [Fintype Y] {ι : Type} [DecidableEq ι] (f : ι → 𝒲[X,Y,𝒮]) (S : Finset ι) (r : 𝒮) :
    (∑ x ∈ S, f x) <• r = (∑ x ∈ S, f x <• r) := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S ih =>
    simp_all

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
theorem one_mul_coe_unique_left {p₁ : RPol[F,N,𝒮]} {y : 𝒲[𝟙, S p₁, 𝒮]} :
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (fun _ ↦ 1 : 𝟙 → S.I {♡} → 𝒮) y.coe_unique_left = y := by
  ext
  simp [Matrix.mul_apply]

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
theorem ι_add_zero_mul {p₁ : RPol[F,N,𝒮]} {a b : 𝒲[𝟙, S p₁, 𝒮]} {c : 𝒲[S wnk_rpol {~p₁*}, S wnk_rpol {~p₁*}, 𝒮]} :
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (ι[a + b, 0] : 𝒲[𝟙, S p₁ ⊕ (↑{♡} : Set _), 𝒮]) c
    = Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul ι[a, 0] c + Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul ι[b, 0] c := by
  unfold S.ι
  simp
  ext
  simp [Matrix.mul_apply, right_distrib, Finset.sum_add_distrib]

omit [Inhabited Pk[F,N]] in
theorem fp₁_Q_is_fp_singleton (p₁ : RPol 𝒮) (α' : Pk[F,N]):
    Q wnk_rpol {~p₁*} [α'] = N'Q p₁ [α'] + Q p₁ [] * Q wnk_rpol {~p₁*} [α'] := by
  conv => left; unfold Q
  ext α β
  simp [RPol.wnka_sem_case, ι, 𝒪, δ, xδ]
  -- TODO: this should simp by it self
  rw [RPol.wnka_sem_case]
  simp [RPol.wnka_sem_case, ι, 𝒪, δ, xδ]
  rw [ι_wProd_δ, ι_wProd_𝒪, one_mul_coe_unique_left]
  simp
  nth_rw 1 [𝒪_heart]
  nth_rw 1 [box_star_iter]
  rw [add_sox]
  simp [Matrix.add_mul, fox, N'Q, N'Q_ij]
  congr
  · unfold Q
    simp only [RPol.wnka_sem_pair, ι, S.I, Matrix.concrete_id, id_eq, 𝒪]
    conv => right; arg 2; ext a b; rw [ι_wProd_𝒪]
    simp only [sox', Listed.array_sum_eq_finset_sum, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.down_sum, Matrix.down_mul_right, RPol.wnka_sem_case, xδ, mul_one,
      List.getLastD_eq_getLast?, List.getLast?_singleton, Option.getD_some, Matrix.zero_mul,
      smul_zero, Finset.sum_const_zero, Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, S.I,
      Finset.univ_unique, Set.default_coe_singleton, Pi.ofNat_apply, Matrix.up_apply, one_mul,
      Finset.sum_const, Finset.card_singleton, one_smul, zero_add]
    -- grind [zero_add, one_smul, one_mul, mul_one]
  · unfold Q
    simp [RPol.wnka_sem_case, ι, 𝒪, xδ, δ, sox']
    -- TODO: this should simp by it self
    conv => right; arg 2; ext α β; rw [RPol.wnka_sem_case]
    simp [RPol.wnka_sem_case, ι, 𝒪, xδ, δ, sox']
    conv => right; arg 2; ext s t; rw [ι_wProd_δ, ι_wProd_𝒪, one_mul_coe_unique_left]
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

theorem fp₁_Q_is_fp (p₁ : RPol 𝒮) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) :
    Q wnk_rpol {~p₁*} xₙ = N'Q p₁ xₙ + Q p₁ [] * Q wnk_rpol {~p₁*} xₙ := by
  induction xₙ using List.reverseRecOn with
  | nil => contradiction
  | append_singleton xₙ α' ih =>
    clear hxₙ ih
    rcases xₙ with _ | ⟨α₁, xₙ⟩
    · exact fp₁_Q_is_fp_singleton p₁ α'
    ext α β
    rw [Q]
    simp only [List.cons_append, RPol.wnka_sem_case, ι, S.I, Matrix.concrete_id, id_eq, xδ, δ, ←
      Matrix.mul_assoc, List.getLastD_eq_getLast?, List.getLast?_cons, List.getLast?_append,
      List.getLast?_nil, Option.getD_none, Option.some_or, Option.getD_some, 𝒪, Matrix.add_apply]
    rw [ι_wProd_δ, one_mul_coe_unique_left]
    simp only [Matrix.zero_mul, zero_add, Matrix.mul_zero, add_zero]
    nth_rw 1 [𝒪_heart, box_star_iter]
    simp [add_sox, fox, ι_add_zero_mul, Matrix.add_mul]
    rw [ι_add_zero_mul]
    simp [Matrix.add_mul]
    congr
    · simp [N'Q, N'Q_ij]
      rw [xδ_δ_iter, ι_wProd_δ, ι_wProd_𝒪]
      simp
      rw [← List.cons_append, xδ_δ'_as_sum]
      simp
      nth_rw 2 [Finset.sum_range_succ]
      simp [Matrix.mul_add, Matrix.add_mul, sox']
      nth_rw 3 [Matrix.mul_sum]
      simp [Matrix.sum_mul, Matrix.sum_apply]
      nth_rw 4 [add_comm]
      congr! 2 with n hn
      · unfold Q
        simp [RPol.wnka_sem_case, xδ, ι, 𝒪]
        conv => right; arg 2; ext α β; rw [RPol.wnka_sem_case]
        simp [RPol.wnka_sem_case, xδ, ι, 𝒪]
        have : List.take (xₙ.length + 1) (xₙ ++ [α']) = (xₙ ++ [α']) := by simp
        simp [this]; clear this
        conv => right; arg 2; ext α β; rw [ι_wProd_𝒪]
        rw [Matrix.mul_apply]
        have : Matrix.down (fun (x : 𝟙) ↦ (1 : S.I {♡} → 𝒮)) = 1 := rfl
        simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.down_sum, Matrix.down_mul_right, ←
          Matrix.mul_assoc, List.getLast?_cons, List.getLast?_append, List.getLast?_nil,
          Option.getD_none, Option.some_or, Option.getD_some, Matrix.zero_mul, smul_zero,
          Finset.sum_const_zero, zero_add, Matrix.down_mul, S.I, this, Matrix.down_up, one_mul]
      · unfold Q
        simp only [← Matrix.mul_assoc, Matrix.mul_sum, Matrix.mul_smul, Matrix.down_sum,
          Matrix.down_mul_right, RPol.wnka_sem_case, xδ, List.getLastD_eq_getLast?, ι, S.I, 𝒪,
          Matrix.mul_apply]
        generalize ι p₁ * δ p₁ α α₁ * xδ (δ p₁) (α₁ :: List.take n (xₙ ++ [α'])) = A
        simp at hn
        have : ¬xₙ.length + 1 ≤ n := by omega
        simp only [crox, List.length_cons, hn, getElem?_pos, Option.getD_some, List.length_append,
          List.length_nil, zero_add, Listed.array_sum_eq_finset_sum, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.down_sum, Finset.sum_mul, List.getLast?_cons, Matrix.concrete_id, id_eq,
          List.getLast?_drop, this, ↓reduceIte, List.getLast?_append, List.getLast?_nil,
          Option.getD_none, Option.some_or]
        rw [Finset.sum_comm]
        congr with γ
        simp [← Matrix.mul_assoc]
        nth_rw 1 [Matrix.mul_assoc]
        conv => left; arg 2; ext; rw [← Matrix.down_mul_right]
        rw [← Matrix.down_mul_right, ← Matrix.down_sum]
        congr
        simp only [Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.mul_sum]
        congr
        ext S _
        rw [Matrix.mul_apply]
        simp
        congr
        · grind
        have : ¬xₙ.length + 1 ≤ n := by omega
        simp [Matrix.down, xδ_δ_iter, ← Matrix.mul_assoc, ι_wProd_δ, ι_wProd_𝒪, this, sox']
        rw [xδ_δ_iter, ι_wProd_δ, ι_wProd_𝒪]
        simp [Matrix.down, xδ_δ_iter, ← Matrix.mul_assoc, ι_wProd_δ, ι_wProd_𝒪, this, sox']
        rw [one_mul_coe_unique_left]
        grind [List.head!_eq_head?, List.head?_drop, δ.δ']
    · rw [Matrix.mul_apply]
      simp [Q, RPol.wnka_sem_case, ι, 𝒪, List.getLast?_cons, xδ, δ, ← Matrix.mul_assoc, ι_wProd_δ]
      conv => right; arg 2; ext; rw [RPol.wnka_sem_case]
      simp [Q, RPol.wnka_sem_case, ι, 𝒪, List.getLast?_cons, xδ, δ, ← Matrix.mul_assoc, ι_wProd_δ]
      conv => right; arg 2; ext; rw [one_mul_coe_unique_left, ← Matrix.down_mul]
      simp [-Matrix.down_mul, ← Matrix.mul_assoc, ← Matrix.down_sum]
      simp [-Matrix.down_sum, ← Matrix.sum_mul]
      congr
      rw [mul_sox]
      nth_rw 1 [sox]
      ext _ γ
      simp only [S.ι, box, Listed.array_sum_eq_finset_sum, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.zero_apply, 𝒪_heart, Matrix.mul_apply, Finset.univ_unique,
        PUnit.default_eq_unit, Finset.sum_singleton]
      rcases γ with _ | γ
      · simp only [Sum.elim_inl]; rfl
      · grind [Sum.elim_inr, mul_zero, Finset.sum_const_zero]

theorem fp₁_Q_is_fp' (p₁ : RPol 𝒮) (h : Q p₁ = M'⟦~p₁⟧) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) (ih : ∀ (y : List Pk[F,N]), y.length < xₙ.length → y ≠ [] → M' wnk_rpol {~p₁*} y = Q wnk_rpol {~p₁*} y) :
    Q wnk_rpol {~p₁*} xₙ = M'⟦~p₁⟧ [] * Q wnk_rpol {~p₁*} xₙ + N' p₁ xₙ := by
  nth_rw 1 [fp₁_Q_is_fp _ _ hxₙ]
  rw [add_comm, h]
  congr
  have N'_eq_N'Q : N' p₁ xₙ = N'Q p₁ xₙ := by
    simp only [N', N'Q]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [N'_ij, N'Q_ij, h]
    grind [Q_empty_eq_M'_empty, List.drop_eq_nil_iff]
  rw [N'_eq_N'Q]

omit [Inhabited Pk[F,N]] in
theorem fp₁_M'_is_fp'' (p₁ : RPol 𝒮) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) :
    M' wnk_rpol {~p₁*} xₙ = (M'⟦~p₁⟧ [])^* * N' p₁ xₙ := by
  have ⟨h₁, h₂⟩ := fp₁_M' p₁ xₙ hxₙ
  simp [fp₁, lowerBounds] at h₁ h₂
  apply le_antisymm
  · apply h₂
    nth_rw 1 [← StarIter.star_iter]
    simp [add_mul, mul_assoc]
  · simp [LawfulStar.star_eq_sum, ← ωSum_mul_right]
    rw [ωSum_nat_eq_ωSup]
    simp
    intro i
    induction i with
    | zero => simp
    | succ i ih' =>
      simp [Finset.sum_range_succ']
      rw [h₁, add_comm]
      gcongr
      simp [pow_succ', Matrix.mul_assoc, ← Matrix.mul_sum]
      gcongr

def M_mul_add_P (M P : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
    ⟨⟨fun y ↦ M * y + P, by intro a b hab; simp; gcongr⟩, by simp [mul_ωSup, ωSup_add]; intro; rfl⟩
def M_star_mul_P (M P : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) : 𝒲[Pk[F,N], Pk[F,N], 𝒮] →𝒄 𝒲[Pk[F,N], Pk[F,N], 𝒮] :=
    ⟨⟨fun y ↦ M^* * P, by intro a b hab; simp⟩, by simp; intro; simp [Chain.map, OrderHom.comp, ωSup_const, Function.comp_def]⟩

-- theorem xδ_add {p₁ : RPol[F,N,𝒮]} {l r : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, S p₁, 𝒮]]} {x} {xs} :
--     xδ (l + r) (x::xs) = sorry := by
--   rcases xs with _ | ⟨y, xs⟩
--   · simp [xδ]
--   · rcases xs with _ | ⟨z, xs⟩
--     · simp [xδ]
--     · rcases xs with _ | ⟨w, xs⟩
--       · simp [xδ]
--       · rcases xs with _ | ⟨v, xs⟩
--         · simp [xδ]
--         · simp [xδ]

-- theorem asdhjasjdhas (p₁ : RPol[F,N,𝒮]) {xn} {α} {n m k : ℕ} (h : Q⟦~p₁⟧ = M'⟦~p₁⟧) (ξ : Pk[F,N]) :
--     ∑ i, (Q⟦~p₁⟧ [] ^ m) α i * Q⟦~p₁⟧ xn i ξ = Q⟦~p₁⟧ xn α ξ := by
--   induction m generalizing xn α ξ with
--   | zero =>
--     simp
--     rw [Finset.sum_eq_single α] <;> simp +contextual
--     sorry
--   | succ m ih =>
--     simp [pow_succ, Matrix.mul_apply]
--     simp [Finset.sum_mul, mul_assoc, ih]
--     simp [h, M']
--     induction p₁
--     all_goals simp [G]
--     next =>
--       simp [GS.mk]
--       clear ih
--       have : ∀ x, ∃ α, (α, [], α) = (x, xn, ξ) ↔ x = α ∧ [] = xn ∧ α = ξ := by simp [eq_comm]
--       simp [this]
--       rw [Finset.sum_eq_single ξ]
--       · simp_all
--         split_ifs
--         · simp_all
--         · simp_all
--           clear ih
--           sorry
--         · simp_all
--           sorry
--         · simp_all
--         · simp_all
--           sorry
--         · simp_all
--       · simp; grind
--       · simp
--     next =>
--       simp [GS.mk]
--       simp_all
--       sorry

--     induction xn with
--     | nil =>
--       simp
--       sorry
--     | cons γ xn ih =>
--       simp [G]
--       sorry

-- @[simp]
theorem ashdjashdj (p₁ : RPol[F,N,𝒮]) {m} {α β} {xn} :
    ((fun α β ↦ G⟦~p₁⟧ (α, xn, β)) ^ m) α β = G⟦~p₁⟧ (α, xn, β) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ']
-- @[simp]
theorem ashdjashdj' (p₁ : RPol[F,N,𝒮]) {m} {α β} {xn} :
    (M'⟦~p₁⟧ xn ^ m) α β = (G⟦~p₁⟧ ♢ ·)^[m] G⟦skip⟧ ⟨α, xn.rep m, β⟩ := by
  unfold M'
  induction m generalizing α β with
  | zero =>
    simp [M', G, GS.mk]
    if α = β then
      subst_eqs; simp_all [GS.mk]
    else
      simp_all [GS.mk]
      grind
  | succ m ih =>
    simp only [pow_succ', Matrix.mul_apply, Function.iterate_succ', Function.comp_apply,
      List.repeat_succ]
    -- simp [ih]
    simp [G.concat_apply, GS.splitAtJoined]
    rw [add_assoc]
    rw [Finset.sum_range_add]
    simp

    simp [G, M']
    sorry


def RPol.A_sem (p : RPol[F,N,𝒮]) := p.wnka.sem
syntax "𝒜⟦" cwnk_rpol "⟧" : term
macro_rules | `(𝒜⟦$p⟧) => `(RPol.A_sem wnk_rpol { $p })
open Lean Elab PrettyPrinter Delaborator Meta Command Term in
@[app_unexpander RPol.A_sem]
def 𝒜.unexpander : Unexpander
| `($_ $y) => do
  let y ← match y with
    | `(wnk_rpol{$y}) => pure y
    | y => `(cwnk_rpol|~$y)
  `(𝒜⟦$y⟧)
| _ => throw ()


omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [∀ (n : ℕ), LawfulStar N𝒲[n, n, 𝒮]] [Inhabited Pk[F,N]] in
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem RPol.A_sem_eq (p : RPol[F,N,𝒮]) : 𝒜⟦~p⟧ = p.wnka.sem := rfl

theorem RPol.Q_eq_A_sem (p : RPol[F,N,𝒮]) {xs} : Q⟦~p⟧ xs = fun x z ↦ 𝒜⟦~p⟧ ⟨x, xs, z⟩ := by
  ext
  simp [Q, A_sem]

theorem RPol.A_sem_eq_G (p : RPol[F,N,𝒮]) (h : Q⟦~p⟧ = M'⟦~p⟧) : 𝒜⟦~p⟧ = G⟦~p⟧ := by
  ext ⟨α, xs, β⟩
  have := congrFun₂ (congrFun h xs) α β
  exact this

theorem Q_star_eq_ωSum_Q_iter (p₁ : RPol[F,N,𝒮]) (h : Q⟦~p₁⟧ = M'⟦~p₁⟧) : Q⟦~p₁*⟧ = ω∑ (i : ℕ), Q⟦~p₁⟧^i := by
  funext xₙ α β

  -- TODO: require that xₘ is nonempty
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  simp [Q]
  rw [RPol.wnka_sem_case]
  simp [ι, 𝒪]
  rw [xδ_δ_iter]
  simp
  rw [ι_wProd_δ, ι_wProd_𝒪]
  simp
  have : ∀ (x : 𝒲[S.I {♡}, S p₁, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p₁, 𝒮] 𝒲[𝟙, S p₁, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  simp [δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq : 𝒪_heart p₁ = ω∑ (m : ℕ), (Q⟦~p₁⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr!
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · replace 𝒪_heart_eq := congrFun₂ 𝒪_heart_eq α β
    simp at 𝒪_heart_eq
    simp [Matrix.coe_unique_left, Q, Matrix.down, ← 𝒪_heart_eq]
    simp [Matrix.mul_apply]
  · simp
    simp [crox]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
    calc
      _ = ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀ * xδ (δ p₁) (α₀ :: xₙ) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₀ :: xₙ).getLast?.getD α) β).down +
            ∑ x ∈ Finset.range xₙ.length,
              ∑ x_1,
                ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀ * xδ (δ p₁) (α₀ :: List.take x xₙ) * 𝒪 p₁ ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                        Q⟦~p₁*⟧ (List.drop x xₙ) x_1 β := by
        rcases xₙ with _ | ⟨α₁, xₙ⟩
        · simp
        simp only [List.getLast?_cons_cons, List.length_cons]
        congr! with i hi γ hγ
        nth_rw 2 [Matrix.mul_assoc]
        nth_rw 1 [Matrix.mul_assoc]
        simp
        congr
        simp [Q]
        rw [RPol.wnka_sem_case]
        simp
        simp [ι, 𝒪]
        rw [xδ_δ_iter]
        simp
        rw [ι_wProd_δ, ι_wProd_𝒪]
        simp
        have : ∀ (x : 𝒲[S.I {♡}, S p₁, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p₁, 𝒮] 𝒲[𝟙, S p₁, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
        simp [this]
        simp at hi
        split_ifs with hi'
        · omega
        · simp [δ.δ', List.head!_eq_head?, Option.getD_default_eq_iget, List.getLast?_drop, hi, hi', List.getLast?_cons]
      _ = ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀ * xδ (δ p₁) (α₀ :: xₙ) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₀ :: xₙ).getLast?.getD α) β).down +
            ∑ i ∈ Finset.range xₙ.length,
              ∑ γ,
                (𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ.take i)) α γ *
                        Q⟦~p₁*⟧ (List.drop i xₙ) γ β := by
        congr! with i hi γ hγ
        simp only [Finset.mem_range] at hi
        nth_rw 1 [Matrix.mul_apply]
        simp [Q, sox, Matrix.sum_mul]
        congr! with ξ hξ
        simp [RPol.wnka_sem_case]
        simp [xδ, fox, ← Matrix.mul_assoc]
        congr! 3
        rcases i with _ | i
        · simp [List.getLast?_cons]
        · have : i < xₙ.length := by omega
          simp [List.getLast?_cons, List.getLast?_take, this]
      _ = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ) * 𝒪_heart p₁) α β +
            ∑ i ∈ Finset.range xₙ.length, ∑ γ,
                (𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ.take i)) α γ * Q⟦~p₁*⟧ (List.drop i xₙ) γ β := by
        congr! with i hi γ hγ
        nth_rw 2 [Matrix.mul_assoc]
        nth_rw 1 [Matrix.mul_apply]
        conv => right; arg 2; ext; rw [Matrix.mul_apply]
        simp [Q, sox, sox', Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum, Matrix.mul_assoc, mul_assoc]
        rw [Finset.sum_comm]
        congr! 4 with γ hγ ξ hξ
        simp [RPol.wnka_sem_case]
        simp [xδ, fox, ← Matrix.mul_assoc]
        congr! 3
      _ = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ) * 𝒪_heart p₁) α β +
            ∑ i ∈ Finset.range xₙ.length,
                ((𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ.take i)) * Q⟦~p₁*⟧ (List.drop i xₙ)) α β := by
        simp [Matrix.mul_apply]
      _ = ∑ i ∈ Finset.range (xₙ.length + 1), ((𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ.take i)) * Q⟦~p₁*⟧ (List.drop i xₙ)) α β := by
        simp [Finset.sum_range_succ]
        rw [add_comm]
        congr!
        ext
        simp [Q]
        rw [RPol.wnka_sem_case]
        simp [ι, xδ, 𝒪]
        rw [ι_wProd_𝒪]
        simp [Matrix.down, Matrix.mul_apply]
      _ = ∑ i ∈ Finset.range (xₙ.length + 1), ((𝒪_heart p₁ * Q⟦~p₁⟧ (α₀ :: xₙ.take i)) * (ω∑ (n : ℕ), Q⟦~p₁⟧^n) (List.drop i xₙ)) α β := by
        simp [Matrix.mul_apply]
        congr! 3
        rw [ihₙ _ (by simp; omega)]
        simp
      _ = ω∑ (n : ℕ), ω∑ (m : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), (Q⟦~p₁⟧ [] ^ m * Q⟦~p₁⟧ (α₀ :: List.take k xₙ) * Q⟦~p₁⟧ (List.drop k xₙ) ^ n) α β := by
        simp [← ωSum_mul_left, ωSum_sum_comm]
        simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
      _ = ω∑ (n : ℕ), ω∑ (m : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, ((Q⟦~p₁⟧ [] ^ m) α γ * Q⟦~p₁⟧ (α₀ :: List.take k xₙ) γ ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
        simp [Matrix.mul_apply]
        simp [← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply, Matrix.mul_assoc]
      -- _ = ω∑ (n : ℕ) (m : ℕ), ∑ x ∈ Finset.range (xₙ.length + 1), ∑ x_1, ∑ x_2, G⟦~(p₁.iter m)⟧ (α, [], x_2) * G⟦~p₁⟧ (x_2, α₀ :: List.take x xₙ, x_1) * G⟦~(p₁.iter n)⟧ (x_1, List.drop x xₙ, β) := by
      --   simp [h]
      --   simp [M']
      -- _ = ω∑ (n : ℕ), ω∑ (m : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      --   simp [← Finset.sum_mul]
      --   congr! with n m k hk ξ hξ
      --   · sorry
      --   · sorry
      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      --   sorry
      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, /- -/ ((∑ γ, ω∑ (m : ℕ), (Q⟦~p₁⟧ [] ^ m) α γ * Q⟦~p₁⟧ (α₀ :: List.take k xₙ) γ ξ) /- -/ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      --   sorry
      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, /- -/ ((Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ)                                  /- -/ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      --   -- congr!
      --   sorry

      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) * Q⟦~p₁⟧ (List.drop k xₙ) ^ n) α β := by
      --   -- simp [← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply]
      --   sorry
      --   simp [h]
      --   unfold M'
      --   simp
      --   sorry
        -- simp [← ωSum_mul_left, ωSum_sum_comm]
        -- simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
      _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1 + 1), ∑ ξ, (Q⟦~p₁⟧ (List.take k (α₀ :: xₙ)) α ξ * (Q⟦~p₁⟧ (List.drop k (α₀ :: xₙ)) ^ n) ξ β) := by
        -- simp [h]
        -- simp [M']
        conv =>
          right
          arg 1; ext n
          rw [Finset.sum_range_succ']
        simp
        conv =>
          left
          arg 1; ext n
          arg 1; ext m
          arg 2; ext m
          rw [Finset.sum_comm]
        conv =>
          left
          arg 1; ext n
          arg 1; ext m
          rw [Finset.sum_comm]

        simp [mul_assoc, ← Finset.mul_sum]
        sorry
      -- _ = ω∑ (n : ℕ) (m : ℕ), ∑ x, G⟦~(p₁.iter m)⟧ (α, [], x) * ∑ i ∈ Finset.range (xₙ.length + 1), ∑ i_1, G⟦~p₁⟧ (x, α₀ :: List.take i xₙ, i_1) * G⟦~(p₁.iter n)⟧ (i_1, List.drop i xₙ, β) := by
      --   simp [h]
      --   simp [M']
      --   have : ∀ n x,
      --         ∑ i ∈ Finset.range (xₙ.length + 1 + 1), ∑ i_1, G⟦~p₁⟧ (x, List.take i (α₀ :: xₙ), i_1) * G⟦~(p₁.iter n)⟧ (i_1, List.drop i (α₀ :: xₙ), β)
      --       = G⟦~p₁ ; ~(p₁.iter n)⟧ (x, α₀ :: xₙ, β) := by
      --     intro n x
      --     simp [G]
      --     simp [G.concat_apply, GS.splitAtJoined]
      --     -- nth_rw 2 [Finset.sum_range_succ']
      --     -- simp
      --     -- sorry
      --   conv at this =>
      --     ext n x
      --     rw [Finset.sum_range_succ']
      --   simp at this
      --   sorry
      _ = ω∑ (n : ℕ), (Q⟦~p₁⟧ (α₀ :: xₙ) ^ n) α β := by
        have : ∀ n, (Q⟦~p₁⟧ (α₀ :: xₙ) ^ n) = sorry := by
          sorry
        nth_rw 2 [ωSum_nat_eq_succ]
        simp [pow_succ', Matrix.mul_apply]
        simp [ωSum_sum_comm, ωSum_mul_left]
        rw [Finset.sum_range_succ']
        simp

        -- simp [h]
        -- simp [M']
        -- nth_rw 2 [ωSum_nat_eq_succ]


        -- simp
        -- have : G⟦skip⟧ (α, α₀ :: xₙ, β) = (0 : 𝒮) := by simp [G, GS.mk]; grind
        -- simp [this]
        -- simp [G, G.concat_apply, GS.splitAtJoined]

  -- induction xₙ using List.reverseRecOn with
  -- | nil =>
  --   simp [h, LawfulStar.star_eq_sum]
  --   sorry
  -- | append_singleton xₙ α' ih =>
  --   simp [Q]
  --   rw [RPol.wnka_sem_case]
  --   simp [ι, 𝒪]
  --   rw [xδ_δ_iter]
  --   simp
  --   rw [ι_wProd_δ, ι_wProd_𝒪]
  --   simp
  --   have : ∀ (x : 𝒲[S.I {♡}, S p₁, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p₁, 𝒮] 𝒲[𝟙, S p₁, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  --   simp [this]
  --   simp [δ.δ']
  --   rw [xδ_δ'_as_sum_unfolded]
  --   conv =>
  --     left
  --     arg 1
  --     arg 1
  --     arg 2
  --     arg 2
  --     arg 2;
  --     rw [xδ_δ'_as_sum_unfolded]

  --   sorry
    -- rcases xₙ with _ | ⟨α₁, xₙ⟩
    -- · sorry
    -- calc
    --     Q⟦~p₁*⟧ (α₁ :: xₙ ++ [α']) α β
    --   = ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ * xδ (δ.δ' p₁) (α₁ :: (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) α' β).down := by
    --       simp [Q]
    --       rw [RPol.wnka_sem_case]
    --       simp
    --       simp [ι, 𝒪]
    --       rw [xδ_δ_iter]
    --       simp
    --       rw [ι_wProd_δ, ι_wProd_𝒪]
    --       simp [List.getLast?_cons]
    --       have : ∀ (x : 𝒲[S.I {♡}, S p₁, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p₁, 𝒮] 𝒲[𝟙, S p₁, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
    --       simp [this]
    --   _ = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₁ :: (xₙ ++ [α'])) * 𝒪_heart p₁) α β +
    --         ∑ x ∈ Finset.range (xₙ.length + 1),
    --           ∑ x_1,
    --             ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ * xδ (δ p₁) (α₁ :: List.take x (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₁ :: xₙ)[x]?.getD default) x_1 *
    --                     (ι p₁ ⊡ δ p₁) x_1 ((xₙ ++ [α'])[x]?.getD default) *
    --                   xδ (δ p₁ + ((𝒪 p₁ ⊟' 𝒪_heart p₁) ⊞ ι p₁ ⊡ δ p₁)) (List.drop x (xₙ ++ [α'])) *
    --                 (𝒪 p₁ ⊟' 𝒪_heart p₁) α' β).down := by
    --       rw [← List.cons_append, xδ_δ'_as_sum]
    --       -- TEST
    --       conv =>
    --         left
    --         arg 1
    --         arg 1
    --         arg 2
    --         arg 2
    --         arg 2; ext
    --         rw [xδ_δ'_as_sum_unfolded]
    --       simp
    --       simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
    --       -- TEST
    --       simp
    --       simp [Matrix.mul_add, Matrix.add_mul]
    --       have : ∀ α₁ xₙ α',
    --             ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ * xδ (δ p₁) (α₁ :: (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) α' β)
    --           = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₁ :: (xₙ ++ [α'])) * 𝒪_heart p₁) α β := by
    --         intro α₁ xₙ α'
    --         ext
    --         nth_rw 2 [Matrix.mul_apply]
    --         conv =>
    --           right
    --           arg 1; arg 2; ext
    --           rw [Matrix.mul_apply]
    --         simp [Q, sox, sox', Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul]
    --         congr! 2
    --         rw [RPol.wnka_sem_case]
    --         simp [List.getLast?_cons, Matrix.down]
    --         rw [xδ]
    --         simp [← Matrix.mul_assoc, fox]
    --       simp [this]; clear this
    --       simp [Matrix.mul_sum]
    --       simp [← Matrix.mul_assoc]
    --       -- simp [sox]
    --       have : (𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) = ((𝒪 p₁ ⊟' 𝒪_heart p₁) ⊞ (ι p₁ ⊡ δ p₁)) := by
    --         ext; simp only [crox, sox, HSMul.hSMul, SMul.smul, Listed.array_sum_eq_finset_sum,
    --           Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_apply, Finset.univ_unique,
    --           PUnit.default_eq_unit, ← mul_assoc, Finset.sum_singleton, sox', MulOpposite.unop_op,
    --           Matrix.sum_mul]; rw [Finset.sum_comm]
    --       simp [this]; clear this
    --       simp [crox]
    --       simp [Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
    --   _ = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₁ :: (xₙ ++ [α'])) * 𝒪_heart p₁) α β +
    --         ∑ x ∈ Finset.range (xₙ.length + 1),
    --           ∑ x_1,
    --             (((𝒪_heart p₁ * Q⟦~p₁⟧ (α₁ :: List.take x (xₙ ++ [α'])) * 𝒪_heart p₁) α x_1 : 𝒲[𝟙, 𝟙, 𝒮]) *
    --                     ((ι p₁ ⊡ δ p₁) x_1 (xₙ[x]?.getD α') *
    --                   xδ (δ p₁ + ((𝒪 p₁ ⊟' 𝒪_heart p₁) ⊞ ι p₁ ⊡ δ p₁)) (List.drop x (xₙ ++ [α'])) *
    --                 (𝒪 p₁ ⊟' 𝒪_heart p₁) α' β)).down := by
    --       simp [← Matrix.mul_assoc, ← mul_assoc]
    --       congr! 8 with i h
    --       ·
    --         ext
    --         nth_rw 2 [Matrix.mul_apply]
    --         conv =>
    --           right
    --           arg 1; arg 2; ext
    --           rw [Matrix.mul_apply]
    --         simp [Q, sox, sox', Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul]
    --         congr! 2
    --         rw [RPol.wnka_sem_case]
    --         simp [List.getLast?_cons, Matrix.down]
    --         rw [xδ]
    --         simp [← Matrix.mul_assoc, fox]
    --         congr! 4
    --         rcases i with _ | i
    --         · simp at h
    --           simp
    --         · simp at h
    --           simp [h, List.getLast?_take, List.getElem?_append]
    --       · simp at h
    --         simp [List.getElem_append, h]
    --         split_ifs with h' <;> simp [h']
    --   _ = (ω∑ (i : ℕ), Q⟦~p₁⟧ ^ i) (α₁ :: xₙ ++ [α']) α β := by
    --       have : ∀ i α₀,
    --             (ι p₁ ⊡ δ p₁) α₀ (xₙ[i]?.getD α') * xδ (δ p₁ + ((𝒪 p₁ ⊟' 𝒪_heart p₁) ⊞ ι p₁ ⊡ δ p₁)) (List.drop i (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) α' β
    --           = (Q⟦~p₁⟧ (List.drop i (xₙ ++ [α'])) * 𝒪_heart p₁) α' β := by
    --         intro i α₀
    --         ext ⟨_⟩ ⟨_⟩
    --         rw [xδ_δ'_as_sum_unfolded]
    --         simp

    --         nth_rw 2 [Matrix.mul_apply]
    --         -- conv =>
    --         --   right
    --         --   arg 1; arg 2; ext
    --         --   rw [Matrix.mul_apply]
    --         simp [Q, sox, sox', Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul]
    --         congr! 2
    --         rw [RPol.wnka_sem_case]
    --         simp [List.getLast?_cons, Matrix.down]
    --         rw [xδ]
    --         simp [← Matrix.mul_assoc, fox]
    --         congr! 4
    --         rcases i with _ | i
    --         · simp at h
    --           simp
    --         · simp at h
    --           simp [h, List.getLast?_take, List.getElem?_append]
    --       · simp at h
    --         simp [List.getElem_append, h]
    --         split_ifs with h' <;> simp [h']


    --       simp [this]

    --       -- have : ∀ {α α₁ x xₙ α' β},
    --       --       (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ * xδ (δ p₁) (α₁ :: List.take x (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₁ :: xₙ)[x]?.getD default) x_1
    --       --       (𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₁ * xδ (δ p₁) (α₁ :: List.take x (xₙ ++ [α'])) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₁ :: xₙ)[x]?.getD defauly) x_1
    --       --     = (𝒪_heart p₁ * Q⟦~p₁⟧ (α₁ :: List.take x (xₙ ++ [α'])) * 𝒪_heart p₁) α x_1 := by
    --       --   intro α α₁ x xₙ α' β
    --       --   ext
    --       --   nth_rw 2 [Matrix.mul_apply]
    --       --   conv =>
    --       --     right
    --       --     arg 1; arg 2; ext
    --       --     rw [Matrix.mul_apply]
    --       --   simp [Q, sox, sox', Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul]
    --       --   congr! 2
    --       --   rw [RPol.wnka_sem_case]
    --       --   simp [List.getLast?_cons, Matrix.down]
    --       --   rw [xδ]
    --       --   simp [← Matrix.mul_assoc, fox]
    --       --   simp only [List.getLast?_take]
    --       --   congr! 4
    --       --   rcases x with _ | x
    --       --   · simp
    --       --   · simp
    --       --     sorry
    --       --   -- · simp at ⊢
    --       --   --   simp [List.getElem?_append, h]
    --       --   --   split)ifs

    --       -- simp [this]
    --       -- simp [← mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_sum]

    --       sorry

theorem Q_star_eq_star_Q (p₁ : RPol[F,N,𝒮]) (h : Q⟦~p₁⟧ = M'⟦~p₁⟧) {xₙ} : Q⟦~p₁*⟧ xₙ = (Q⟦~p₁⟧ xₙ)^* := by
  rw [Q_star_eq_ωSum_Q_iter _ h]; simp [LawfulStar.star_eq_sum]

theorem fp₁_Q_is_fp'' (p₁ : RPol 𝒮) (h : Q p₁ = M'⟦~p₁⟧) (xₙ : List Pk[F,N]) (hxₙ : xₙ ≠ []) (ih : ∀ (y : List Pk[F,N]), y.length < xₙ.length → y ≠ [] → M' wnk_rpol {~p₁*} y = Q wnk_rpol {~p₁*} y) :
    Q wnk_rpol {~p₁*} xₙ = (M'⟦~p₁⟧ [])^* * N' p₁ xₙ := by
  rw [Q_star_eq_star_Q _ h, h]
  rw [← fp₁_M'_is_fp'' _ _ hxₙ]
  ext α β
  simp [M', G, LawfulStar.star_eq_sum]
  congr with n
  induction n generalizing α β with
  | zero =>
    simp [G]
    if α = β then
      subst_eqs; simp [GS.mk, hxₙ, Prod.eq_iff_fst_eq_snd_eq]
      sorry
    else
      simp_all [GS.mk, hxₙ, Prod.eq_iff_fst_eq_snd_eq]
      sorry
  | succ n ih =>
    simp [G, pow_succ]
    sorry
  -- ComputableSemiring.unique_star _ _ _ (fp₁_Q_is_fp' p₁ h xₙ hxₙ ih).symm

theorem M'_eq_Q (p₁ : RPol[F,N,𝒮]) (ih : p₁.wnka.sem = G p₁) : M'⟦~p₁*⟧ = Q⟦~p₁*⟧ := by
  funext xₙ
  induction xₙ using Nat.strongRecMeasure List.length; next xₙ ihₙ =>
  induction xₙ with
  | nil => exact IsLeast.unique (fp₀_M' p₁) (fp₀_Q p₁)
  | cons α₀ xₙ ih₀ =>
    clear ih₀
    rw [fp₁_M'_is_fp'' p₁ (α₀ :: xₙ) (by simp)]
    have ih' : Q p₁ = M'⟦~p₁⟧ := by ext x α αb; simp [Q]; rw [ih]; rfl
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

theorem the_complete_theorem (p : Pol[F,N,𝒮]) (π) (h) :
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

-- /--
-- info: 'WeightedNetKAT.the_complete_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms the_complete_theorem

end WeightedNetKAT
