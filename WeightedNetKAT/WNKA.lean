import Batteries.Data.Array.Pairwise
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.List.DropRight
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Order.ScottTopology
import WeightedNetKAT.ComputableSemiring
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Language
import WeightedNetKAT.ListExt
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.MatrixStar
import WeightedNetKAT.Star

open OmegaCompletePartialOrder
open scoped RightActions

open WeightingNotation

namespace WeightedNetKAT

variable {F : Type} [Listed F]
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

notation "♡" => Sum.inl ()
notation "♣" => Sum.inr ()

abbrev S : RPol[F,N,𝒮] → Type
  | wnk_rpol {drop} => 𝟙
  | wnk_rpol {skip} => 𝟙
  | wnk_rpol {@test ~_} => 𝟙
  | wnk_rpol {@mod ~_} => 𝟙
  | wnk_rpol {dup} => 𝟙 ⊕ 𝟙
  | wnk_rpol {~_ ⨀ ~p₁} => S p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁ ; ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁*} => S p₁ ⊕ 𝟙

abbrev S.decidableEq (p : RPol[F,N,𝒮]) : DecidableEq (S p) :=
  match p with
  | wnk_rpol {drop} => inferInstanceAs <| DecidableEq 𝟙
  | wnk_rpol {skip} => inferInstanceAs <| DecidableEq 𝟙
  | wnk_rpol {@test ~_}
  | wnk_rpol {@mod ~_} => inferInstanceAs <| DecidableEq 𝟙
  | wnk_rpol {dup} => inferInstanceAs <| DecidableEq (𝟙 ⊕ 𝟙)
  | wnk_rpol {~_ ⨀ ~p₁} => S.decidableEq p₁
  | wnk_rpol {~p₁ ⨁ ~p₂}
  | wnk_rpol {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_rpol {~p₁*} =>
    letI := S.decidableEq p₁
    instDecidableEqSum

instance : Unique (Fin (Listed.size 𝟙)) where
  uniq := by intro ⟨a, ha⟩; have : Listed.size 𝟙 = 1 := rfl; grind

instance S.instDecidableEq (p : RPol[F,N,𝒮]) : DecidableEq (S p) := S.decidableEq p

def S.ι {X Y : Type} : (Matrix 𝟙 X 𝒮) → (Matrix 𝟙 Y 𝒮) → (Matrix 𝟙 (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "ι[" a "," b"]" => S.ι a b

def S.𝒪 {X Y : Type} : (Matrix X 𝟙 𝒮) → (Matrix Y 𝟙 𝒮) → (Matrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "𝒪[" a "," b"]" => S.𝒪 a b

section delta

variable {X Y Z W : Type*}

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

notation "δ[" "[" a ", " b "]" ", " "[" c ", " d "]" "]" => S.δ a b c d

end delta

@[reducible]
instance S.fintype (p : RPol[F,N,𝒮]) : Fintype (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    inferInstanceAs (Fintype 𝟙)
  | wnk_rpol {dup} => inferInstanceAs (Fintype (𝟙 ⊕ 𝟙))
  | wnk_rpol {~_ ⨀ ~p₁} => S.fintype p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁*} => letI := S.fintype p₁; instFintypeSum _ _
instance S.Finite {p : RPol[F,N,𝒮]} : Finite (S p) := Finite.of_fintype (S p)

instance S.listed (p : RPol[F,N,𝒮]) : Listed (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    inferInstanceAs (Listed 𝟙)
  | wnk_rpol {dup} => inferInstanceAs (Listed (𝟙 ⊕ 𝟙))
  | wnk_rpol {~_ ⨀ ~p₁} => S.listed p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.listed p₁; letI := S.listed p₂; Listed.instSum
  | wnk_rpol {~p₁*} => letI := S.listed p₁; Listed.instSum

abbrev η₁ {X : Type} [DecidableEq X] (i : X) : X → 𝒮 :=
  fun i' ↦ if i = i' then 1 else 0
abbrev η₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] (i : X) (j : Y) : Matrix X Y 𝒮 :=
  fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def ι (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η₂ () ()
  | wnk_rpol {dup} => η₂ () ♡
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~_} => ι[ι p₁, 0]
  | wnk_rpol {~_*} => ι[0, fun () ↦ 1]

def 𝒞.transpose {X Y : Type} (m : (X × Y) →₀ 𝒮) : (Y × X) →₀ 𝒮 :=
  ⟨(m.support.map ⟨fun (y, x) ↦ (x, y), by grind⟩), (fun (y, x) ↦ m (x, y)), (by simp)⟩

variable [Star 𝒮]

section

variable {Pk : Type*} [Fintype Pk]

def box {X} [Fintype X] {Q : Type*} [Mul Q] [AddCommMonoid Q] {Z : Type*} [Fintype Z] [Unique Z]
    (l : 𝒲[Z, X, Q]) (r : 𝒲[Pk, Pk, 𝒲[X, Z, Q]]) :
    𝒲[Pk,Pk,Q] :=
  fun α β ↦ (l * r α β).down

infixr:50 " ⊠ " => box

def fox {A B C : Type*} {Q : Type*} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B] [Fintype C]
    (l : 𝒲[A, B, Q]) (r : 𝒲[Pk, Pk, 𝒲[B, C, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, C, Q]] :=
  fun α β ↦ l * r α β

infixr:50 " ⊡ " => fox

def sox {A B : Type*} {Q : Type*} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B]
    (l : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, B, Q]] :=
  fun α β ↦ ∑ m, l α m •> r m β

infixr:50 " ⊟ " => sox

def sox' {A B : Type*} {Q : Type*} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B]
    (l : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) (r : 𝒲[Pk, Pk, Q]) :
    𝒲[Pk, Pk, 𝒲[A, B, Q]] :=
  fun α β ↦ ∑ m, l α m <• r m β

infixr:50 " ⊟' " => sox'

def crox {A B C : Type*} {Q : Type*} [AddCommMonoid Q] [Mul Q]
    [Fintype A] [Fintype B] [DecidableEq C] [Fintype C]
    (l : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) (r : 𝒲[Pk, Pk, 𝒲[B, C, Q]]) :
    𝒲[Pk, Pk, 𝒲[A, C, Q]] :=
  fun α β ↦ ∑ m, l α m * r m β

infixr:50 " ⊞ " => crox

@[simp]
theorem Listed.array_sum_eq_finset_sum {α ι : Type*} [Listed ι] [Fintype ι] [AddCommMonoid α] (f : ι → α) :
    (Listed.array.map f).sum = ∑ x, f x := by
  classical
  rw [← Array.sum_toList]
  simp [← List.sum_toFinset (f:=f) Listed.nodup, Fintype.sum_subset]

theorem add_sox {A B : Type*} {Q : Type*} [NonUnitalSemiring Q]
    [Fintype A] [Fintype B]
    (l l' : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((l + l') ⊟ r) = (l ⊟ r) + (l' ⊟ r) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, add_mul, Finset.sum_add_distrib]

theorem mul_sox {A B : Type*} {Q : Type*} [NonUnitalSemiring Q]
    [Fintype A] [Fintype B]
    (l l' : 𝒲[Pk, Pk, Q]) (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((l * l') ⊟ r) = (l ⊟ (l' ⊟ r)) := by
  ext α β a b
  simp [sox]
  simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

variable [DecidableEq Pk]

@[simp]
theorem one_sox {A B : Type*} {Q : Type*} [Semiring Q]
    [Fintype A] [Fintype B]
    (r : 𝒲[Pk, Pk, 𝒲[A, B, Q]]) :
    ((1 : 𝒲[Pk, Pk, Q]) ⊟ r) = r := by
  ext α β a b
  simp [sox, Matrix.one_apply]

end

-- NOTE: computable star
noncomputable section

variable [DecidableEq N] [DecidableEq F]

mutual

def 𝒪_heart (p₁ : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] 𝒮 := (ι p₁ ⊠ 𝒪 p₁)^*

def 𝒪 (p : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p) 𝟙 𝒮) := fun α β ↦
  match p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} => if α = β then fun _ ↦ 1 else 0
  | wnk_rpol {@test ~γ} => if α = β ∧ β = γ then fun _ ↦ 1 else 0
  | wnk_rpol {@mod ~π} => if β = π then fun _ ↦ 1 else 0
  | wnk_rpol {dup} => if α = β then η₂ ♣ () else 0
  | wnk_rpol {~_ ⨀ ~p₁} => 𝒪 p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} => 𝒪[𝒪 p₁ α β, 𝒪 p₂ α β]
  | wnk_rpol {~p₁ ; ~p₂} => 𝒪[∑ γ, (𝒪 p₁ α γ * ι p₂ * 𝒪 p₂ γ β), 𝒪 p₂ α β]
  | wnk_rpol {~p₁*} =>
    𝒪[
      (𝒪 p₁ ⊟' 𝒪_heart p₁) α β,
      𝒪_heart p₁ α β
    ]

end

def δ (p : RPol[F,N,𝒮]) : 𝒲[Pk[F,N],Pk[F,N],𝒲[S p,S p,𝒮]] := fun α β ↦
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    0
  | wnk_rpol {dup} => fun s ↦ if s = ♡ ∧ α = β then η₁ ♣ else 0
  | wnk_rpol {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
      δ[[δ p₁ α β,    0],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁ ; ~p₂} =>
      δ[[δ p₁ α β,    ∑ γ, (𝒪 p₁ α γ * ι p₂ * δ p₂ γ β)],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁*} =>
    δ[[δ' p₁ α β, 0],
      [(𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α β, 0]]
where δ' (p₁ : RPol[F,N,𝒮]) : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p₁, S p₁, 𝒮]] := δ p₁ + (𝒪 p₁ ⊞ 𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁)

def 𝒪_heart_n (p₁ : RPol[F,N,𝒮]) (n : ℕ) : Matrix Pk[F,N] Pk[F,N] 𝒮 :=
  ∑ i ∈ Finset.range n, (ι p₁ ⊠ 𝒪 p₁)^i

def approx_ι (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p ⊕ 𝟙) 𝒮 :=
  ι[0, fun () ↦ 1]
def approx_𝒪 (p : RPol[F,N,𝒮]) (n : ℕ) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p ⊕ 𝟙) 𝟙 𝒮) := fun α β ↦
    𝒪[
      (𝒪 p ⊟' 𝒪_heart_n p n) α β,
      𝒪_heart_n p n α β
    ]
def approx_δ (p : RPol[F,N,𝒮]) (n : ℕ) : 𝒲[Pk[F,N],Pk[F,N],𝒲[S p ⊕ 𝟙,S p ⊕ 𝟙,𝒮]] := fun α β ↦
  δ[[δ' p n α β, 0],
    [(𝒪_heart_n p n ⊟ ι p ⊡ δ p) α β, 0]]
where δ' (p : RPol[F,N,𝒮]) (n : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p, S p, 𝒮]] := δ p + (𝒪 p ⊞ 𝒪_heart_n p n ⊟ ι p ⊡ δ p)

instance : Unique (Fin (Listed.size 𝟙)) where
  default := ⟨0, by show 0 < 1; omega⟩
  uniq := by have : Listed.size 𝟙 = 1 := rfl; omega
instance : Unique (Fin (Listed.size 𝟙)) where
  default := ⟨0, by show 0 < 1; omega⟩
  uniq := by have : Listed.size 𝟙 = 1 := rfl; omega

variable [LawfulStar 𝒮]

def RPol.wnka [Star 𝒮] [LawfulStar 𝒮] (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] := ⟨ι p, δ p, 𝒪 p⟩

@[simp] theorem RPol.wnka_ι (p : RPol[F,N,𝒮]) : p.wnka.ι = ι p := rfl
@[simp] theorem RPol.wnka_δ (p : RPol[F,N,𝒮]) : p.wnka.δ = δ p := rfl
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
  | nil => grind [compute, compute', Matrix.one_mul]
  | cons α₀ A ih =>
    rcases A with _ | ⟨α₁, A⟩
    · grind [compute, compute', mul_one]
    · grind only [List.append_eq_nil_iff, List.cons_append, → List.eq_nil_of_append_eq_nil,
        compute', Matrix.mul_assoc, compute]

def WNKA.compute_pair' {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α₀ α' α'' : Pk[F,N]) :
    𝒜.compute (α₀ :: (A ++ [α', α''])) = (𝒜.compute' (α₀ :: (A ++ [α'])) * 𝒜.𝒪 α' α'') := by
  rw [← List.cons_append, WNKA.compute_pair]; rfl

def WNKA.sem {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨(fun x ↦ (𝒜.ι * 𝒜.compute x.pks) () ()), SetCoe.countable _⟩

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

theorem RPol.A_sem_eq (p : RPol[F,N,𝒮]) : 𝒜⟦~p⟧ = p.wnka.sem := rfl

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
theorem S.δ_identity {A B : Type*} [DecidableEq A] [DecidableEq B] :
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

@[simp]
theorem RPol.wnka_sem_pair (p : RPol[F,N,𝒮]) (α γ : Pk[F,N]) :
    p.wnka.sem (α, [], γ) = (ι p * 𝒪 p α γ) () () := by simp [wnka]; rfl

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
          A[A.length - 2]'(by simp [A]),
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

def xδ {X : Type} [DecidableEq X] [Fintype X] (d : Pk[F,N] → Pk[F,N] → 𝒲[X, X, 𝒮]) (xs : List Pk[F,N]) : 𝒲[X, X, 𝒮] :=
  match xs with
  | [] | [_] => 1
  | α::α'::xs => d α α' * xδ d (α'::xs)

variable [Inhabited Pk[F,N]] in
theorem xδ_δ_iter {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} :
      xδ (δ p₁.Iter) (α :: xₙ)
    = δ[[xδ (δ.δ' p₁) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α xₙ.head! * xδ (δ.δ' p₁) xₙ), if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp [S, xδ]
  | cons α₁ xₙ ih => rw [xδ, ih, δ, δ_wProd_δ]; simp; rfl

variable [Inhabited Pk[F,N]] in
theorem xδ_approx_δ_iter {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} {n} :
      xδ (approx_δ p₁ n) (α :: xₙ)
    = δ[[xδ (approx_δ.δ' p₁ n) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪_heart_n p₁ n ⊟ ι p₁ ⊡ δ p₁) α xₙ.head! * xδ (approx_δ.δ' p₁ n) xₙ),if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp only [xδ, ↓reduceIte, S.δ_identity]
  | cons α₁ xₙ ih => rw [xδ, ih, approx_δ, δ_wProd_δ]; simp [xδ]

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

theorem RPol.wnka_sem_drop :
    (RPol.wnka wnk_rpol {drop}).sem = G (wnk_rpol {drop} : RPol[F,N,𝒮]) := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, GS.pks, List.cons_append, asdasd, ↓reduceIte, GS.mk,
      Countsupp.coe_mk, List.nil_append, WNKA.compute, 𝒪]
    rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, List.nil_append,
      WNKA.compute, δ, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply]
@[simp]
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
      Countsupp.coe_mk, List.nil_append, WNKA.compute, δ, zero_mul, Matrix.zero_apply,
      right_eq_ite_iff, forall_exists_index]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, GS.pks, List.cons_append, GS.mk, Countsupp.coe_mk, WNKA.compute, δ,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.zero_apply, right_eq_ite_iff, forall_exists_index]
    grind
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
theorem RPol.wnka_compute'_dup {A : List Pk[F,N]} :
      wnk_rpol {dup}.wnka.compute' (𝒮:=𝒮) A
    = match A with
      | [] | [_] => 1
      | [α, β] => if α = β then η₂ ♡ ♣ else 0
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
        ext s₁ s₂
        split_ifs
        · simp only [η₁, η₂]
          grind [mul_zero, zero_mul, δ, Finsupp.η'_apply]
        · grind
        · simp_all only [and_true, Pi.ofNat_apply, right_eq_ite_iff, and_imp]
          grind
        · simp_all
      next A' α₃ α₄ h =>
        simp_all; clear h
        rintro ⟨_⟩
        ext s₁ s₂
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
    · simp only [S, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, G, GS.mk, GS.ofPks,
      List.cons_append, List.head_cons, List.drop_succ_cons, List.drop_zero, ne_eq, reduceCtorEq,
      not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_cons₂,
      List.dropLast_singleton, List.append_eq_nil_iff, and_false, List.getLast_cons,
      List.getLast_append_of_ne_nil, List.cons_ne_self, List.getLast_singleton, G.ofPk_apply,
      right_eq_ite_iff, forall_exists_index]
      grind

theorem RPol.wnka_sem_add {p₁ p₂ : RPol[F,N,𝒮]} :
    wnk_rpol {~p₁ ⨁ ~p₂}.wnka.sem = p₁.wnka.sem + p₂.wnka.sem := by
  ext ⟨α, xₙ, β⟩
  rw [RPol.wnka_sem_case]
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

theorem RPol.wnka_sem_weight {w} {p : RPol[F,N,𝒮]} :
    wnk_rpol {~w ⨀ ~p}.wnka.sem = (w * p.wnka.sem) := by
  ext ⟨α, xₙ, β⟩
  simp only [S, wnka_sem_case, ι, Matrix.smul_mul, List.getLastD_eq_getLast?, 𝒪,
    Matrix.down_smul_left, smul_eq_mul, Countsupp.hMul_apply_left]
  congr! 4
  induction xₙ generalizing α with
  | nil => simp [xδ]
  | cons α₀ xₙ ih => simp [xδ, δ, ih]

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

theorem RPol.wnka_sem_seq {p₁ p₂ : RPol[F,N,𝒮]}
    (ih₁ : p₁.wnka.sem = G p₁) (ih₂ : p₂.wnka.sem = G p₂) :
    wnk_rpol {~p₁ ; ~p₂}.wnka.sem = G wnk_rpol {~p₁; ~p₂} := by
  apply wnka_sem_eq_of
  intro A α α'
  letI : Inhabited Pk[F,N] := ⟨α⟩
  rw [seq_wnka_compute'']
  simp only [ι, List.length_append, List.length_cons, List.length_nil, zero_add,
    add_tsub_cancel_right, List.getElem!_eq_getElem?_getD, 𝒪, G, GS.ofPks, GS.mk, List.drop_one,
    ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_append_of_ne_nil, List.cons_ne_self,
    List.getLast_cons, List.getLast_singleton, G.concat_apply, List.length_dropLast,
    List.length_tail, Nat.reduceAdd, Nat.add_one_sub_one, GS.splitAtJoined, List.splitAt_eq]
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
      · simp_all only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right, getElem?_pos, Matrix.mul_assoc, List.drop_append,
        (by omega : n + 1 - A.length = 0), List.drop_zero, List.append_assoc, List.cons_append,
        List.nil_append, WNKA.compute_pair', wnka_𝒪]
        nth_rw 2 [← Matrix.mul_assoc]
        nth_rw 1 [← Matrix.mul_assoc]
        rw [Matrix.mul_apply]
        simp
        congr! 3
        induction A using List.reverseRecOn with
        | nil => simp at hn
        | append_singleton A α₁ ih =>
          simp at hn
          simp [List.take_append, List.getElem_append, hn]
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

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.Q_eq_A_sem (p : RPol[F,N,𝒮]) {xs} : Q⟦~p⟧ xs = fun x z ↦ 𝒜⟦~p⟧ ⟨x, xs, z⟩ := by
  ext
  simp [Q, A_sem]

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

omit [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq N] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Listed N] [Inhabited Pk[F,N]] in
@[simp]
theorem Matrix.smul_apply' (r : 𝒮) (A : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) (i j : Pk[F,N]) :
    (A <• r) i j = (A i j) •> r := rfl

section

noncomputable instance : HPow (GS F N →c 𝒮) ℕ (GS F N →c 𝒮) where
  hPow s n := (s ♢ ·)^[n] G⟦skip⟧

variable {p p₁ p₂ : RPol[F,N,𝒮]} {n} {α β} {xn}

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Inhabited Pk[F,N]] [Star 𝒮] in
@[simp]
theorem GS.skip_concat {x : GS F N →c 𝒮} : (G⟦skip⟧ ♢ x) = x := by
  ext ⟨α, xn, β⟩
  simp [G, G.concat_apply, GS.splitAtJoined, GS.mk]
  rw [Finset.sum_eq_single 0]
  · simp
    rw [Finset.sum_eq_single α]
    · simp
    · simp; grind
    · simp
  · simp
    grind [Prod.mk.injEq, List.take_eq_nil_iff, List.length_nil]
  · simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [Inhabited Pk[F,N]] [Star 𝒮] in
@[simp]
theorem GS.concat_skip {x : GS F N →c 𝒮} : (x ♢ G⟦skip⟧) = x := by
  ext ⟨α, xn, β⟩
  simp [G, G.concat_apply, GS.splitAtJoined, GS.mk]
  rw [Finset.sum_eq_single xn.length]
  · simp
    rw [Finset.sum_eq_single β]
    · simp
    · simp; grind
    · simp
  · simp
    grind [Prod.mk.injEq, List.take_eq_nil_iff, List.length_nil]
  · simp

theorem GS.concat_assoc {a b c : GS F N →c 𝒮} :
    (a ♢ b ♢ c) = (a ♢ (b ♢ c)) := by
  ext γ
  simp [G, G.concat_apply]
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  have {s : GS F N} {n} {γ} : (s.splitAtJoined n γ).1.2.1.length = min n s.2.1.length := by
    simp [GS.splitAtJoined]
    split
    simp
  have {s : GS F N} {n} {γ} : (s.splitAtJoined n γ).2.2.1.length = s.2.1.length - n := by
    simp [GS.splitAtJoined]
    split
    simp
  have : ∀ {s : GS F N} {n m} {γ κ}, ((s.splitAtJoined n γ).1.splitAtJoined m κ).1 = (s.splitAtJoined (n ⊓ m) κ).1 := by
    intro s n m γ κ
    simp [GS.splitAtJoined]
    grind
  have : ∀ {s : GS F N} {n m} {γ κ}, ((s.splitAtJoined n γ).2.splitAtJoined m κ).2 = (s.splitAtJoined (n + m) κ).2 := by
    intro s n m γ κ
    simp [GS.splitAtJoined]
    split
    rename_i h; split at h; cases h
    simp
  have : ∀ {s : GS F N} {n m} {γ κ}, ((s.splitAtJoined m κ).2.splitAtJoined (n - m) γ).1 = ((s.splitAtJoined n γ).1.splitAtJoined m κ).2 := by
    intro s n m γ κ
    simp [GS.splitAtJoined]
    split
    rename_i h; split at h; cases h
    simp
    rw [List.drop_take]
  simp_all
  have {n} {f : ℕ → Pk[F,N] → 𝒮} : ∑ x ∈ Finset.range n, ∑ (α : Pk[F, N]), f x α = ∑ (α : Pk[F, N]), ∑ x ∈ Finset.range n, f x α := by rw [Finset.sum_comm]
  simp [this]
  rw [Finset.sum_comm]; congr! 2 with α _ β
  simp_all only [Finset.mem_univ]
  have :
        ∑ i ∈ ..=‖γ.2.1‖, ∑ x ∈ ..=min i ‖γ.2.1‖, a (γ.splitAtJoined (min i x) α).1 * (b ((γ.splitAtJoined i β).1.splitAtJoined x α).2 * c (γ.splitAtJoined i β).2)
      = ∑ i ∈ ..=‖γ.2.1‖, ∑ x ∈ ..=i, a (γ.splitAtJoined x α).1 * (b ((γ.splitAtJoined i β).1.splitAtJoined x α).2 * c (γ.splitAtJoined i β).2) := by
    congr!
    · simp_all
    · simp_all
  simp [this]; clear this
  have {n} {f : ℕ → ℕ → 𝒮} : ∑ x ∈ ..=n, ∑ y ∈ ..=n - x, f x y = ∑ x ∈ ..=n, ∑ y ∈ ..=x, f y (x - y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp [Finset.sum_range_succ (n := n + 1)]
      have : ∑ x ∈ ..=n, ∑ y ∈ ..=n + 1 - x, f x y = ∑ x ∈ ..=n, ∑ y ∈ ..=(n - x) + 1, f x y := by
        congr! 2
        ext
        simp_all
        omega
      simp [this]
      conv => enter [1, 1, 2, x]; rw [Finset.sum_range_succ]
      simp [ih, Finset.sum_add_distrib]
      simp [add_assoc]
      congr! 3 with i hi j hj k hk
      grind
  simp [this]
  simp_all
  congr!
  grind

@[simp]
theorem GS.pow_zero : (𝒜⟦~p⟧^0) = G⟦skip⟧ := by
  simp [HPow.hPow, G]
@[simp]
theorem GS.pow_one : (𝒜⟦~p⟧^1) = 𝒜⟦~p⟧ := by
  ext ⟨α, xn, β⟩
  simp [HPow.hPow, G, G.concat_apply, GS.splitAtJoined, GS.mk]
  rw [Finset.sum_eq_single xn.length]
  · simp
    rw [Finset.sum_eq_single β]
    · simp
    · simp; grind
    · simp
  · simp
    grind [List.length_nil]
  · simp
theorem GS.pow_succ {n} : (𝒜⟦~p⟧^(n+1)) = (𝒜⟦~p⟧ ♢ 𝒜⟦~p⟧^n : GS F N →c 𝒮) := by
  simp only [HPow.hPow, G, mk, Function.iterate_succ', Function.comp_apply]
theorem GS.pow_succ' {n} : (𝒜⟦~p⟧^(n+1)) = ((𝒜⟦~p⟧^n) ♢ 𝒜⟦~p⟧ : GS F N →c 𝒮) := by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 1 [GS.pow_succ]
    nth_rw 2 [GS.pow_succ]
    rw [ih]
    simp [GS.concat_assoc]

theorem A_sem_cases {s} : 𝒜⟦~p₁⟧ s = (ι p₁ * xδ (δ p₁) (s.1 :: s.2.1) * 𝒪 p₁ (s.2.1.getLastD s.1) s.2.2).down := by
  rcases s with ⟨α, xn, β⟩
  simp [RPol.A_sem]
  rw [RPol.wnka_sem_case]
  simp

end

@[simp]
theorem G.pow_one {p : RPol[F,N,𝒮]} : G⟦~p⟧ ^ 1 = G⟦~p⟧ := by ext ⟨_, _, _⟩; simp [HPow.hPow]
@[simp]
theorem G.pow_zero {p : RPol[F,N,𝒮]} : G⟦~p⟧ ^ 0 = G⟦skip⟧ := by ext ⟨_, _, _⟩; simp [HPow.hPow]
@[simp]
theorem G.skip_apply {α β : Pk[F,N]} {xs : List Pk[F,N]} :
    G⟦skip⟧ (α, xs, β) = if xs = [] ∧ α = β then (1 : 𝒮) else 0 := by
  simp [G, GS.mk]
  split_ifs with h
  · rfl
  · grind
  · simp_all only [exists_apply_eq_apply, not_true_eq_false]
  · rfl
@[simp]
theorem G.pow_zero_cons_apply {p : RPol[F,N,𝒮]} {α γ β : Pk[F,N]} {xs : List Pk[F,N]} : (G⟦~p⟧ ^ 0) (α, γ :: xs, β) = 0 := by simp

variable (p p' : RPol[F,N,𝒮]) (h : 𝒜⟦~p⟧ = G⟦~p⟧)

def RPol.iterLe (p : RPol[F,N,𝒮]) : ℕ → RPol[F,N,𝒮]
  | 0 => wnk_rpol {skip}
  | n+1 => p.iterLe n + p^(n + 1)
@[simp]
theorem RPol.iterLe_zero : p.iterLe 0 = wnk_rpol {skip} := by
  rfl
@[simp]
theorem RPol.iterLe_one : p.iterLe 1 = wnk_rpol {skip} + wnk_rpol {~p; skip} := by
  simp only [iterLe, zero_add, pow_eq_iter, iter, add_def]
@[simp]
theorem RPol.iterLe_succ {n} : p.iterLe (n + 1) = p.iterLe n + p^(n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [iterLe]

@[simp]
theorem 𝒜_skip : (𝒜⟦skip⟧ : GS F N →c 𝒮) = G⟦skip⟧ := by
  simp [RPol.A_sem, ← RPol.wnka_sem_skip]
@[simp]
theorem 𝒜_add : 𝒜⟦~p ⨁ ~p'⟧ = 𝒜⟦~p⟧ + 𝒜⟦~p'⟧ := by
  simp [RPol.A_sem]
  rw [RPol.wnka_sem_add]
@[simp]
theorem 𝒜_seq (hp : 𝒜⟦~p⟧ = G⟦~p⟧) (hp' : 𝒜⟦~p'⟧ = G⟦~p'⟧) : 𝒜⟦~p ; ~p'⟧ = (𝒜⟦~p⟧ ♢ 𝒜⟦~p'⟧) := by
  simp [RPol.A_sem]
  rw [RPol.wnka_sem_seq]
  · simp [G, ← hp, ← hp']; rfl
  · assumption
  · assumption
theorem 𝒜_iter_eq_G (hp : 𝒜⟦~p⟧ = G⟦~p⟧) {n} : 𝒜⟦~(p.iter n)⟧ = G⟦~(p.iter n)⟧ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih, hp, G]

theorem 𝒜_iterLe_eq_G (h : 𝒜⟦~p⟧ = G⟦~p⟧) (n) : 𝒜⟦~(p.iterLe n)⟧ = G⟦~(p.iterLe n)⟧ := by
  induction n with
  | zero => simp
  | succ n ih => simp [G, ih, h, 𝒜_iter_eq_G]

theorem 𝒜_iterLe (h : 𝒜⟦~p⟧ = G⟦~p⟧) (n) : 𝒜⟦~(p.iterLe n)⟧ = ∑ i ∈ Finset.range (n + 1), 𝒜⟦~p⟧^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih, h, 𝒜_iter_eq_G]
    nth_rw 2 [Finset.sum_range_succ]
    congr
    simp [← h]
    rw [GS.pow_succ]
    simp_all
    congr
    clear ih
    induction n with
    | zero => simp
    | succ n ih =>
      simp [← h, GS.pow_succ]
      simp [h, ih, G]

@[simp]
theorem 𝒜_iterLe_succ (n) : 𝒜⟦~(p.iterLe (n + 1))⟧ = 𝒜⟦~(p.iterLe n)⟧ + 𝒜⟦~p; ~(p.iter n)⟧ := by
  simp
@[simp]
theorem 𝒜_iter_add (h : 𝒜⟦~p⟧ = G⟦~p⟧) (n m) : 𝒜⟦~(p.iter (n + m))⟧ = 𝒜⟦~(p.iter n) ; ~(p.iter m)⟧ := by
  induction m with
  | zero => simp [h, 𝒜_iter_eq_G]
  | succ m ih =>
    simp only [h, 𝒜_iter_eq_G, 𝒜_seq]
    have {m} : G⟦~(p.iter (m + 1))⟧ = G⟦~(p.iter m); ~p⟧ := by
      clear ih
      induction m with
      | zero =>
        ext ⟨α, xs, β⟩
        simp [G, G.concat_apply, GS.splitAtJoined]
        have {xs} {α₀ α₁ : Pk[F,N]} : (∃ α_1, gs[α_1;α_1] = (α₀, (xs : List Pk[F,N]), α₁)) ↔ α₀ = α₁ ∧ xs = [] := by
          simp [GS.mk]
          constructor
          · grind
          · simp
            rintro ⟨_⟩ ⟨_⟩
            grind
        simp [this, ite_and]
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ']
        simp_all
        rw [Finset.sum_ite_of_false]
        · simp
        · simp
      | succ m ih =>
        rw [RPol.iter]
        rw [G, ih, G, G]
        simp [G, GS.concat_assoc]
    rw [this, ← add_assoc]
    rw [this]
    simp [G]
    simp_all [𝒜_iter_eq_G, GS.concat_assoc]

@[simp]
theorem 𝒜_iterLe_add (h : 𝒜⟦~p⟧ = G⟦~p⟧) (n m) : 𝒜⟦~(p.iterLe (n + m))⟧ = 𝒜⟦~(p.iterLe n)⟧ + ∑ i ∈ Finset.range m, 𝒜⟦~(p.iter (i + 1)); ~(p.iter n)⟧ := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp_all [← add_assoc, Finset.sum_range_succ]
    congr! 1
    rw [add_comm, 𝒜_seq, 𝒜_seq, 𝒜_iter_add] <;> try assumption
    · simp only [h, 𝒜_iter_eq_G, 𝒜_seq, GS.concat_assoc]
    · simp only [h, 𝒜_iter_eq_G, 𝒜_seq, G]
    · simp only [h, 𝒜_iter_eq_G]
    · simp only [h, 𝒜_iter_eq_G]

@[simp]
theorem G_iterLe_add (h : 𝒜⟦~p⟧ = G⟦~p⟧) (n m) : G⟦~(p.iterLe (n + m))⟧ = G⟦~(p.iterLe n)⟧ + ∑ i ∈ Finset.range m, G⟦~(p.iter (i + 1)); ~(p.iter n)⟧ := by
  simp [𝒜_iterLe_add, ← 𝒜_iterLe_eq_G, h]
  congr with
  (repeat rw [𝒜_seq]) <;> try simp_all [G, 𝒜_iter_eq_G]

theorem new_approach' (h : 𝒜⟦~p⟧ = G⟦~p⟧) : ωSup ⟨fun n ↦ 𝒜⟦~(p.iterLe n)⟧, by simp [monotone_nat_of_le_succ, le_add_of_le_of_nonneg]⟩ = ω∑ (i : ℕ), 𝒜⟦~p⟧^i := by
  simp [𝒜_iterLe, h, ωSum_nat_eq_ωSup_succ]
theorem new_approach'_apply (h : 𝒜⟦~p⟧ = G⟦~p⟧) {xs} : ωSup ⟨fun n ↦ 𝒜⟦~(p.iterLe n)⟧ xs, by simp [monotone_nat_of_le_succ, le_add_of_le_of_nonneg]⟩ = ω∑ (i : ℕ), (𝒜⟦~p⟧^i) xs := by
  simp [𝒜_iterLe, h, ωSum_nat_eq_ωSup_succ]

def approx_𝒜 (p : RPol[F,N,𝒮]) (n : ℕ) : GS F N → 𝒮 := fun ⟨α, xₙ, β⟩ ↦ (approx_ι p * xδ (approx_δ p n) (α :: xₙ) * approx_𝒪 p n (xₙ.getLast?.getD α) β).down

@[simp]
theorem Q_empty_iter_eq_𝒜 {i α γ} : (Q⟦~p⟧ [] ^ i) α γ = (𝒜⟦~p⟧ ^ i) (α, [], γ) := by
  induction i generalizing α γ with
  | zero => simp; rfl
  | succ i ih =>
    simp [pow_succ, Matrix.mul_apply, GS.pow_succ', G.concat_apply, GS.splitAtJoined, ih]
    congr

@[simp]
theorem 𝒜_iter_empty {α β} : 𝒜⟦~p*⟧ ⟨α, [], β⟩ = 𝒪_heart p α β := by
  rw [A_sem_cases]
  simp [ι, 𝒪]
  rw [xδ_δ_iter, ι_wProd_δ, ι_wProd_𝒪]
  simp only [Matrix.down, Matrix.zero_mul, ↓reduceIte, Matrix.mul_zero, add_zero, Matrix.mul_one,
    zero_add, PUnit.default_eq_unit, Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply,
    Finset.univ_unique, Pi.one_apply, Matrix.up_apply, one_mul, Finset.sum_const,
    Finset.card_singleton, one_smul]
theorem 𝒜_iter_nonempty {α α₀ β} {xₙ} : 𝒜⟦~p*⟧ ⟨α, α₀ :: xₙ, β⟩ = ∑ x ∈ ..=‖xₙ‖, ∑ x_1, ∑ x_2, (ω∑ (x : ℕ), (𝒜⟦~p⟧ ^ x) (α, [], x_2)) * 𝒜⟦~p⟧ (x_2, α₀ :: xₙ[..x], x_1) * 𝒜⟦~p*⟧ (x_1, xₙ[x..], β) := by
  rw [A_sem_cases]
  simp [approx_𝒜]
  simp [ι, 𝒪, approx_ι, approx_𝒪]
  rw [xδ_δ_iter]
  simp
  rw [ι_wProd_δ, ι_wProd_𝒪]
  simp
  have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  simp [δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr! with i
    induction i generalizing α γ with
    | zero => simp; rfl
    | succ i ih =>
      simp [pow_succ, Matrix.mul_apply, GS.pow_succ', G.concat_apply, GS.splitAtJoined, ih]
      congr
  simp only [crox, Listed.array_sum_eq_finset_sum]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
  calc
    _ = ((𝒪_heart p ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p ⊟' 𝒪_heart p) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ x ∈ Finset.range xₙ.length,
            ∑ x_1,
              ((𝒪_heart p ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: List.take x xₙ) * 𝒪 p ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                      𝒜⟦~p*⟧ (x_1, List.drop x xₙ, β) := by
      rcases xₙ with _ | ⟨α₁, xₙ⟩
      · simp
      simp only [List.getLast?_cons_cons, List.length_cons]
      congr! with i hi γ hγ
      nth_rw 2 [Matrix.mul_assoc]
      nth_rw 1 [Matrix.mul_assoc]
      simp
      congr
      simp [A_sem_cases]
      simp [ι, 𝒪]
      rw [xδ_δ_iter]
      simp
      rw [ι_wProd_δ, ι_wProd_𝒪]
      simp
      have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
      simp [this]
      simp at hi
      split_ifs with hi'
      · omega
      · simp [δ.δ', List.head!_eq_head?, Option.getD_default_eq_iget, List.getLast?_drop, hi, hi', List.getLast?_cons]
    _ = ((𝒪_heart p ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p ⊟' 𝒪_heart p) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ i ∈ Finset.range xₙ.length,
            ∑ γ,
              (𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ *
                      Q⟦~p*⟧ (List.drop i xₙ) γ β := by
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
    _ = (𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪_heart p) α β +
          ∑ i ∈ Finset.range xₙ.length, ∑ γ,
              (𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ * Q⟦~p*⟧ (List.drop i xₙ) γ β := by
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
    _ = (𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪_heart p) α β +
          ∑ i ∈ Finset.range xₙ.length,
              ((𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ.take i)) * Q⟦~p*⟧ (List.drop i xₙ)) α β := by
      simp [Matrix.mul_apply]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ((𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ.take i)) * Q⟦~p*⟧ (List.drop i xₙ)) α β := by
      simp [Finset.sum_range_succ]
      rw [add_comm]
      congr!
      ext
      simp [Q]
      rw [RPol.wnka_sem_case]
      simp [ι, xδ, 𝒪]
      rw [ι_wProd_𝒪]
      simp [Matrix.down, Matrix.mul_apply]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart p α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
      simp [Matrix.mul_apply, Finset.sum_mul, RPol.Q_eq_A_sem]
    _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
      simp only [ωSum_sum_comm]
      simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, Q_empty_iter_eq_𝒜,
        ← ωSum_mul_right, ← ωSum_sum_comm]
    _ = _ := by simp [ωSum_sum_comm, ωSum_mul_right]

@[simp]
theorem approx_𝒜_iter_empty {α β} {n} : approx_𝒜 p n ⟨α, [], β⟩ = 𝒪_heart_n p n α β := by
  conv => left; simp [approx_𝒜]
  simp [xδ, approx_ι, approx_𝒪]
  rw [ι_wProd_𝒪]
  simp only [Matrix.down, Matrix.zero_mul, PUnit.default_eq_unit, Matrix.add_apply,
    Matrix.zero_apply, Matrix.mul_apply, Finset.univ_unique, Pi.one_apply, Matrix.up_apply, one_mul,
    Finset.sum_const, Finset.card_singleton, one_smul, zero_add]

theorem approx_𝒜_iter_nonempty {α α₀ β} {xₙ} {n} : approx_𝒜 p n ⟨α, α₀ :: xₙ, β⟩ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart_n p n α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * approx_𝒜 p n ⟨ξ, List.drop i xₙ, β⟩ := by
  conv => left; simp [approx_𝒜]
  simp [ι, 𝒪, approx_ι, approx_𝒪]
  rw [xδ_approx_δ_iter]
  simp
  rw [ι_wProd_δ, ι_wProd_𝒪]
  simp
  have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  simp [approx_δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq {n} : 𝒪_heart_n p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr!
  simp only [crox, Listed.array_sum_eq_finset_sum]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
  calc
    _ = ((𝒪_heart_n p n ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p ⊟' 𝒪_heart_n p n) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ x ∈ Finset.range xₙ.length,
            ∑ x_1,
              ((𝒪_heart_n p n ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: List.take x xₙ) * 𝒪 p ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                      approx_𝒜 p n (x_1, List.drop x xₙ, β) := by
      rcases xₙ with _ | ⟨α₁, xₙ⟩
      · simp
      simp only [List.getLast?_cons_cons, List.length_cons]
      congr! with i hi γ hγ
      nth_rw 2 [Matrix.mul_assoc]
      nth_rw 1 [Matrix.mul_assoc]
      simp
      congr
      simp [approx_𝒜]
      simp [approx_ι, approx_𝒪]
      rw [xδ_approx_δ_iter]
      simp
      rw [ι_wProd_δ, ι_wProd_𝒪]
      simp
      have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
      simp [this]
      simp at hi
      split_ifs with hi'
      · omega
      · simp [approx_δ.δ', List.head!_eq_head?_getD, Option.getD, List.getLast?_drop, hi, hi', List.getLast?_cons]
    _ = ((𝒪_heart_n p n ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p ⊟' 𝒪_heart_n p n) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ i ∈ Finset.range xₙ.length,
            ∑ γ,
              (𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ *
                      approx_𝒜 p n ⟨γ, List.drop i xₙ, β⟩ := by
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
    _ = (𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪_heart_n p n) α β +
          ∑ i ∈ Finset.range xₙ.length, ∑ γ,
              (𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ * approx_𝒜 p n ⟨γ, List.drop i xₙ, β⟩ := by
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
    _ = (𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪_heart_n p n) α β +
          ∑ i ∈ Finset.range xₙ.length,
              ∑ γ, ((𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ * approx_𝒜 p n ⟨γ, List.drop i xₙ, β⟩) := by
      simp [Matrix.mul_apply]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ γ, ((𝒪_heart_n p n * Q⟦~p⟧ (α₀ :: xₙ.take i))) α γ * approx_𝒜 p n ⟨γ, List.drop i xₙ, β⟩ := by
      simp [Finset.sum_range_succ, Matrix.mul_apply]
      rw [add_comm]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart_n p n α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * approx_𝒜 p n ⟨ξ, List.drop i xₙ, β⟩ := by
      simp [Matrix.mul_apply, Finset.sum_mul, RPol.Q_eq_A_sem]

theorem approx_𝒜_iter_eq {α β} {xₙ} {n} :
      approx_𝒜 p n ⟨α, xₙ, β⟩
    = if xₙ = [] then 𝒪_heart_n p n α β else ∑ i ∈ Finset.range xₙ.length, ∑ ξ, ∑ γ, 𝒪_heart_n p n α γ * 𝒜⟦~p⟧ ⟨γ, xₙ.take (i + 1), ξ⟩ * approx_𝒜 p n ⟨ξ, List.drop (i + 1) xₙ, β⟩ := by
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
  · simp [approx_𝒜_iter_nonempty]

theorem Finset.sum_range_le_sup_of_le {m n} {f g : ℕ → 𝒮} (h : f ≤ g) : ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (m ⊔ n), g i := by
  if h' : m < n then
    have : max m n = n := by omega
    simp_all; gcongr; apply h
  else
    simp_all
    grw [h']
    · gcongr; apply h
    · simp

theorem 𝒪_heart_n_apply {n α β} : 𝒪_heart_n p n α β = ∑ i ∈ Finset.range n, ((ι p ⊠ 𝒪 p) ^ i) α β  := by
  simp [𝒪_heart_n]; rw [Matrix.sum_apply]
@[simp]
theorem 𝒪_heart_n_le_succ {n α β} : 𝒪_heart_n p n α β ≤ 𝒪_heart_n p (n + 1) α β := by
  simp [𝒪_heart_n_apply]
  gcongr
  · simp
  · simp
@[gcongr]
theorem 𝒪_heart_n_le_apply_of_le {n m α β} (h : n ≤ m) : 𝒪_heart_n p n α β ≤ 𝒪_heart_n p m α β := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m h ih => grw [ih]; simp
@[gcongr]
theorem 𝒪_heart_n_le_of_le {n m} (h : n ≤ m) : 𝒪_heart_n p n ≤ 𝒪_heart_n p m :=
  fun _ _ ↦ 𝒪_heart_n_le_apply_of_le _ h
@[simp]
theorem approx_𝒜_le_succ {n} : approx_𝒜 p n ≤ approx_𝒜 p (n + 1) := by
  intro ⟨α, xₙ, β⟩
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
  simp [approx_𝒜_iter_nonempty]
  gcongr
  · omega
  · apply ihₙ; simp
@[gcongr]
theorem approx_𝒜_monotone : Monotone (approx_𝒜 p) := by
  refine monotone_nat_of_le_succ ?_
  simp
@[gcongr]
theorem approx_𝒜_apply_monotone {x} : Monotone (approx_𝒜 p · x) := by
  refine monotone_nat_of_le_succ fun i ↦ ?_
  apply approx_𝒜_monotone; omega

theorem 𝒜_pow_empty {i} {α β} : (𝒜⟦~p⟧ ^ i) (α, [], β) = ((ι p ⊠ 𝒪 p) ^ i) α β := by
  induction i generalizing α β with
  | zero => simp; rfl
  | succ i ih =>
    simp [GS.pow_succ', G.concat_apply, pow_succ, Matrix.mul_apply, GS.splitAtJoined, ih]
    congr

-- MARKER: 2026-03-20
theorem 𝒜_iter_eq_ωSup_approx {α β} {xₙ} : 𝒜⟦~p*⟧ ⟨α, xₙ, β⟩ = ωSup ⟨fun n ↦ approx_𝒜 p n ⟨α, xₙ, β⟩, approx_𝒜_apply_monotone p⟩ := by
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
    have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
      ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr! with i
      induction i generalizing α γ with
      | zero => simp; rfl
      | succ i ih =>
        simp_all
        simp [pow_succ, Matrix.mul_apply, ih, GS.pow_succ', G.concat_apply, GS.splitAtJoined]
        congr
    have 𝒪_heart_n_eq {n} : 𝒪_heart_n p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
      ext α γ; simp; congr!
    simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, ωSum_nat_eq_ωSup,
      𝒪_heart_n_eq]
    simp [Matrix.sum_apply]
  · simp [𝒜_iter_nonempty, approx_𝒜_iter_nonempty]
    conv => enter [1, 2, x, 2, x_1, 2, x_2, 2]; rw [ihₙ _ (by simp)]
    simp [mul_ωSup, sum_ωSup', ωSum_nat_eq_ωSup, ωSup_mul]
    apply le_antisymm
    · simp
      intro j k
      apply le_ωSup_of_le (j ⊔ k)
      simp
      simp [𝒪_heart_n_apply]
      gcongr with m hm γ _ γ'
      · apply Finset.sum_range_le_sup_of_le fun i ↦ ?_
        simp [𝒜_pow_empty]
      · simp
    · simp
      intro n
      apply le_ωSup_of_le n
      simp
      apply le_ωSup_of_le n
      simp
      congr!
      simp [𝒪_heart_n]
      rw [Matrix.sum_apply]
      congr!
      simp [𝒜_pow_empty]

@[simp]
theorem GS.exists_mk {γ δ : Pk[F,N]} {xs} : (∃ α, gs[α;α] = (γ, xs, δ)) ↔ γ = δ ∧ xs = [] := by
  constructor
  · simp [GS.mk]; grind
  · simp [GS.mk]; simp_all

@[simp]
theorem G.seq_skip : G⟦~p; skip⟧ = G⟦~p⟧ := by
  ext ⟨α, xs, β⟩;
  simp [G.concat_apply, G, GS.splitAtJoined, Finset.sum_range_succ, ite_and]
  have {x} : x ∈ Finset.range ‖xs‖ → ¬‖xs‖ ≤ x := by simp
  rw [Finset.sum_ite_of_false]
  · simp
  · simp

noncomputable def G' (xs : List Pk[F,N]) : 𝒲[Pk[F,N],Pk[F,N],𝒮] := fun a b ↦ G⟦~p⟧ ⟨a, xs, b⟩
theorem G_eq_G' {a xs b} : G⟦~p⟧ ⟨a, xs, b⟩ = G' p xs a b := by rfl
theorem 𝒜_eq_G' {a xs b} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : 𝒜⟦~p⟧ ⟨a, xs, b⟩ = G' p xs a b := by
  rw [← ihp]; rfl

theorem 𝒪_heart_n_eq_G' {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : 𝒪_heart_n p n = (∑ x ∈ Finset.range n, G' p [] ^ x) := by
  simp [𝒪_heart_n]
  have : (ι p ⊠ 𝒪 p) = G' p [] := by
    ext α' β'
    rw [← 𝒜_eq_G' p ihp]
    rfl
  simp [this]

@[simp]
def count (n m : ℕ) : ℕ := 2*n + m + (m - 1) * n

example {n} : count n 0 = 2 * n + 0 := by simp +arith [count]
example {n} : count n 1 = 2 * n + 1 := by simp +arith [count]
example {n} : count n 2 = 3 * n + 2 := by simp +arith [count]
example {n} : count n 3 = 4 * n + 3 := by simp +arith [count]
example {n} : count n 4 = 5 * n + 4 := by simp +arith [count]
example {n} : count n 5 = 6 * n + 5 := by simp +arith [count]

noncomputable def A' (n : ℕ) (xs : List Pk[F,N]) : 𝒲[Pk[F,N],Pk[F,N],𝒮] := fun a b ↦ approx_𝒜 p n ⟨a, xs, b⟩
theorem approx_𝒜_eq_A' {n} {g} : approx_𝒜 p n g = A' p n g.2.1 g.1 g.2.2 := by rfl

@[simp]
theorem A'_iter_zero {xs} :
    A' p 0 xs = 0 := by
  ext; simp [A']; rw [approx_𝒜_iter_eq]; simp [𝒪_heart_n]
theorem A'_iter_one_nil :
    A' p 1 [] = 1 := by
  ext; simp [A', 𝒪_heart_n]
theorem A'_iter_one_single {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 1 [α₀] = G' p [α₀] := by
  ext; simp [A', 𝒪_heart_n, approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, ← Matrix.mul_apply, mul_assoc]
theorem A'_iter_one_pair {α₀ α₁} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 1 [α₀, α₁] = G' p [α₀] * G' p [α₁] + G' p [α₀, α₁] := by
  ext; simp [A', 𝒪_heart_n, approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, ← Matrix.mul_apply, mul_assoc, Finset.sum_range_succ, ← Matrix.add_apply]
theorem A'_iter_one_triple {α₀ α₁ α₂} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 1 [α₀, α₁, α₂] = G' p [α₀] * G' p [α₁] * G' p [α₂] + G' p [α₀] * G' p [α₁, α₂] + G' p [α₀, α₁] * G' p [α₂] + G' p [α₀, α₁, α₂] := by
  ext; simp [A', 𝒪_heart_n, approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, ← Matrix.mul_apply, mul_assoc, Finset.sum_range_succ, ← Matrix.add_apply, mul_add]

noncomputable def G'' (n : ℕ) := ∑ i ∈ Finset.range n, (G' p [])^i
@[simp] theorem G''_zero : G'' p 0 = 0 := by simp [G'']
theorem G''_succ {n} : G'' p (n + 1) = G'' p n + (G' p [])^n := by simp [G'', Finset.sum_range_succ]
theorem G''_succ' {n} : G'' p (n + 1) = (G' p [])^n + G'' p n := by simp [G'', Finset.sum_range_succ, add_comm]

@[simp]
theorem A'_iter_nil {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n [] = G'' p n := by
  ext; simp [A', 𝒪_heart_n_eq_G', ihp, G'']

theorem A'_iter_single {α₀} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n [α₀] = G'' p n * G' p [α₀] * G'' p n := by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 1 [G''_succ]
    nth_rw 1 [G''_succ']
    simp [mul_add, add_mul]
    simp [← ih]; clear ih
    ext α β
    simp [A']
    rw [approx_𝒜_iter_eq]
    rw [approx_𝒜_iter_eq]
    simp [𝒪_heart_n_eq_G', ihp, Finset.sum_range_succ]
    simp [A', G'', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
    simp [Finset.mul_sum, Finset.sum_mul]
    simp [← mul_assoc]
    simp [← Finset.sum_mul]
    simp [← Matrix.mul_apply]
    simp [← Finset.mul_sum]
    simp [← Matrix.add_apply]
    set Q := (∑ x ∈ Finset.range n, G' p [] ^ x)
    set A := G' p [α₀]
    set B := G' p [] ^ n
    simp
    grind

theorem A'_iter_eq' {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n xs = (if xs = [] then (G'' p n) else ((G'' p n) * ∑ i ∈ Finset.range ‖xs‖, G' p (xs[..i + 1]) * A' p n (xs[i + 1..])) ) := by
  ext α β
  simp [A']
  rw [approx_𝒜_iter_eq]
  simp [𝒪_heart_n_eq_G', ihp, ← Finset.sum_mul, Finset.mul_sum, ← Matrix.mul_apply, 𝒜_eq_G', ← mul_assoc, approx_𝒜_eq_A']
  simp [← Finset.mul_sum, mul_assoc, ← Matrix.sum_apply]
  split_ifs <;> rfl
theorem A'_iter_eq {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n xs = G'' p n * (∑ ys ∈ List.partitions xs, (ys.map (fun y ↦ G' p y * G'' p n)).prod) := by
  induction xs using Nat.strongRecMeasure List.length; next xs ih =>
  rcases xs with _ | ⟨α₀, xs⟩
  · simp [List.partitions, ihp]
  simp_all only [List.length_cons]
  ext α β
  simp [A']
  simp [approx_𝒜_iter_nonempty]
  simp [𝒪_heart_n_eq_G', ihp, 𝒜_eq_G', approx_𝒜_eq_A']
  simp [← Matrix.mul_apply, ← Finset.sum_mul]
  simp [← Matrix.sum_apply]
  simp [Matrix.mul_assoc, ← Matrix.mul_sum]
  have : (∑ x ∈ Finset.range n, G' p [] ^ x) = G'' p n := by simp [G'']
  simp [this]
  congr!
  conv => enter [1, 2, _]; rw [ih _ (by simp)]
  simp [← mul_assoc]
  set g := fun y ↦ G' p y * G'' p n
  have : ∀ y, g y = G' p y * G'' p n := by intro; rfl
  simp [← this]
  simp [Finset.mul_sum]
  conv =>
    enter [1, 2, x, 2, i]
    rw [← List.prod_cons, ← List.map_cons]
  set f := fun ys ↦ (List.map g ys).prod
  rw [List.partitions_cons_eq_split]

theorem sum_partitions'_cons {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {x : ι} {xs : List ι} {n} {f : List (ℕ × List ι) → 𝒮'} :
      ∑ ys ∈ List.partitions' (x :: xs) n, f ys
    = if xs = [] then ∑ i ∈ ..=n, f [(i, [x])] else ∑ ys ∈ xs.partitions' n, (f ((ys.head!.1, x :: ys.head!.2) :: ys.tail) + ∑ i ∈ Finset.image (fun j ↦ (j, [x]) :: ys) (..=n), f i) := by
  split_ifs
  · subst_eqs
    simp [List.partitions']
  simp [List.partitions']
  rw [Finset.sum_biUnion]
  · have :
        ∑ ys ∈ xs.partitions' n,
          ∑
            i ∈
              match ys with
              | [] => Finset.image (fun i ↦ [(i, [x])]) (..=n)
              | (i, y) :: ys => insert ((i, x :: y) :: ys) (Finset.image (fun j ↦ (j, [x]) :: (i, y) :: ys) (..=n)),
            f i
      = ∑ ys ∈ xs.partitions' n,
          (f ((ys.head!.1, x :: ys.head!.2) :: ys.tail) + ∑ i ∈ (Finset.image (fun j ↦ (j, [x]) :: ys) (..=n)), f i) := by
      congr!
      split
      · simp_all [List.mem_partitions'_iff]
      · simp_all [List.mem_partitions'_iff]
    convert this
    simp
  · intro as has bs hbs h S h₁ h₂ Z hZ
    simp_all only [SetLike.mem_coe, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty,
      Finset.notMem_empty]
    specialize h₁ hZ
    specialize h₂ hZ
    simp_all [List.mem_partitions'_iff]
    rcases as with _ | ⟨⟨a, a'⟩, as⟩ <;> rcases bs with _ | ⟨⟨b, b'⟩, bs⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
      grind

theorem sum_partitionsFill' {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {xs : List ι} {n} {f : List (List ι) → 𝒮'} :
    ∑ ys ∈ List.partitionsFill' xs n, f ys = ∑ x ∈ xs.partitions' n, ∑ x_1 ∈ ..=n, f (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) x ++ List.replicate x_1 []) := by
  simp [List.partitionsFill']
  rw [Finset.sum_biUnion, Finset.sum_image]
  · simp
  · intro as has bs hbs h
    simp_all [List.mem_partitions'_iff]
    obtain ⟨⟨_⟩, has⟩ := has
    obtain ⟨h', hbs⟩ := hbs
    induction as generalizing bs with
    | nil => simp_all; rcases bs with _ | _ <;> simp_all; grind
    | cons a as ih =>
      obtain ⟨a, a'⟩ := a
      simp_all
      rcases bs with _ | ⟨⟨b, b'⟩, bs⟩
      · simp_all
      · simp_all
        suffices a = b by
          simp_all
          specialize @ih bs (by simp_all) (by grind)
          apply ih <;> clear ih
          · simp_all
          · grind
        rcases a' with _ | ⟨a₀, a'⟩
        · simp_all; grind
        rcases b' with _ | ⟨b₀, b'⟩
        · simp_all; grind
        simp_all
        set ts := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) as
        set ss := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) bs
        clear ih has hbs h'
        induction a generalizing b with
        | zero => simp at h; rcases b with _ | _ <;> simp_all [List.replicate]
        | succ a ih => rcases b with _ | _ <;> simp_all [List.replicate]
  · simp
    intro as has bs hbs h S h₁ h₂ Z hZ
    simp_all only [Set.mem_image, SetLike.mem_coe, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty,
      Finset.notMem_empty]
    simp_all [List.mem_partitions'_iff]
    specialize h₁ hZ
    specialize h₂ hZ
    simp_all
    obtain ⟨i, h₁, ⟨_⟩⟩ := h₁
    obtain ⟨j, h₂, h'⟩ := h₂
    obtain ⟨as, ⟨⟨_⟩, has⟩, _, ⟨_⟩⟩ := has
    obtain ⟨bs, ⟨h'', hbs⟩, _, ⟨_⟩⟩ := hbs
    clear hZ S
    contrapose! h
    simp_all
    suffices i = j by subst_eqs; simp_all only [List.append_cancel_right_eq]
    clear h''
    induction as using List.reverseRecOn with
    | nil =>
      simp at h'
      induction bs using List.reverseRecOn with
      | nil => simp at h'; omega
      | append_singleton bs b ih =>
        obtain ⟨b, b'⟩ := b
        clear ih
        simp at h'
        simp [← List.append_assoc] at h'
        simp [List.eq_replicate_iff] at h'
        obtain ⟨h₁, h₂⟩ := h'
        subst_eqs
        specialize h₂ b'
        simp at h₂
        subst_eqs
        simp at hbs
        grind
    | append_singleton as a ih =>
      obtain ⟨a, a'⟩ := a
      clear ih
      induction bs using List.reverseRecOn with
      | nil =>
        symm at h'
        simp [List.eq_replicate_iff] at h'
        obtain ⟨h₁, h₂⟩ := h'
        specialize h₂ a'
        simp at h₂
        subst_eqs
        simp at hbs
        grind
      | append_singleton bs b ih =>
        obtain ⟨b, b'⟩ := b
        clear ih
        simp at h'
        simp at has hbs
        rcases a' with _ | ⟨a₀, a'⟩
        · grind
        rcases b' with _ | ⟨b₀, b'⟩
        · grind
        simp [← List.append_assoc] at h'
        set ts := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) bs ++ List.replicate b []
        set ss := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) as ++ List.replicate a []
        clear hbs has
        induction i generalizing j with
        | zero =>
          simp at h'; rcases j with _ | _
          · rfl
          · simp [List.replicate_add] at h'
            rw [List.append_cons, List.append_cons] at h'
            simp only [List.append_nil, ← List.append_assoc, List.append_singleton_inj, List.nil_eq,
              reduceCtorEq, and_false] at h'
        | succ i ih =>
          rcases j with _ | j
          · simp [List.replicate_add] at h'
            nth_rw 2 [List.append_cons, List.append_cons] at h'
            simp [← List.append_assoc] at h'
          · simp [List.replicate_add] at h'
            conv at h' => left; rw [List.append_cons, ← List.append_assoc, ← List.append_cons]
            conv at h' => right; rw [List.append_cons, ← List.append_assoc, ← List.append_cons]
            simp
            exact ih (by omega) j (by omega) (List.append_cancel_right h')



theorem sum_partitionsFill'_cons {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {x : ι} {xs : List ι} {n} {f : List (List ι) → 𝒮'} (h : xs ≠ []) (hf : ∀ a b, f (a ++ b) = f a * f b) :
      ∑ ys ∈ List.partitionsFill' (x :: xs) n, f ys
    = ((∑ i ∈ xs.partitions' n,
      f (List.replicate i.head!.1 []) * f [x :: i.head!.2] *
        f (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) i.tail)) *
    ∑ i ∈ ..=n, f (List.replicate i [])) + ∑ i ∈ ..=n, ∑ ys ∈ List.partitionsFill' xs n, f (List.replicate i [] ++ [x] :: ys) := by
  simp [sum_partitionsFill']
  nth_rw 2 [Finset.sum_comm]
  simp [sum_partitions'_cons]
  simp [Finset.sum_add_distrib, h]
  congr! 1
  have hf' {a b} : f (a :: b) = f [a] * f b := by
    rw [← List.singleton_append, hf]
  simp [hf]
  conv => enter [1, 2, _, 2, _]; rw [hf']
  simp [hf]
  simp [← Finset.mul_sum]
  simp [← Finset.sum_mul, ← mul_assoc]

theorem List.mul_prod_mul_eq {α ι : Type*} [Semiring α] {xs : List ι} {a : α} {f : ι → α} :
    a * (xs.map (f · * a)).prod = (xs.map (a * f ·)).prod * a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [mul_assoc]
theorem A'_iter_eq_partitionsFill' {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p (n + 1) xs = ∑ ys ∈ List.partitionsFill' xs n, (ys.map (G' p)).prod := by
  induction xs using Nat.strongRecMeasure List.length; next xs ih =>
  rcases xs with _ | ⟨x, xs⟩
  · simp [A'_iter_eq, ihp, List.partitionsFill']; rfl
  · rw [A'_iter_eq' _ ihp]
    simp
    conv => enter [1, 2, 2, x, 2]; rw [ih _ (by simp)]
    if hxs : xs = [] then
      subst_eqs
      simp
      simp [sum_partitionsFill']
      simp [List.partitions', Finset.mul_sum, Finset.sum_mul, G'', mul_assoc]
      rw [Finset.sum_comm]
    else
      rw [sum_partitionsFill'_cons hxs (by simp)]
      simp
      rw [Finset.sum_range_succ']
      simp
      simp [← Finset.sum_mul, ← Finset.mul_sum, mul_add]
      congr! 1
      simp [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, ← Finset.mul_sum]
      have {ys : List (ℕ × List Pk[F,N])} : (List.map (G' p) (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) ys)).prod = (ys.map (fun x ↦ (G' p []) ^ x.1 * G' p x.2)).prod := by
        clear ih hxs
        induction ys with
        | nil => simp
        | cons y ys ih => simp_all [mul_assoc]
      simp [this]
      simp [← List.prod_cons, ← List.map_tail]
      conv =>
        enter [2, 1, 2, x', 1]
        rw [← List.map_cons (f := fun (x : ℕ × List Pk[F,N]) ↦ G' p [] ^ x.1 * G' p x.2) (a := ⟨x'.head!.1, x :: x'.head!.2⟩)]
      conv => left; simp [Finset.mul_sum]
      clear ih this
      conv => enter [1, 2, x, 2, i, 2, 1, 2]; rw [← List.singleton_append]
      conv => enter [2, 1, 2, x', 1, 2, 1, 2]; rw [← List.singleton_append]
      generalize [x] = l
      clear x
      induction xs generalizing l with
      | nil => simp at hxs
      | cons x xs ih =>
        simp_all
        rw [Finset.sum_range_succ']
        if hxs : xs = [] then
          subst_eqs
          simp [sum_partitionsFill']
          simp [List.partitions', Finset.mul_sum, Finset.sum_mul, G'', mul_assoc]
        else
          have ih' := ih hxs (l ++ [x])
          simp at ih'
          simp [ih']; clear ih'
          rw [sum_partitions'_cons]
          simp [hxs]
          simp [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
          congr! 1
          rw [sum_partitionsFill']
          simp
          simp [G'', ← Finset.mul_sum, ← Finset.sum_mul, ← mul_assoc]
          congr! 3 with ls hl
          clear ih hxs hl
          induction ls with
          | nil => simp
          | cons l ls ih => simp_all [mul_assoc]

theorem G'_seq xs : G' (p.Seq p') xs = (∑ c ∈ ..=‖xs‖, G' p (xs[..c]) * G' p' (xs[c..])) := by
  ext
  simp [G', G, G.concat_apply, GS.splitAtJoined]
  simp [G_eq_G', ← Matrix.mul_apply, ← Matrix.sum_apply]
theorem G'_skip xs : G' (wnk_rpol {skip} : RPol[F,N,𝒮]) xs = match xs with | [] => 1 | _ => 0 := by
  ext α β
  simp [G']
  split_ifs with h
  · rcases h with ⟨⟨_⟩, ⟨_⟩⟩
    simp
  · split
    · simp_all
    · simp_all

@[simp]
theorem G'_iter_nil {n} : G' (p.iter n) [] = (G' p [])^n := by
  induction n with
  | zero => simp [G'_skip]
  | succ n ihn =>
    simp [G'_seq]
    simp_all
    rcases n
    · simp_all
    · simp_all [pow_succ']

@[simp]
theorem List.buckets_pairwise_disjoint {α : Type*} [DecidableEq α] {xs : List α} {S : Set ℕ} :
    S.PairwiseDisjoint xs.buckets := by
  intro i hi j hj h A h₁ h₂ ls hls
  simp_all
  specialize h₁ hls
  specialize h₂ hls
  simp_all [List.mem_buckets_iff]

@[simp]
theorem List.buckets_succ_pairwise_disjoint {α : Type*} [DecidableEq α] {xs : List α} {S : Set ℕ} :
    S.PairwiseDisjoint (xs.buckets ·.succ) := by
  intro i hi j hj h A h₁ h₂ ls hls
  simp_all
  specialize h₁ hls
  specialize h₂ hls
  simp_all [List.mem_buckets_iff]

theorem G'_iter_eq_buckets {xs : List Pk[F,N]} {n : ℕ} :
    ∑ i ∈ Finset.range n, G' (p.iter i.succ) xs = ∑ ys ∈ (Finset.range n).biUnion (List.buckets xs ·.succ), (ys.map (G' p)).prod := by
  simp [Finset.sum_biUnion]
  congr! with i hi
  clear hi n
  induction i generalizing xs with
  | zero =>
    simp [G'_skip, G'_seq, Finset.sum_range_succ]
    have {a b : 𝒲[Pk[F,N], Pk[F,N], 𝒮]} : a = 0 → a + b = b := by simp_all
    apply this; clear this
    simp
    intro i hi
    split
    · simp_all; omega
    · simp_all
  | succ n ih =>
    simp_all
    rw [G'_seq]
    simp [ih]
    simp [Finset.mul_sum]
    simp [← List.prod_cons, ← List.map_cons]
    have : ∑ x ∈ ..=‖xs‖, ∑ x_1 ∈ xs[x..].buckets (n + 1), (List.map (G' p) (xs[..x] :: x_1)).prod = ∑ x ∈ ..=‖xs‖, ∑ x_1 ∈ (xs[x..].buckets (n + 1)).image (xs[..x] :: ·), (List.map (G' p) x_1).prod := by
      simp
    rw [this]; clear this
    rw [← Finset.sum_biUnion]
    · congr
      ext ys
      simp [List.mem_buckets_iff]
      constructor
      · simp
        rintro i hi zs h h' ⟨_⟩
        simp_all
      · simp
        rintro ⟨_⟩ h
        simp
        clear ih
        induction ys generalizing n with
        | nil => simp_all
        | cons y ys ih =>
          simp_all
          use ‖y‖
          simp
    · simp
      intro i hi j hj h S h₁ h₂ Z hZ
      simp_all only [Set.mem_Iio, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty,
        Finset.notMem_empty]
      specialize h₁ hZ
      specialize h₂ hZ
      simp_all
      obtain ⟨l₁, h₁, _, _⟩ := h₁
      obtain ⟨l₂, h₂, h'⟩ := h₂
      simp_all

theorem ωSup_nat_eq_succ {α : Type*} [OmegaCompletePartialOrder α] (f : Chain α) :
    ωSup f = ωSup ⟨(f <| · + 1), by intro a b hab; simp_all; grw [hab]⟩ := by
  apply le_antisymm
  all_goals simp; intro n; apply le_ωSup_of_le (n + 1); simp
  apply f.mono; omega

theorem 𝒜_star_eq_G (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : 𝒜⟦~p*⟧ = G⟦~p*⟧ := by
  ext ⟨α, xs, β⟩
  rw [𝒜_iter_eq_ωSup_approx]
  simp [G]
  simp [ωSum_nat_eq_ωSup_succ]
  have f (k : ℕ) := congrFun₂ (G'_iter_eq_buckets p (n:=k) (xs:=xs)) α β
  simp at f
  conv at f => enter [k, 1]; rw [Matrix.sum_apply]
  simp [Finset.sum_range_succ', f, G_eq_G']
  rw [ωSup_nat_eq_succ]
  rcases xs with _ | ⟨x, xs⟩
  · simp only [approx_𝒜_iter_empty, Chain.mk_apply, Finset.coe_range,
    List.buckets_succ_pairwise_disjoint, Finset.sum_biUnion]
    simp only [ihp, 𝒪_heart_n_eq_G', Finset.sum_range_succ', pow_zero, Matrix.add_apply,
      List.buckets_nil, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Finset.sum_singleton, List.map_replicate, List.prod_replicate, G'_skip]
  · simp [A'_iter_eq_partitionsFill', ihp, approx_𝒜_eq_A', G'_skip]
    apply le_antisymm
    all_goals apply ωSup_le _ _ fun n ↦ le_ωSup_of_le (List.count' (‖xs‖ + 1) (n + 1)) ?_
    all_goals simp only [Chain.mk_apply]; repeat rw [Matrix.sum_apply]
    · gcongr
      · simp
      · grw [List.partitionsFill'_subset_buckets _ _ (by simp)]
        simp
        intro i hi b hb
        simp
        rcases i with _ | i
        · simp_all
        · use i
          simp_all
          simp_all [List.count', mul_add, add_mul]
          omega
    · gcongr
      · simp
      · simp
        intro i hi
        apply subset_trans _ (List.buckets_subset_partitionsFill' (x :: xs) (n + 1) (by simp))
        intro b hb
        simp
        use i + 1
        simp_all

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
  | Iter p₁ ih => exact 𝒜_star_eq_G p₁ ih.symm

theorem Pol.sem_eq_toRPol_wnka_sem (p : Pol[F,N,𝒮]) (π) (h) :
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
      replace h := Prod.eq_iff_fst_eq_snd_eq.not.mp h
      simp_all
      split_ifs
      · simp_all
        grind
      · simp

/--
info: 'WeightedNetKAT.Pol.sem_eq_toRPol_wnka_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Pol.sem_eq_toRPol_wnka_sem

end

end WeightedNetKAT
