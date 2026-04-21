module

public import Batteries.Data.Array.Pairwise
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Data.List.DropRight
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Topology.Order.ScottTopology
public import WeightedNetKAT.FinsuppExt
public import WeightedNetKAT.Language
public import WeightedNetKAT.ListExt
public import WeightedNetKAT.MatrixExt
public import WeightedNetKAT.KStar.Matrix
public import WeightedNetKAT.KStar

@[expose] public section

open scoped RightActions
open scoped Computability
open OmegaCompletePartialOrder

open MatrixNotation

namespace WeightedNetKAT

variable {F : Type} [Listed F]
variable {N : Type} [Listed N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

scoped notation "𝟙" => Unit

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `B[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝒪` is a family of output weightings `R[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝒪 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F N 𝒮 Q: Type) [Semiring 𝒮] [Listed F] where
  /-- `ι` is the initial weightings. -/
  ι : 𝕄[𝟙,Q,𝒮]
  /-- `δ` is a family of transition functions `B[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F,N]) → 𝕄[Q,Q,𝒮]
  /-- `𝒪` is a family of output weightings `R[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : (α β : Pk[F,N]) → 𝕄[Q,𝟙,𝒮]
notation "WNKA[" F "," N "," 𝒮 "," Q "]" => WNKA F N 𝒮 Q

namespace WNKA

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def sem [DecidableEq N] [DecidableEq F] (𝒜 : WNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨fun ⟨α, xs, β⟩ ↦
    (((α :: xs).zip xs).foldl (fun acc (γ, κ) ↦ acc * 𝒜.δ γ κ) 𝒜.ι * 𝒜.𝒪 (xs.getLast?.getD α) β) () (),
    SetCoe.countable _⟩

def xδ (d : Pk[F,N] → Pk[F,N] → 𝕄[Q, Q, 𝒮]) (xs : List Pk[F,N]) : 𝕄[Q, Q, 𝒮] :=
  match xs with
  | [] | [_] => 1
  | α::α'::xs => d α α' * xδ d (α'::xs)

omit [Listed N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem xδ_right (f : Pk[F,N] → Pk[F,N] → 𝕄[Q, Q, 𝒮]) (A : List Pk[F,N]) {α₁ α₀} :
    xδ f (A ++ [α₁, α₀]) = (xδ f (A ++ [α₁]) * f α₁ α₀) := by
  induction A with
  | nil => simp [xδ]
  | cons α₀ s ih =>
    simp
    rcases s with _ | ⟨α₁, s⟩
    · simp [xδ]
    · simp [xδ]
      simp at ih
      rw [ih]
      simp [Matrix.mul_assoc]

omit [Listed N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem xδ_δ'_as_sum_unfolded [Inhabited Pk[F,N]] {xₙ : List Pk[F,N]} {l r : 𝕄[Pk[F,N], Pk[F,N], 𝕄[Q, Q, 𝒮]]} :
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

end WNKA

open WNKA (xδ xδ_right xδ_δ'_as_sum_unfolded)

scoped notation "♡" => Sum.inl ()
scoped notation "♣" => Sum.inr ()

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
abbrev η₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] (i : X) (j : Y) : 𝕄[X,Y,𝒮] :=
  fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

section Operators

/-! ## Homebrew matrix operators

For the automata construction we define some custom matrix operators that are variants of nested
multiplication or nested scalar multiplication.

-/

variable {N : Type*} [Fintype N]
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
variable {Q : Type*} [AddCommMonoid Q] [Mul Q]

def box [Unique A] (l : 𝕄[A, B, Q]) (r : 𝕄[N, N, 𝕄[B, A, Q]]) : 𝕄[N, N, Q] :=
  fun α β ↦ (l * r α β).down
infixl:70 " ⊠ " => box

def fox (l : 𝕄[A, B, Q]) (r : 𝕄[N, N, 𝕄[B, C, Q]]) : 𝕄[N, N, 𝕄[A, C, Q]] :=
  fun α β ↦ l * r α β
infixl:70 " ⊡ " => fox

def sox (l : 𝕄[N, N, Q]) (r : 𝕄[N, N, 𝕄[A, B, Q]]) : 𝕄[N, N, 𝕄[A, B, Q]] :=
  fun α β ↦ ∑ m, l α m •> r m β
infixl:70 " ⊟> " => sox

def sox' (l : 𝕄[N, N, 𝕄[A, B, Q]]) (r : 𝕄[N, N, Q]) : 𝕄[N, N, 𝕄[A, B, Q]] :=
  fun α β ↦ ∑ m, l α m <• r m β
infixl:70 " <⊟ " => sox'

def crox (l : 𝕄[N, N, 𝕄[A, B, Q]]) (r : 𝕄[N, N, 𝕄[B, C, Q]]) : 𝕄[N, N, 𝕄[A, C, Q]] :=
  fun α β ↦ ∑ m, l α m * r m β
infixl:70 " ⊞ " => crox

omit [Fintype A] [Fintype B]

theorem add_sox [RightDistribClass Q] (l l' : 𝕄[N, N, Q]) (r : 𝕄[N, N, 𝕄[A, B, Q]]) :
    ((l + l') ⊟> r) = (l ⊟> r) + (l' ⊟> r) := by
  ext α β a b
  simp [sox, Matrix.sum_apply, add_mul, Finset.sum_add_distrib]

theorem mul_sox {Q : Type*} [NonUnitalSemiring Q] (l l' : 𝕄[N, N, Q]) (r : 𝕄[N, N, 𝕄[A, B, Q]]) :
    ((l * l') ⊟> r) = (l ⊟> (l' ⊟> r)) := by
  ext α β a b
  simp [sox, Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

variable [DecidableEq N]

@[simp]
theorem one_sox {Q : Type*} [Semiring Q] (r : 𝕄[N, N, 𝕄[A, B, Q]]) :
    ((1 : 𝕄[N, N, Q]) ⊟> r) = r := by
  ext α β a b
  simp [sox, Matrix.one_apply]

end Operators

-- NOTE: computable star
noncomputable section

variable [DecidableEq N] [DecidableEq F]

namespace RPol

def ι (p : RPol[F,N,𝒮]) : 𝕄[𝟙,S p,𝒮] := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η₂ () ()
  | wnk_rpol {dup} => η₂ () ♡
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => C[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~_} => C[ι p₁, 0]
  | wnk_rpol {~_*} => C[0, 1]

mutual

def 𝒪_heart (p₁ : RPol[F,N,𝒮]) : 𝕄[Pk[F,N],Pk[F,N],𝒮] := (ι p₁ ⊠ 𝒪 p₁)∗

def 𝒪 (p : RPol[F,N,𝒮]) : 𝕄[Pk[F,N],Pk[F,N],𝕄[S p,𝟙,𝒮]] := fun α β ↦
  match p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} => if α = β then fun _ ↦ 1 else 0
  | wnk_rpol {@test ~γ} => if α = β ∧ β = γ then fun _ ↦ 1 else 0
  | wnk_rpol {@mod ~π} => if β = π then fun _ ↦ 1 else 0
  | wnk_rpol {dup} => if α = β then η₂ ♣ () else 0
  | wnk_rpol {~_ ⨀ ~p₁} => 𝒪 p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} => R[𝒪 p₁ α β, 𝒪 p₂ α β]
  | wnk_rpol {~p₁ ; ~p₂} => R[∑ γ, (𝒪 p₁ α γ * ι p₂ * 𝒪 p₂ γ β), 𝒪 p₂ α β]
  | wnk_rpol {~p₁*} =>
    R[(𝒪 p₁ <⊟ 𝒪_heart p₁) α β,
      𝒪_heart p₁ α β]

end

def δ (p : RPol[F,N,𝒮]) : 𝕄[Pk[F,N],Pk[F,N],𝕄[S p,S p,𝒮]] := fun α β ↦
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    0
  | wnk_rpol {dup} => fun s ↦ if s = ♡ ∧ α = β then η₁ ♣ else 0
  | wnk_rpol {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
      B[[δ p₁ α β,    0],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁ ; ~p₂} =>
      B[[δ p₁ α β,    ∑ γ, (𝒪 p₁ α γ * ι p₂ * δ p₂ γ β)],
        [0,           δ p₂ α β]]
  | wnk_rpol {~p₁*} =>
    B[[δ' p₁ α β, 0],
      [(𝒪_heart p₁ ⊟> (ι p₁ ⊡ δ p₁)) α β, 0]]
where δ' (p₁ : RPol[F,N,𝒮]) : 𝕄[Pk[F,N], Pk[F,N], 𝕄[S p₁, S p₁, 𝒮]] := δ p₁ + (𝒪 p₁ ⊞ (𝒪_heart p₁ ⊟> (ι p₁ ⊡ δ p₁)))

def 𝒪ₐ_heart (p₁ : RPol[F,N,𝒮]) (n : ℕ) : 𝕄[Pk[F,N],Pk[F,N],𝒮] :=
  ∑ i ∈ Finset.range n, (ι p₁ ⊠ 𝒪 p₁)^i
def ιₐ (p : RPol[F,N,𝒮]) : 𝕄[𝟙,S p ⊕ 𝟙,𝒮] :=
  C[0, fun () ↦ 1]
def 𝒪ₐ (p : RPol[F,N,𝒮]) (n : ℕ) : 𝕄[Pk[F,N],Pk[F,N],𝕄[S p ⊕ 𝟙,𝟙,𝒮]] := fun α β ↦
    R[
      (𝒪 p <⊟ 𝒪ₐ_heart p n) α β,
      𝒪ₐ_heart p n α β
    ]
def δₐ (p : RPol[F,N,𝒮]) (n : ℕ) : 𝕄[Pk[F,N],Pk[F,N],𝕄[S p ⊕ 𝟙,S p ⊕ 𝟙,𝒮]] := fun α β ↦
  B[[δ' p n α β, 0],
    [(𝒪ₐ_heart p n ⊟> (ι p ⊡ δ p)) α β, 0]]
where δ' (p : RPol[F,N,𝒮]) (n : ℕ) : 𝕄[Pk[F,N], Pk[F,N], 𝕄[S p, S p, 𝒮]] := δ p + (𝒪 p ⊞ (𝒪ₐ_heart p n ⊟> (ι p ⊡ δ p)))

theorem xδ_δ_iter {p₁ : RPol[F,N,𝒮]} {α : Pk[F,N]} {xₙ : List Pk[F,N]} :
      xδ (δ p₁.Iter) (α :: xₙ)
    = B[[xδ (δ.δ' p₁) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪_heart p₁ ⊟> (ι p₁ ⊡ δ p₁)) α (xₙ.head?.getD α) * xδ (δ.δ' p₁) xₙ), if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp [S, xδ]
  | cons α₁ xₙ ih => rw [xδ, ih, δ, Matrix.B_mul_B]; simp; rfl

theorem xδ_δₐ_iter {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} {n} :
      xδ (δₐ p₁ n) (α :: xₙ)
    = B[[xδ (δₐ.δ' p₁ n) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪ₐ_heart p₁ n ⊟> (ι p₁ ⊡ δ p₁)) α (xₙ.head?.getD α) * xδ (δₐ.δ' p₁ n) xₙ),if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp only [xδ, ↓reduceIte, Matrix.fromBlocks_one]
  | cons α₁ xₙ ih => rw [xδ, ih, δₐ, Matrix.B_mul_B]; simp [xδ]

theorem xδ_seq_eq {p₁ p₂ : RPol[F,N,𝒮]} [Inhabited Pk[F,N]] {A} :
      xδ (δ wnk_rpol {~p₁; ~p₂}) A =
    B[[xδ (δ p₁) A,
        ∑ γ, ∑ i ∈ Finset.range (A.length - 1), xδ (δ p₁) (A.take (i + 1)) * 𝒪 p₁ A[i]! γ * ι p₂ * xδ (δ p₂) (γ :: A.drop (i + 1))],
      [0, xδ (δ p₂) A]] := by
  induction A using List.reverseRecOn with
  | nil => simp [xδ]
  | append_singleton A α₀ ih =>
    clear ih
    induction A using List.reverseRecOn generalizing α₀ with
    | nil => simp [xδ]
    | append_singleton A α₁ ih =>
      simp
      simp [xδ_right]
      rw [ih]; clear ih
      simp [δ]
      rw [Matrix.B_mul_B]
      simp only [Matrix.mul_zero, add_zero, Matrix.mul_sum, ← Matrix.mul_assoc, Matrix.sum_mul, ←
        Finset.sum_add_distrib, Matrix.zero_mul, zero_mul, Finset.sum_const_zero, zero_add]
      congr! 4 with γ hi
      simp [Finset.sum_range_add, xδ]
      nth_rw 2 [add_comm]
      congr! 2 with n hn
      · congr; simp [List.take_append]
      · simp at hn
        simp only [List.take_append, (by omega : n + 1 - A.length = 0), List.take_zero,
          List.append_nil, List.getElem?_append, hn, ↓reduceIte, getElem?_pos, Option.getD_some,
          List.drop_append, List.drop_zero]
        nth_rw 2 [← List.cons_append]
        simp only [xδ_right]
        grind [Matrix.mul_assoc]

open Lean PrettyPrinter in
meta def unexpand : TSyntax `term → UnexpandM (TSyntax `cwnk_rpol)
  | `(wnk_rpol{$y}) => pure y | y => `(cwnk_rpol|~$y)

/-- Notation class for `X⟦~p⟧` -/
class Semantics (F N : Type) [Listed F] (𝒮 : Type) {α : Type*} (sem : RPol[F,N,𝒮] → α) where
abbrev Semantics.sem {F N : Type} [Listed F] {𝒮 : Type} {α : Type*} (sem : RPol[F,N,𝒮] → α) := sem

syntax:max ident "⟦" cwnk_rpol "⟧" : term
macro_rules | `($i:ident⟦$p⟧) => `(open RPol in Semantics.sem $i wnk_rpol { $p })
@[app_unexpander Semantics.sem]
meta def Semantics.sem.unexpander : Lean.PrettyPrinter.Unexpander
| `($_ $b:ident $p) => do
  `($b:ident⟦$(← unexpand p)⟧)
| _ => throw ()

variable (p p' : RPol[F,N,𝒮])

section

/-- The `WNKA` of policy `p` -/
def wnka [KStar 𝒮] [LawfulKStar 𝒮] (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] := ⟨ι p, δ p, 𝒪 p⟩

variable [KStar 𝒮] [LawfulKStar 𝒮]

@[simp] theorem wnka_ι : p.wnka.ι = ι p := rfl
@[simp] theorem wnka_δ : p.wnka.δ = δ p := rfl
@[simp] theorem wnka_𝒪 : p.wnka.𝒪 = 𝒪 p := rfl

/-- `𝒜⟦·⟧` is the **automata semantics** of `p` -/
def 𝒜 (p : RPol[F,N,𝒮]) := p.wnka.sem
instance : Semantics F N 𝒮 𝒜 where

/-- `Q⟦·⟧` is the **automata semantics** of `p` expressed as a matrix -/
def Q (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝕄[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ 𝒜⟦~p⟧ ⟨α, xᵢ, β⟩
instance : Semantics F N 𝒮 Q where

end

/-- `𝒜ₐ⟦·⟧` is the **approximate automata semantics** of `p` -/
def 𝒜ₐ (p : RPol[F,N,𝒮]) (n : ℕ) : GS F N → 𝒮 :=
  fun ⟨α, xₙ, β⟩ ↦ (ιₐ p * xδ (δₐ p n) (α :: xₙ) * 𝒪ₐ p n (xₙ.getLast?.getD α) β).down
instance : Semantics F N 𝒮 𝒜ₐ where

/-- `M⟦·⟧` is the **language semantics** of `p` expressed as a matrix -/
def M (p : RPol[F,N,𝒮]) (xᵢ : List Pk[F,N]) : 𝕄[Pk[F,N], Pk[F,N], 𝒮] :=
  fun α β ↦ G⟦~p⟧ ⟨α, xᵢ, β⟩
instance : Semantics F N 𝒮 M where

/-- `Qₐ⟦·⟧` is the **`n`-bounded automata semantics** of `p` expressed as a matrix -/
def Qₐ (p : RPol[F,N,𝒮]) (n : ℕ) (xs : List Pk[F,N]) : 𝕄[Pk[F,N],Pk[F,N],𝒮] :=
  fun a b ↦ 𝒜ₐ⟦~p⟧ n ⟨a, xs, b⟩
instance : Semantics F N 𝒮 Qₐ where

/-- `M'⟦·⟧` is the **`n`-repeated language semantics** of `p` expressed as a matrix -/
def M' (p : RPol[F,N,𝒮]) (n : ℕ) := ∑ i ∈ Finset.range n, (M⟦~p⟧ [])^i
instance : Semantics F N 𝒮 M' where

@[simp]
theorem 𝒜ₐ_iter_empty {α β} {n} : 𝒜ₐ⟦~p⟧ n ⟨α, [], β⟩ = 𝒪ₐ_heart p n α β := by
  conv => left; simp [𝒜ₐ, Semantics.sem]
  simp [xδ, ιₐ, 𝒪ₐ]
  rw [Matrix.C_mul_R]
  simp only [Matrix.down, Matrix.zero_mul, PUnit.default_eq_unit, Matrix.add_apply,
    Matrix.zero_apply, Matrix.mul_apply, Finset.univ_unique, Pi.one_apply, Matrix.up_apply, one_mul,
    Finset.sum_const, Finset.card_singleton, one_smul, zero_add]

section

variable [KStar 𝒮] [LawfulKStar 𝒮]

theorem 𝒜_def {p : RPol[F,N,𝒮]} {gs} :
    𝒜⟦~p⟧ gs = (((gs.1 :: gs.2.1).zip gs.2.1).foldl (fun acc (γ, κ) ↦ acc * δ p γ κ) (ι p) * 𝒪 p (gs.2.1.getLast?.getD gs.1) gs.2.2) () () := by
  obtain ⟨α, xs, β⟩ := gs
  simp [Semantics.sem, 𝒜, WNKA.sem]

theorem 𝒜_def' {p : RPol[F,N,𝒮]} {gs} :
      𝒜⟦~p⟧ gs
    = if gs.2.1 = [] then (ι p * 𝒪 p gs.1 gs.2.2) () () else
      (ι p * (((gs.1 :: gs.2.1).zip gs.2.1).map (fun (γ, κ) ↦ δ p γ κ)).prod * 𝒪 p (gs.2.1.getLast?.getD gs.1) gs.2.2) () () := by
  obtain ⟨α, (_ | ⟨γ, xs⟩), β⟩ := gs
  · simp [𝒜_def]
  · simp [𝒜_def, ← Matrix.mul_assoc, List.getLast?_cons]
    generalize ι p * δ p α γ = i
    generalize 𝒪 p (xs.getLast?.getD γ) β = j
    clear α β
    induction xs generalizing i γ with
    | nil => simp
    | cons x xs ih => simp [← Matrix.mul_assoc, ih]

theorem 𝒜_def'' {p : RPol[F,N,𝒮]} {gs} :
      𝒜⟦~p⟧ gs
    = if gs.2.1 = [] then (ι p * 𝒪 p gs.1 gs.2.2) () () else
      (ι p * xδ (δ p) (gs.1 :: gs.2.1) * 𝒪 p (gs.2.1.getLast?.getD gs.1) gs.2.2) () () := by
  rw [𝒜_def']
  obtain ⟨α, (_ | ⟨γ, xs⟩), β⟩ := gs
  · simp
  · simp [Matrix.mul_assoc, List.getLast?_cons]
    congr! 1
    simp [← Matrix.mul_assoc]
    congr! 1
    induction xs generalizing α γ with
    | nil => simp [xδ]
    | cons x xs ih => simp [xδ, ih]

/-- A proof that `𝒜⟦p⟧ = G⟦p⟧` -/
syntax "𝒜_proof " cwnk_rpol : term
macro_rules | `(𝒜_proof $t) => `((𝒜⟦$t⟧ : GS[F, N] →c 𝒮) = G⟦$t⟧)

theorem 𝒜_drop : 𝒜_proof drop := by
  ext ⟨α, xs, β⟩
  simp [𝒜_def]
  rcases xs with _ | ⟨x, xs⟩ <;> simp [ι, 𝒪, G] <;> rfl

theorem 𝒜_single {α : Type*} {motive : α → List α → α → Prop}
    (nil : ∀ a b, motive a [] b) (single : ∀ a x b, motive a [x] b)
    (ind : ∀ a b c d xs, motive c xs d → motive b (c :: xs) d → motive a (b :: c :: xs) d)
    (a : α) (xs : List α) (b : α) :
    motive a xs b := by
  induction xs using Nat.strongRecMeasure List.length generalizing a b with
  | ind xs ih => rcases xs with _ | ⟨x, (_ | ⟨x', xs⟩)⟩ <;> grind

@[simp]
theorem 𝒜_skip : 𝒜_proof skip := by
  ext ⟨α, xs, β⟩
  simp [𝒜_def]
  induction α, xs, β using 𝒜_single <;> simp_all [ι, δ, 𝒪, List.getLast?_cons, Matrix.ite_apply]
  split_ifs <;> rfl

theorem 𝒜_test {t} : 𝒜_proof @test ~t := by
  ext ⟨α, xs, β⟩
  simp [𝒜_def]
  induction α, xs, β using 𝒜_single <;> simp_all [ι, δ, 𝒪, List.getLast?_cons,]
  split_ifs <;> (try rfl) <;> grind

theorem 𝒜_mod {π} : 𝒜_proof @mod ~π := by
  ext ⟨α, xs, β⟩
  simp [𝒜_def]
  induction α, xs, β using 𝒜_single <;> simp_all [ι, δ, 𝒪, List.getLast?_cons,]
  split_ifs <;> rfl

theorem 𝒜_dup : 𝒜_proof dup := by
  ext ⟨α, xs, β⟩
  simp [𝒜_def']
  rcases xs with _ | ⟨γ, (_ | ⟨κ, xs⟩)⟩
  · simp [ι, 𝒪, Matrix.mul_apply, Matrix.ite_apply]
  · simp [ι, 𝒪, δ]
    by_cases α = γ <;> by_cases γ = β <;> subst_eqs <;> simp_all [Matrix.mul_apply] <;> grind
  · simp [← Matrix.mul_assoc]
    generalize h : ι (wnk_rpol {dup} : RPol[_,_,𝒮]) * δ wnk_rpol {dup} α γ * δ wnk_rpol {dup} γ κ = x
    suffices x = 0 by simp [this]
    ext ⟨_⟩ s
    simp [← h, ι, δ, Matrix.mul_apply]
    simp [ite_apply, ← ite_and]

@[simp]
theorem 𝒜_add_eq {p₁ p₂ : RPol[F,N,𝒮]} : 𝒜⟦~p₁ ⨁ ~p₂⟧ = 𝒜⟦~p₁⟧ + 𝒜⟦~p₂⟧ := by
  ext ⟨α, (_ | ⟨γ, xs⟩), β⟩
  · simp [𝒜_def', ι, 𝒪, Matrix.C_mul_R]
  · simp [𝒜_def', ι, 𝒪, δ, Matrix.C_mul_B, ← Matrix.mul_assoc]
    generalize ι p₁ * δ p₁ α γ = i₁
    generalize ι p₂ * δ p₂ α γ = i₂
    induction xs generalizing i₁ i₂ α β γ with
    | nil => simp [Matrix.C_mul_R]
    | cons x xs ih => simp [Matrix.C_mul_B, ← Matrix.mul_assoc, ih]

theorem 𝒜_add {p₁ p₂} (ih₁ : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) (ih₂ : 𝒜⟦~p₂⟧ = G⟦~p₂⟧) : 𝒜_proof ~p₁ ⨁ ~p₂ := by
  simp [ih₁, ih₂, G]

@[simp]
theorem 𝒜_weight_eq {w} {p : RPol[F,N,𝒮]} : 𝒜⟦~w ⨀ ~p⟧ = w * 𝒜⟦~p⟧ := by
  ext ⟨α, (_ | ⟨γ, xs⟩), β⟩ <;> simp [𝒜_def', ι, 𝒪, δ, ← Matrix.mul_assoc]

theorem 𝒜_weight {w p} (ih : 𝒜⟦~p⟧ = G⟦~p⟧) : 𝒜_proof ~w ⨀ ~p := by simp [G, ih]

@[simp]
theorem 𝒜_seq_eq {p₁ p₂ : RPol[F,N,𝒮]} : 𝒜⟦~p₁ ; ~p₂⟧ = (𝒜⟦~p₁⟧ ♢ 𝒜⟦~p₂⟧) := by
  ext ⟨α, (_ | ⟨γ, xs⟩), β⟩
  · simp only [𝒜_def', ↓reduceIte, ι, 𝒪, Matrix.C_mul_R, Matrix.mul_sum, ← Matrix.mul_assoc,
    Matrix.zero_mul, Matrix.add_apply, Matrix.sum_apply, Matrix.zero_apply, add_zero,
    G.concat_apply, List.length_nil, zero_add, Finset.range_one, GS.splitAtJoined, List.splitAt_eq,
    List.take_nil, List.drop_nil, ← Matrix.unit_mul_apply, Finset.sum_const, Finset.card_singleton,
    one_smul]
  · simp [𝒜_def'', ι, 𝒪, δ, Matrix.C_mul_B, ← Matrix.mul_assoc, G.concat_apply, GS.splitAtJoined, xδ]
    letI : Inhabited Pk[F,N] := ⟨α⟩
    simp [List.getLast?_cons]
    rw [xδ_seq_eq]
    simp [Matrix.C_mul_B, Matrix.C_mul_R]
    rw [Finset.sum_range_succ]
    simp [Matrix.mul_sum, Matrix.sum_mul, xδ, List.getLast?_cons]
    rw [add_comm]
    congr
    · rw [Finset.sum_range_succ']
      have {n : ℕ} {f g : ℕ → 𝒮} : (∑ i ∈ Finset.range n, if n ≤ i then f i else g i) = ∑ i ∈ Finset.range n, g i := by
        congr! with i
        simp_all
      simp [xδ, this, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply]
      rw [Finset.sum_comm]
      congr! with i hi κ
      · simp [← Matrix.unit_mul_apply, ← Matrix.mul_assoc, List.getLast?_cons, List.getLast?_drop, List.getLast?_take, List.getElem?_cons]
        grind
      · simp [← Matrix.unit_mul_apply, ← Matrix.mul_assoc, List.getLast?_cons]
    · simp [← Matrix.unit_mul_apply, ← Matrix.mul_assoc, Matrix.sum_apply]

theorem 𝒜_seq {p₁ p₂} (ih₁ : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) (ih₂ : 𝒜⟦~p₂⟧ = G⟦~p₂⟧) : 𝒜_proof ~p₁ ; ~p₂ := by
  simp [G, ih₁, ih₂]

theorem Q_eq_𝒜 (p : RPol[F,N,𝒮]) {xs} : Q⟦~p⟧ xs = fun x z ↦ 𝒜⟦~p⟧ ⟨x, xs, z⟩ := by rfl

theorem 𝒜_eq_M {a xs b} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : 𝒜⟦~p⟧ ⟨a, xs, b⟩ = M⟦~p⟧ xs a b := by
  rw [← ihp]; rfl

theorem 𝒪ₐ_heart_eq_M {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : 𝒪ₐ_heart p n = (∑ x ∈ Finset.range n, M⟦~p⟧ [] ^ x) := by
  simp [𝒪ₐ_heart]
  have : (ι p ⊠ 𝒪 p) = M⟦~p⟧ [] := by
    ext α' β'
    rw [← 𝒜_eq_M p ihp]
    rfl
  simp [this]

@[simp]
theorem Q_nil_iter_eq_𝒜 {i α γ} : (Q⟦~p⟧ [] ^ i) α γ = (𝒜⟦~p⟧ ^ i) (α, [], γ) := by
  induction i generalizing α γ with
  | zero => simp; rfl
  | succ i ih =>
    simp [pow_succ, Matrix.mul_apply, GS.pow_succ', G.concat_apply, GS.splitAtJoined, ih]
    congr

@[simp]
theorem 𝒜_iter_nil {α β} : 𝒜⟦~p*⟧ ⟨α, [], β⟩ = 𝒪_heart p α β := by
  rw [𝒜_def']; simp [ι, 𝒪, Matrix.C_mul_R]

theorem 𝒜_pow_empty {i} {α β} : (𝒜⟦~p⟧ ^ i) (α, [], β) = ((ι p ⊠ 𝒪 p) ^ i) α β := by
  induction i generalizing α β with
  | zero => simp; rfl
  | succ i ih =>
    simp [GS.pow_succ', G.concat_apply, pow_succ, Matrix.mul_apply, GS.splitAtJoined, ih]
    congr

@[simp]
theorem Qₐ_iter_nil {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    Qₐ⟦~p⟧ n [] = M'⟦~p⟧ n := by
  ext; simp [Qₐ, 𝒪ₐ_heart_eq_M, ihp, M']

variable [Inhabited Pk[F,N]]

theorem 𝒜ₐ_iter_nonempty {α α₀ β} {xₙ} {n} :
    𝒜ₐ⟦~p⟧ n ⟨α, α₀ :: xₙ, β⟩ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪ₐ_heart p n α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜ₐ⟦~p⟧ n ⟨ξ, List.drop i xₙ, β⟩ := by
  conv => left; simp [𝒜ₐ, Semantics.sem]
  simp [ιₐ, 𝒪ₐ]
  rw [xδ_δₐ_iter]
  simp [Matrix.C_mul_B, Matrix.C_mul_R, δₐ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq {n} : 𝒪ₐ_heart p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
    ext α γ; simp; congr!
  simp only [crox]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
  calc
    _ = ((𝒪ₐ_heart p n ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p <⊟ 𝒪ₐ_heart p n) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ x ∈ Finset.range xₙ.length,
            ∑ x_1,
              ((𝒪ₐ_heart p n ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: List.take x xₙ) * 𝒪 p ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                      𝒜ₐ⟦~p⟧ n (x_1, List.drop x xₙ, β) := by
      rcases xₙ with _ | ⟨α₁, xₙ⟩
      · simp
      simp only [List.getLast?_cons_cons, List.length_cons]
      congr! with i hi γ hγ
      nth_rw 2 [Matrix.mul_assoc]
      nth_rw 1 [Matrix.mul_assoc]
      simp
      congr
      simp [𝒜ₐ, Semantics.sem]
      simp [ιₐ, 𝒪ₐ]
      rw [xδ_δₐ_iter]
      simp
      rw [Matrix.C_mul_B, Matrix.C_mul_R]
      simp
      simp at hi
      split_ifs with hi'
      · omega
      · simp [δₐ.δ', Option.getD, List.getLast?_drop, hi, hi', List.getLast?_cons]
    _ = ((𝒪ₐ_heart p n ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p <⊟ 𝒪ₐ_heart p n) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ i ∈ Finset.range xₙ.length,
            ∑ γ,
              (𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ *
                      𝒜ₐ⟦~p⟧ n ⟨γ, List.drop i xₙ, β⟩ := by
      congr! with i hi γ hγ
      simp only [Finset.mem_range] at hi
      nth_rw 1 [Matrix.mul_apply]
      simp [Q, Semantics.sem.eq_def (sem:=Q), sox, Matrix.sum_mul]
      congr! with ξ hξ
      simp [𝒜_def'']
      simp [xδ, fox, ← Matrix.mul_assoc, Matrix.down, List.getLast?_cons, List.getLast?_take]
      congr! 2
      rcases i with _ | i
      · simp
      · have : i < xₙ.length := by omega
        simp [this]
    _ = (𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪ₐ_heart p n) α β +
          ∑ i ∈ Finset.range xₙ.length, ∑ γ,
              (𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ * 𝒜ₐ⟦~p⟧ n ⟨γ, List.drop i xₙ, β⟩ := by
      congr! with i hi γ hγ
      nth_rw 2 [Matrix.mul_assoc]
      nth_rw 1 [Matrix.mul_apply]
      conv => right; arg 2; ext; rw [Matrix.mul_apply]
      simp [Q, Semantics.sem.eq_def (sem:=Q), sox, sox', Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum, Matrix.mul_assoc, mul_assoc]
      rw [Finset.sum_comm]
      congr! 4 with γ hγ ξ hξ
      simp [𝒜_def'']
      simp [xδ, fox, ← Matrix.mul_assoc]
      congr! 3
    _ = (𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ) * 𝒪ₐ_heart p n) α β +
          ∑ i ∈ Finset.range xₙ.length,
              ∑ γ, ((𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ * 𝒜ₐ⟦~p⟧ n ⟨γ, List.drop i xₙ, β⟩) := by
      simp [Matrix.mul_apply]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ γ, ((𝒪ₐ_heart p n * Q⟦~p⟧ (α₀ :: xₙ.take i))) α γ * 𝒜ₐ⟦~p⟧ n ⟨γ, List.drop i xₙ, β⟩ := by
      simp [Finset.sum_range_succ, Matrix.mul_apply]
      rw [add_comm]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪ₐ_heart p n α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜ₐ⟦~p⟧ n ⟨ξ, List.drop i xₙ, β⟩ := by
      simp [Matrix.mul_apply, Finset.sum_mul, Q_eq_𝒜]

theorem 𝒜ₐ_iter_eq {α β} {xₙ} {n} :
      𝒜ₐ⟦~p⟧ n ⟨α, xₙ, β⟩
    = if xₙ = [] then 𝒪ₐ_heart p n α β else ∑ i ∈ Finset.range xₙ.length, ∑ ξ, ∑ γ, 𝒪ₐ_heart p n α γ * 𝒜⟦~p⟧ ⟨γ, xₙ.take (i + 1), ξ⟩ * 𝒜ₐ⟦~p⟧ n ⟨ξ, List.drop (i + 1) xₙ, β⟩ := by
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
  · simp [𝒜ₐ_iter_nonempty]

end

@[simp] theorem M'_zero : M'⟦~p⟧ 0 = 0 := by simp [M']
theorem M'_succ {n} : M'⟦~p⟧ (n + 1) = M'⟦~p⟧ n + (M⟦~p⟧ [])^n := by simp [M', Semantics.sem, Finset.sum_range_succ]
theorem M'_succ' {n} : M'⟦~p⟧ (n + 1) = (M⟦~p⟧ [])^n + M'⟦~p⟧ n := by simp [M', Semantics.sem, Finset.sum_range_succ, add_comm]

theorem G_eq_M {a xs b} : G⟦~p⟧ ⟨a, xs, b⟩ = M⟦~p⟧ xs a b := by rfl

theorem M_seq xs : M⟦~p ; ~p'⟧ xs = ∑ c ∈ ..=‖xs‖, M⟦~p⟧ (xs[..c]) * M⟦~p'⟧ (xs[c..]) := by
  ext
  simp [M, G, Semantics.sem, G.concat_apply, GS.splitAtJoined]
  simp [G_eq_M, Semantics.sem, ← Matrix.mul_apply, ← Matrix.sum_apply]
theorem M_skip {xs : List Pk[F,N]} : M⟦skip⟧ xs = if xs = [] then (1 : 𝕄[_,_,𝒮]) else 0 := by
  ext α β
  rcases xs with _ | ⟨_, _⟩ <;> simp [M, Semantics.sem]
  rfl

@[simp]
theorem M_iter_nil {n} : M⟦~(p.iter n)⟧ [] = M⟦~p⟧ [] ^ n := by
  induction n with
  | zero => simp [M_skip]
  | succ => rcases ‹Nat› <;> simp_all [M_seq, pow_succ']

theorem M_iter_eq_buckets {xs : List Pk[F,N]} {n : ℕ} :
    ∑ i ∈ Finset.range n, M⟦~p; ~(p.iter i)⟧ xs = ∑ ys ∈ (Finset.range n).biUnion (List.buckets xs ·.succ), (ys.map M⟦~p⟧).prod := by
  simp [Finset.sum_biUnion]
  congr! with i hi
  clear hi n
  induction i generalizing xs with
  | zero =>
    simp [M_skip, M_seq, Finset.sum_range_succ]
    have {a b : 𝕄[Pk[F,N], Pk[F,N], 𝒮]} : a = 0 → a + b = b := by simp_all
    apply this; clear this
    simp_all
  | succ n ih =>
    simp_all
    rw [M_seq]
    simp [ih]
    simp [Finset.mul_sum]
    simp [← List.prod_cons, ← List.map_cons]
    have : ∑ x ∈ ..=‖xs‖, ∑ x_1 ∈ xs[x..].buckets (n + 1), (List.map (M⟦~p⟧) (xs[..x] :: x_1)).prod = ∑ x ∈ ..=‖xs‖, ∑ x_1 ∈ (xs[x..].buckets (n + 1)).image (xs[..x] :: ·), (List.map (M⟦~p⟧) x_1).prod := by
      simp
    rw [this, ← Finset.sum_biUnion]; clear this
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
        | cons y ys ih => use ‖y‖; simp_all
    · simp
      intro i hi j hj h S h₁ h₂ Z hZ
      simp_all only [Set.mem_Iio, ne_eq, Finset.le_eq_subset]
      specialize h₁ hZ
      specialize h₂ hZ
      simp_all
      obtain ⟨l₁, h₁, _, _⟩ := h₁
      obtain ⟨l₂, h₂, h'⟩ := h₂
      simp_all

theorem 𝒪ₐ_heart_apply {n α β} : 𝒪ₐ_heart p n α β = ∑ i ∈ Finset.range n, ((ι p ⊠ 𝒪 p) ^ i) α β  := by
  simp [𝒪ₐ_heart]; rw [Matrix.sum_apply]

@[simp]
theorem 𝒪ₐ_heart_le_succ {n α β} : 𝒪ₐ_heart p n α β ≤ 𝒪ₐ_heart p (n + 1) α β := by
  simp [𝒪ₐ_heart_apply]
  gcongr
  · simp
  · simp
@[gcongr]
theorem 𝒪ₐ_heart_le_apply_of_le {n m α β} (h : n ≤ m) : 𝒪ₐ_heart p n α β ≤ 𝒪ₐ_heart p m α β := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m h ih => grw [ih]; simp
@[gcongr]
theorem 𝒪ₐ_heart_le_of_le {n m} (h : n ≤ m) : 𝒪ₐ_heart p n ≤ 𝒪ₐ_heart p m :=
  fun _ _ ↦ 𝒪ₐ_heart_le_apply_of_le _ h

theorem 𝒜ₐ_eq_Qₐ {n} {g} : 𝒜ₐ⟦~p⟧ n g = Qₐ⟦~p⟧ n g.2.1 g.1 g.2.2 := by rfl

variable [KStar 𝒮] [LawfulKStar 𝒮] [Inhabited Pk[F,N]]

theorem Qₐ_iter_eq' {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    Qₐ⟦~p⟧ n xs = (if xs = [] then (M'⟦~p⟧ n) else ((M'⟦~p⟧ n) * ∑ i ∈ Finset.range ‖xs‖, M⟦~p⟧ (xs[..i + 1]) * Qₐ⟦~p⟧ n (xs[i + 1..])) ) := by
  ext α β
  simp [Qₐ]
  rw [𝒜ₐ_iter_eq]
  simp [𝒪ₐ_heart_eq_M, ihp, ← Finset.sum_mul, Finset.mul_sum, ← Matrix.mul_apply, 𝒜_eq_M, ← mul_assoc, 𝒜ₐ_eq_Qₐ]
  simp [← Finset.mul_sum, mul_assoc, ← Matrix.sum_apply]
  split_ifs <;> rfl
theorem Qₐ_iter_eq {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    Qₐ⟦~p⟧ n xs = M'⟦~p⟧ n * (∑ ys ∈ List.partitions xs, (ys.map (fun y ↦ M⟦~p⟧ y * M'⟦~p⟧ n)).prod) := by
  induction xs using Nat.strongRecMeasure List.length; next xs ih =>
  rcases xs with _ | ⟨α₀, xs⟩
  · simp [List.partitions, ihp]
  simp_all only [List.length_cons]
  ext α β
  have : (∑ x ∈ Finset.range n, M⟦~p⟧ [] ^ x) = M'⟦~p⟧ n := by simp [M', Semantics.sem]
  simp [Qₐ, 𝒜ₐ_iter_nonempty]
  simp [𝒪ₐ_heart_eq_M, ihp, 𝒜_eq_M, 𝒜ₐ_eq_Qₐ, ← Matrix.mul_apply, ← Finset.sum_mul, ← Matrix.sum_apply, Matrix.mul_assoc, ← Matrix.mul_sum, this]
  congr!
  conv => enter [1, 2, _]; rw [ih _ (by simp)]
  simp [← mul_assoc]
  set g := fun y ↦ M⟦~p⟧ y * M'⟦~p⟧ n
  have {y} : M⟦~p⟧ y * M'⟦~p⟧ n = g y := rfl
  simp [this, Finset.mul_sum]
  conv => enter [1, 2, x, 2, i]; rw [← List.prod_cons, ← List.map_cons]
  rw [List.partitions_cons_eq_split]

theorem Qₐ_iter_eq_partitionsFill' {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    Qₐ⟦~p⟧ (n + 1) xs = ∑ ys ∈ List.partitionsFill' xs n, (ys.map M⟦~p⟧).prod := by
  induction xs using Nat.strongRecMeasure List.length; next xs ih =>
  rcases xs with _ | ⟨x, xs⟩
  · simp [Qₐ_iter_eq, ihp, List.partitionsFill']; rfl
  · rw [Qₐ_iter_eq' _ ihp]
    simp
    conv => enter [1, 2, 2, x, 2]; rw [ih _ (by simp)]
    if hxs : xs = [] then
      subst_eqs
      simp
      simp [List.sum_partitionsFill']
      simp [List.partitions', Finset.mul_sum, Finset.sum_mul, M', mul_assoc]
      rw [Finset.sum_comm]
    else
      rw [List.sum_partitionsFill'_cons hxs (by simp)]
      simp
      rw [Finset.sum_range_succ']
      simp
      simp [← Finset.sum_mul, ← Finset.mul_sum, mul_add]
      congr! 1
      simp [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, ← Finset.mul_sum]
      have {ys : List (ℕ × List Pk[F,N])} : (List.map (M⟦~p⟧) (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) ys)).prod = (ys.map (fun x ↦ (M⟦~p⟧ []) ^ x.1 * M⟦~p⟧ x.2)).prod := by
        clear ih hxs
        induction ys with
        | nil => simp
        | cons y ys ih => simp_all [mul_assoc]
      simp [this]
      simp [← List.prod_cons, ← List.map_tail]
      conv =>
        enter [2, 1, 2, x', 1]
        rw [← List.map_cons (f := fun (x : ℕ × List Pk[F,N]) ↦ M⟦~p⟧ [] ^ x.1 * M⟦~p⟧ x.2) (a := ⟨x'.head!.1, x :: x'.head!.2⟩)]
      conv => left; simp [Finset.mul_sum]
      clear ih this
      conv => enter [1, 2, x, 2, i, 2, 1, 3]; rw [← List.singleton_append]
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
          simp [List.sum_partitionsFill', List.partitions', Finset.mul_sum, Finset.sum_mul, M', mul_assoc]
        else
          have ih' := ih hxs (l ++ [x])
          simp at ih'
          simp [ih']; clear ih'
          rw [List.sum_partitions'_cons]
          simp [hxs, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
          congr! 1
          rw [List.sum_partitionsFill']
          simp [M', ← Finset.mul_sum, ← Finset.sum_mul, ← mul_assoc]
          congr! 3 with ls hl
          clear ih hxs hl
          induction ls with simp_all [mul_assoc]

variable [MulLeftMono 𝒮] [MulRightMono 𝒮]

@[simp]
theorem 𝒜ₐ_le_succ {n} : 𝒜ₐ⟦~p⟧ n ≤ 𝒜ₐ⟦~p⟧ (n + 1) := by
  intro ⟨α, xₙ, β⟩
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
  simp [𝒜ₐ_iter_nonempty]
  gcongr
  · omega
  · apply ihₙ; simp
@[gcongr]
theorem 𝒜ₐ_monotone : Monotone 𝒜ₐ⟦~p⟧ := by
  refine monotone_nat_of_le_succ ?_
  simp
@[gcongr]
theorem 𝒜ₐ_apply_monotone {x} : Monotone (𝒜ₐ⟦~p⟧ · x) := by
  refine monotone_nat_of_le_succ fun i ↦ ?_
  apply 𝒜ₐ_monotone; omega

variable [OmegaContinuousNonUnitalSemiring 𝒮]

theorem 𝒜_iter_nonempty {α α₀ β} {xₙ} :
      𝒜⟦~p*⟧ ⟨α, α₀ :: xₙ, β⟩
    = ∑ x ∈ ..=‖xₙ‖, ∑ x_1, ∑ x_2, (ω∑ (x : ℕ), (𝒜⟦~p⟧ ^ x) (α, [], x_2)) * 𝒜⟦~p⟧ (x_2, α₀ :: xₙ[..x], x_1) * 𝒜⟦~p*⟧ (x_1, xₙ[x..], β) := by
  rw [𝒜_def'']
  simp [ι, 𝒪]
  rw [xδ_δ_iter]
  simp [← Matrix.mul_assoc, Matrix.C_mul_B, Matrix.C_mul_R, δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulKStar.kstar_eq_sum]; congr! with i
    induction i generalizing α γ with
    | zero => simp; rfl
    | succ i ih =>
      simp [pow_succ, Matrix.mul_apply, GS.pow_succ', G.concat_apply, GS.splitAtJoined, ih]
      congr
  simp only [crox]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
  calc
    _ = ((𝒪_heart p ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p <⊟ 𝒪_heart p) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ x ∈ Finset.range xₙ.length,
            ∑ x_1,
              ((𝒪_heart p ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: List.take x xₙ) * 𝒪 p ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                      𝒜⟦~p*⟧ (x_1, List.drop x xₙ, β) := by
      rcases xₙ with _ | ⟨α₁, xₙ⟩
      · simp [xδ, Matrix.down]
      congr! with i hi γ hγ
      have {x y : 𝕄[𝟙, 𝟙, 𝒮]} : (x * y) () () = x () () * y () () := by simp [Matrix.mul_apply]
      nth_rw 2 [Matrix.mul_assoc]
      nth_rw 1 [Matrix.mul_assoc]
      simp [this]
      congr
      simp [𝒜_def'', ι, 𝒪, Matrix.C_mul_R]
      rw [xδ_δ_iter]
      simp [Matrix.C_mul_B, Matrix.C_mul_R]
      simp at hi
      split_ifs with hi'
      · omega
      · simp [δ.δ', Option.getD, List.getLast?_drop, hi, hi', List.getLast?_cons]
    _ = ((𝒪_heart p ⊟> (ι p ⊡ δ p)) α α₀ * xδ (δ p) (α₀ :: xₙ) * (𝒪 p <⊟ 𝒪_heart p) ((α₀ :: xₙ).getLast?.getD α) β).down +
          ∑ i ∈ Finset.range xₙ.length,
            ∑ γ,
              (𝒪_heart p * Q⟦~p⟧ (α₀ :: xₙ.take i)) α γ *
                      Q⟦~p*⟧ (List.drop i xₙ) γ β := by
      congr! with i hi γ hγ
      simp only [Finset.mem_range] at hi
      nth_rw 1 [Matrix.mul_apply]
      simp [Q, Semantics.sem.eq_def (sem:=Q), sox, Matrix.sum_mul]
      congr! with ξ hξ
      simp [𝒜_def'']
      simp [xδ, fox, ← Matrix.mul_assoc, Matrix.down]
      congr! 2
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
      simp [Q, Semantics.sem.eq_def (sem:=Q), sox, sox', Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum, Matrix.mul_assoc, mul_assoc]
      rw [Finset.sum_comm]
      congr! 4 with γ hγ ξ hξ
      simp [𝒜_def'']
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
      simp [Q, Semantics.sem.eq_def (sem:=Q)]
    _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart p α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
      simp [Matrix.mul_apply, Finset.sum_mul, Q_eq_𝒜]
    _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
      simp only [ωSum_sum_comm]
      simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, Q_nil_iter_eq_𝒜,
        ← ωSum_mul_right, ← ωSum_sum_comm]
    _ = _ := by simp [ωSum_sum_comm, ωSum_mul_right]

/-- In the limit the automata semantics are equal to the approximate. -/
theorem 𝒜_iter_eq_ωSup_approx {α β} {xₙ} :
    𝒜⟦~p*⟧ ⟨α, xₙ, β⟩ = ωSup ⟨fun n ↦ 𝒜ₐ⟦~p⟧ n ⟨α, xₙ, β⟩, 𝒜ₐ_apply_monotone p⟩ := by
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
    have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
      ext α γ; simp [𝒪_heart, LawfulKStar.kstar_eq_sum]; congr! with i
      induction i generalizing α γ with
      | zero => simp; rfl
      | succ i ih =>
        simp_all
        simp [pow_succ, Matrix.mul_apply, ih, GS.pow_succ', G.concat_apply, GS.splitAtJoined]
        congr
    have 𝒪ₐ_heart_eq {n} : 𝒪ₐ_heart p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
      ext α γ; simp; congr!
    simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, ωSum_nat_eq_ωSup, Semantics.sem,
      𝒪ₐ_heart_eq]
    simp [Matrix.sum_apply]
  · simp [𝒜_iter_nonempty, 𝒜ₐ_iter_nonempty]
    conv => enter [1, 2, x, 2, x_1, 2, x_2, 2]; rw [ihₙ _ (by simp)]
    simp [mul_ωSup, sum_ωSup', ωSum_nat_eq_ωSup, ωSup_mul]
    apply le_antisymm
    · simp
      intro j k
      apply le_ωSup_of_le (j ⊔ k)
      simp
      simp [𝒪ₐ_heart_apply]
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
      simp [𝒪ₐ_heart]
      rw [Matrix.sum_apply]
      congr!
      simp [𝒜_pow_empty]

theorem _root_.ωSup_nat_eq_succ {α : Type*} [OmegaCompletePartialOrder α] (f : Chain α) :
    ωSup f = ωSup ⟨(f <| · + 1), by intro a b hab; simp_all; grw [hab]⟩ := by
  apply le_antisymm
  all_goals simp; intro n; apply le_ωSup_of_le (n + 1); simp
  apply f.mono; omega

theorem 𝒜_iter (ihp : 𝒜⟦~p⟧ = G⟦~p⟧) : 𝒜⟦~p*⟧ = G⟦~p*⟧ := by
  ext ⟨α, xs, β⟩
  rw [𝒜_iter_eq_ωSup_approx]
  simp [G]
  simp [ωSum_nat_eq_ωSup_succ]
  have f (k : ℕ) := congrFun₂ (M_iter_eq_buckets p (n:=k) (xs:=xs)) α β
  simp at f
  conv at f => enter [k, 1]; rw [Matrix.sum_apply]
  simp [Finset.sum_range_succ', f, G_eq_M]
  rw [ωSup_nat_eq_succ]
  simp only [Chain.mk_apply]
  rcases xs with _ | ⟨x, xs⟩
  · simp only [𝒜ₐ_iter_empty, Finset.coe_range, List.buckets_succ_pairwise_disjoint,
    Finset.sum_biUnion]
    simp only [ihp, 𝒪ₐ_heart_eq_M, Finset.sum_range_succ', pow_zero, Matrix.add_apply,
      List.buckets_nil, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Finset.sum_singleton, List.map_replicate, List.prod_replicate, M_skip]
  · simp [Qₐ_iter_eq_partitionsFill', ihp, 𝒜ₐ_eq_Qₐ, M_skip]
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
theorem 𝒜_eq_G (p : RPol[F,N,𝒮]) : 𝒜_proof ~p := by
  induction p with
  | Drop              => exact 𝒜_drop
  | Skip              => exact 𝒜_skip
  | Test t            => exact 𝒜_test
  | Mod π             => exact 𝒜_mod
  | Dup               => exact 𝒜_dup
  | Add p₁ p₂ ih₁ ih₂ => exact 𝒜_add ih₁ ih₂
  | Weight w p ih     => exact 𝒜_weight ih
  | Seq p₁ p₂ ih₁ ih₂ => exact 𝒜_seq ih₁ ih₂
  | Iter p₁ ih        => exact 𝒜_iter p₁ ih

end RPol


variable [KStar 𝒮] [LawfulKStar 𝒮] [Inhabited Pk[F,N]] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

theorem Pol.sem_eq_toRPol_𝒜 (p : Pol[F,N,𝒮]) (π) (h) :
    p.sem ⟨π, []⟩ h = 𝒜⟦~p.toRPol⟧ (π, h.2.reverse, h.1) := by
  rw [← Pol.toRol_sem_eq_sem, RPol.sem_G, RPol.𝒜_eq_G]
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
info: 'WeightedNetKAT.Pol.sem_eq_toRPol_𝒜' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Pol.sem_eq_toRPol_𝒜

end

end WeightedNetKAT
