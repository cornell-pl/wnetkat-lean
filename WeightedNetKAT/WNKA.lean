import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.List.DropRight
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Order.ScottTopology
import WeightedNetKAT.ComputableSemiring
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Language
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.MatrixStar
import WeightedNetKAT.Star

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


namespace List

variable {α β : Type*}

/-! # Products -/

@[simp, grind =]
theorem product_length {as : List α} {bs : List β} :
    (as.product bs).length = as.length * bs.length := by
  simp [product, List.map_const']

attribute [local grind =] pair_mem_product

def products : List (List α) → List (List α)
  | [] => [[]]
  | x::xs => (x.product xs.products).map (fun ⟨a, as⟩ ↦ a :: as)

variable {xs ys : List (List α)}

@[simp, grind =]
theorem products_nil : ([] : List (List α)).products = [[]] := by rfl
@[simp, grind =]
theorem products_length : xs.products.length = (xs.map List.length).prod := by
  fun_induction products with grind
@[simp, grind .]
theorem mem_products_length {x} (h : x ∈ xs.products) : x.length = xs.length := by
  fun_induction products generalizing x with grind

@[grind =, simp]
theorem products_eq_nil : xs.products = [] ↔ [] ∈ xs := by
  grind [List.eq_nil_iff_length_eq_zero, products_length, prod_eq_zero_iff, length_eq_zero_iff]

@[grind =]
theorem mem_products {x} :
    x ∈ xs.products ↔
      x.length = xs.length ∧ ∀ i, (h : i < x.length) → (h' : i < xs.length) → x[i]'h ∈ xs[i]'h'
:= by
  fun_induction products generalizing x with
  | case1 => simp
  | case2 y ys ih =>
    constructor
    · grind
    · simp only [length_cons, mem_map, Prod.exists]; intro h; have := h.right 0; grind [cases List]

theorem singleton_product {β : Type*} {l : List β} {a} :
    ([a] : List α).product l = l.map (⟨a, ·⟩) := by rw [product]; simp
theorem product_singleton {β : Type*} {l : List β} {a : α} :
    l.product [a] = l.map (⟨·, a⟩) := by rw [product]; simp [map_eq_flatMap]

theorem products_append :
    (xs ++ ys).products = (xs.products.product ys.products).map (fun ⟨x, y⟩ ↦ x ++ y) := by
  induction xs with
  | nil =>
    simp only [nil_append, products_nil, singleton_product, map_map]; unfold Function.comp; simp
  | cons x xs ih => simp [products, ih, product, map_flatMap, flatMap_map, flatMap_assoc]; rfl

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
    [((𝒪_heart_n p n ⊟ ι p ⊡ δ p) α β).coe_unique_left, 0]]
where δ' (p : RPol[F,N,𝒮]) (n : ℕ) : 𝒲[Pk[F,N], Pk[F,N], 𝒲[S p, S p, 𝒮]] := δ p + (𝒪 p ⊞ 𝒪_heart_n p n ⊟ ι p ⊡ δ p)

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
  congr! 2
  ext
  simp [box]
  rw [EMatrix.asNMatrix_apply]
  nth_rw 1 [EMatrix.get]
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
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
variable [Inhabited Pk[F,N]] in
theorem xδ_approx_δ_iter {p₁ : RPol[F,N,𝒮]} {α  : Pk[F,N]} {xₙ : List Pk[F,N]} {n} :
      xδ (approx_δ p₁ n) (α :: xₙ)
    = δ[[xδ (approx_δ.δ' p₁ n) (α :: xₙ),0],
        [if xₙ = [] then 0 else ((𝒪_heart_n p₁ n ⊟ ι p₁ ⊡ δ p₁) α xₙ.head! * xδ (approx_δ.δ' p₁ n) xₙ).coe_unique_left,if xₙ = [] then 1 else 0]] := by
  induction xₙ generalizing α with
  | nil => simp only [xδ, S.I, ↓reduceIte, S.δ_identity]
  | cons α₁ xₙ ih => rw [xδ, ih, approx_δ, δ_wProd_δ]; simp [xδ]

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
    · simp only [S, S.I, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, G, GS.mk, GS.ofPks,
      List.cons_append, List.head_cons, List.drop_succ_cons, List.drop_zero, ne_eq, reduceCtorEq,
      not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_cons₂,
      List.dropLast_singleton, List.append_eq_nil_iff, and_false, List.getLast_cons,
      List.getLast_append_of_ne_nil, List.cons_ne_self, List.getLast_singleton, G.ofPk_apply,
      right_eq_ite_iff, forall_exists_index]
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
  simp only [S, wnka_sem_case, ι, Matrix.concrete_id, id_eq, Matrix.smul_mul,
    List.getLastD_eq_getLast?, 𝒪, Matrix.down_smul_left, smul_eq_mul, Countsupp.hMul_apply_left]
  congr! 4
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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.Q_eq_A_sem (p : RPol[F,N,𝒮]) {xs} : Q⟦~p⟧ xs = fun x z ↦ 𝒜⟦~p⟧ ⟨x, xs, z⟩ := by
  ext
  simp [Q, A_sem]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.A_sem_eq_Q (p : RPol[F,N,𝒮]) {xs} {α β} : 𝒜⟦~p⟧ ⟨α, xs, β⟩ = Q⟦~p⟧ xs α β := by
  simp [RPol.Q_eq_A_sem]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.A_sem_eq_G (p : RPol[F,N,𝒮]) (h : Q⟦~p⟧ = M'⟦~p⟧) : 𝒜⟦~p⟧ = G⟦~p⟧ := by
  ext ⟨α, xs, β⟩
  have := congrFun₂ (congrFun h xs) α β
  exact this


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

section

noncomputable instance : HPow (GS F N →c 𝒮) ℕ (GS F N →c 𝒮) where
  hPow s n := (s ♢ ·)^[n] G⟦skip⟧

variable {p p₁ p₂ : RPol[F,N,𝒮]} {n} {α β} {xn}

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [∀ (n : ℕ), LawfulStar N𝒲[n, n, 𝒮]] [Inhabited Pk[F,N]] [Star 𝒮] in
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
    intros _ _ _ _ _ h
    rw [Prod.mk_inj, Prod.mk_inj] at h
    simp_all
  · simp
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [∀ (n : ℕ), LawfulStar N𝒲[n, n, 𝒮]] [Inhabited Pk[F,N]] [Star 𝒮] in
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
    intros _ _ _ _ _ h
    rw [Prod.mk_inj, Prod.mk_inj] at h
    simp_all
    omega
  · simp

theorem GS.concat_assoc {a b c : GS F N →c 𝒮} :
    (a ♢ b ♢ c) = (a ♢ (b ♢ c)) := by
  ext γ
  simp [G, GS.mk, G.concat_apply]
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
  sorry

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
    intros
    rename_i h
    rw [Prod.mk_inj, Prod.mk_inj] at h
    simp_all
    omega
  · simp
theorem GS.pow_succ {n} : (𝒜⟦~p⟧^(n+1)) = (𝒜⟦~p⟧ ♢ 𝒜⟦~p⟧^n : GS F N →c 𝒮) := by
  simp only [HPow.hPow, G, mk, Function.iterate_succ', Function.comp_apply]
theorem GS.pow_succ' {n} : (𝒜⟦~p⟧^(n+1)) = ((𝒜⟦~p⟧^n) ♢ 𝒜⟦~p⟧ : GS F N →c 𝒮) := by
  induction n with
  | zero => simp
  | succ n ih =>
    sorry
theorem GS.pow_add {n m : ℕ} : (𝒜⟦~p⟧^(n + m)) = (𝒜⟦~p⟧^n ♢ 𝒜⟦~p⟧^m : GS F N →c 𝒮) := by
  induction m with
  | zero => simp
  | succ m ih => simp [← add_assoc, GS.pow_succ', ih, GS.concat_assoc]


theorem A_sem_seq (h₁ : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) (h₂ : 𝒜⟦~p₂⟧ = G⟦~p₂⟧) : 𝒜⟦~p₁; ~p₂⟧ = (𝒜⟦~p₁⟧ ♢ 𝒜⟦~p₂⟧) := by
  ext ⟨α, xn, β⟩
  simp [RPol.A_sem_eq_Q, G.concat_apply]
  sorry

theorem A_sem_pow (p : RPol[F,N,𝒮]) {n} : (𝒜⟦~p⟧^n) = 𝒜⟦~(p.iter n)⟧ := by
  induction n with
  | zero =>
    ext ⟨α, xn, β⟩
    simp
    sorry
  | succ n ih =>
    ext ⟨α, xn, β⟩
    simp [GS.pow_succ]
    simp [A_sem_seq sorry sorry]
    simp [ih]

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

notation xs "[.." n "]" => List.take n xs
notation xs "[" n "..]" => List.drop n xs
notation "..=" n => Finset.range (n + 1)
notation "‖" xs "‖" => List.length xs

-- attribute [-simp] G.pow_zero in
-- attribute [-simp] G.pow_one in
theorem iddkkkk
    (p₁ : RPol 𝒮)
    (h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧)
    (α β : Pk[F,N])
    (this : ∀ (x : 𝒲[S.I (↑{♡} : Set _), S p₁, 𝒮]), (@HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p₁, 𝒮] 𝒲[𝟙, S p₁, 𝒮] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (fun x ↦ 1) x : 𝒲[𝟙, S p₁, 𝒮]) = x.coe_unique_left)
    (𝒪_heart_eq' : 𝒪_heart p₁ = ω∑ (m : ℕ), (Q⟦~p₁⟧ ^ m) [])
    (𝒪_heart_eq : ∀ (α β : Pk[F,N]), 𝒪_heart p₁ α β = ω∑ (m : ℕ), (𝒜⟦~p₁⟧ ^ m) (α, [], β))
    (α₀ : Pk[F,N])
    (xₙ : List Pk[F,N])
    (ihₙ : ∀ (y : List Pk[F,N]),
      y.length < (α₀ :: xₙ).length → ∀ (α β : Pk[F,N]), 𝒜⟦~p₁*⟧ (α, y, β) = (ω∑ (i : ℕ), 𝒜⟦~p₁⟧ ^ i) (α, y, β)) :
    ω∑ (n : ℕ),
      ∑ i ∈ Finset.range (xₙ.length + 1),
        ∑ ξ,
          ∑ γ,
            (ω∑ (m : ℕ), (𝒜⟦~p₁⟧ ^ m) (α, [], γ)) * 𝒜⟦~p₁⟧ (γ, α₀ :: List.take i xₙ, ξ) *
              (𝒜⟦~p₁⟧ ^ n) (ξ, List.drop i xₙ, β) =
    ω∑ (m : ℕ) (n : ℕ),
      ∑ ξ,
        ∑ k ∈ Finset.range (xₙ.length + 1 + 1),
          (𝒜⟦~p₁⟧ ^ m) (α, List.take k (α₀ :: xₙ), ξ) * (𝒜⟦~p₁⟧ ^ (n - m)) (ξ, List.drop k (α₀ :: xₙ), β) := by
  simp_all only [S.I, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, List.length_cons,
    Countsupp.ωSum_apply]
  clear ihₙ this h

  rw [ωSum_comm]
  simp [← ωSum_sum_comm, ← ωSum_mul_right]
  rw [ωSum_nat_eq_succ]
  simp
  rw [ωSum_nat_eq_succ]
  simp
  simp [ite_and]
  rw [Finset.sum_range_succ]
  simp
  rw [add_comm]
  rw [ωSum_nat_eq_succ]
  simp

  symm
  rw [ωSum_nat_eq_succ]
  simp
  rw [ωSum_nat_eq_succ]
  simp [ite_and]
  rw [ωSum_nat_eq_succ]
  simp
  rw [add_comm]
  rw [ωSum_nat_eq_succ]
  simp
  rw [ωSum_nat_eq_succ]
  simp [ite_and]
  have : ∀ {f : Pk[F,N] → 𝒮} (a), ∑ (x : Pk[F,N]), f x = f a + ∑ x, if x = a then 0 else f x := by
    intro f a
    sorry
  rw [this β]
  simp
  rw [Finset.sum_range_succ]
  simp
  conv =>
    enter [1, 1, 1, 1]
    -- rw [Finset.sum_ite_eq]
  rw [Finset.sum_eq_sum]



  sorry

  rw [ωSum_comm]
  simp [← ωSum_sum_comm, ← ωSum_mul_right]
  simp [Finset.sum_range_succ' (n:=xₙ.length + 1)]
  set A := G⟦~p₁⟧

  have {n} {f : ℕ → Pk[F,N] → 𝒮} : ∑ x ∈ Finset.range n, ∑ (α : Pk[F, N]), f x α = ∑ (α : Pk[F, N]), ∑ x ∈ Finset.range n, f x α := by rw [Finset.sum_comm]
  simp [this]
  conv => enter [2, 1, _, 1, _, 2, _]; rw [Finset.sum_range_succ']
  simp
  simp [Finset.sum_add_distrib, ωSum_add]
  simp [ωSum_sum_comm]
  have {γ} {ys xs : List Pk[F,N]} (h : xs ≠ []) : (ω∑ (n : ℕ) (m : ℕ), (G⟦~p₁⟧ ^ m) (α, ys, γ) * (G⟦~p₁⟧ ^ (n - m)) (γ, xs, β)) = (ω∑ (n : ℕ) (m : ℕ), (G⟦~p₁⟧ ^ m) (α, ys, γ) * (G⟦~p₁⟧ ^ n) (γ, xs, β)) := by
    nth_rw 1 [ωSum_comm]; nth_rw 2 [ωSum_comm]
    congr with m
    apply ωSum_eq_ωSum_of_ne_one_bij fun ⟨x, hx⟩ ↦ x + m
    · intro ⟨i, hi⟩ ⟨j, hj⟩ h; simp_all
    · simp
      intro i hi
      if m ≤ i then
        use i - m
        simp_all
      else
        simp_all
        have : i - m = 0 := by omega
        simp_all
    · simp
  simp [this]
  simp [Finset.sum_range_succ]
  simp [Finset.sum_add_distrib, ωSum_add]
  simp [ωSum_sum_comm]
  conv =>
    enter [2, 1, 2, x]
    rw [Finset.sum_range_succ]
    rw [← Finset.sum_attach]
    enter [1, 2, y]
    rw [this (by obtain ⟨y, hy⟩ := y; simp at hy; simp; omega)]
  simp
  congr with n
  nth_rw 2 [Finset.sum_comm]
  simp
  simp [← ωSum_mul_right]
  simp [← ωSum_sum_comm, ← ωSum_add]
  induction n with
  | zero =>
    simp [ite_and]
    simp [ωSum_sum_comm]
    rw [Finset.sum_eq_single xₙ.length (by grind) (by simp)]
    rw [Finset.sum_eq_single xₙ.length (by grind) (by simp)]
    simp
    have : ∀ m, (G⟦~p₁⟧ ^ (m + 1)) = (G⟦~p₁⟧ ^ m ♢ G⟦~p₁⟧) := by
      intro m
      induction m with
      | zero => simp [HPow.hPow]
      | succ m ih =>
        simp [ih]
        simp only [HPow.hPow, Function.iterate_succ', Function.comp_apply] at ih ⊢
        simp [← GS.concat_assoc, ih]
    induction xₙ with
    | nil => simp
    | cons x xₙ ih =>
      nth_rw 2 [ωSum_nat_eq_succ]; simp_all
      simp [G.concat_apply]
      nth_rw 2 [ωSum_sum_comm]
      rw [Finset.sum_range_succ']
      have {s : GS F N} {γ} : (s.splitAtJoined 0 γ) = (⟨s.1, [], γ⟩, ⟨γ, s.2⟩) := by
        simp [GS.splitAtJoined]
        split
        simp
      simp [this]
      simp_all

    sorry
    nth_rw 2 [ωSum_nat_eq_succ]; simp_all
    nth_rw 2 [ωSum_nat_eq_succ]; simp_all
    nth_rw 2 [ωSum_nat_eq_succ]; simp_all
    nth_rw 2 [ωSum_nat_eq_succ]; simp_all
    have : ∀ m, (G⟦~p₁⟧ ^ (m + 1)) = (G⟦~p₁⟧ ^ m ♢ G⟦~p₁⟧) := by
      intro m
      induction m with
      | zero => simp [HPow.hPow]
      | succ m ih =>
        simp [ih]
        simp only [HPow.hPow, Function.iterate_succ', Function.comp_apply] at ih ⊢
        simp [← GS.concat_assoc, ih]
    simp [this]
    simp [G.concat_apply]
    congr! 3 with m x
    -- have : (G⟦~p₁⟧ ^ (m + 1)) = (G⟦~p₁⟧ ♢ G⟦~p₁⟧ ^ m) := by
    --   simp_all only [Finset.mem_univ]
    --   induction m with
    --   | zero => simp [HPow.hPow]
    --   | succ m ih =>
    --     simp [ih]; clear ih
    --     simp only [HPow.hPow, Function.iterate_succ', Function.comp_apply]
    simp [G.concat_apply]
    nth_rw 2 [Finset.sum_eq_single 0]
    · simp [GS.splitAtJoined]
    · simp [GS.splitAtJoined]
      rintro (_ | b) _ _ γ
      · contradiction
      · simp_all
    · simp
  | succ n ih =>
    have : ∀ m, (G⟦~p₁⟧ ^ (m + 1)) = (G⟦~p₁⟧ ^ m ♢ G⟦~p₁⟧) := by
      intro m
      induction m with
      | zero => simp [HPow.hPow]
      | succ m ih =>
        simp [ih]
        simp only [HPow.hPow, Function.iterate_succ', Function.comp_apply] at ih ⊢
        simp [← GS.concat_assoc, ih]
    simp_all
    conv => left; simp [G.concat_apply]
    simp [GS.splitAtJoined]
    conv => enter [1, 1, x, 2, i, 2, _, 2, _]; rw [Finset.sum_range_succ']
    simp
    simp [mul_add, Finset.sum_add_distrib, ωSum_add]
    have : ω∑ (m : ℕ),
      ∑ i ∈ Finset.range (xₙ.length + 1),
        ∑ γ₁,
          ∑ γ₀,
            (G⟦~p₁⟧ ^ m) (α, [], γ₀) * G⟦~p₁⟧ (γ₀, α₀ :: List.take i xₙ, γ₁) *
              ∑ γ, (G⟦~p₁⟧ ^ n) (γ₁, [], γ) * G⟦~p₁⟧ (γ, List.drop i xₙ, β) =
      -- ω∑ (m : ℕ),
      --   ∑ i ∈ Finset.range (xₙ.length + 1),
      --     ∑ γ₁,
      --       ∑ γ₀,
      --         (G⟦~p₁⟧ ^ m) (α, [], γ₀) * G⟦~p₁⟧ (γ₀, α₀ :: List.take i xₙ, γ₁) * (G⟦~p₁⟧ ^ n) (γ₁, List.drop i xₙ, β)
        ω∑ (m : ℕ),
          ∑ i ∈ Finset.range (xₙ.length + 1),
            ∑ γ₁,
              ∑ γ₀,
                (G⟦~p₁⟧ ^ m) (α, [], γ₀) * G⟦~p₁⟧ (γ₀, α₀ :: List.take i xₙ, γ₁) * (G⟦~p₁⟧ ^ n) (γ₁, [], γ) * G⟦~p₁⟧ (γ, List.drop i xₙ, β) := by
      sorry
    nth_rw 2 [ωSum_nat_eq_succ]
    simp
    have {x} {α γ β : Pk[F,N]} {xs : List Pk[F,N]} : (G⟦~p₁⟧ ^ (n + 1 - x)) (α, γ::xs, β) = (G⟦~p₁⟧ ^ (n - x + 1)) (α, γ::xs, β) := by
      if x ≤ n then
        rw [Nat.sub_add_comm ‹_›]
      else
        simp_all
        have : n - x = 0 := by omega
        have : n + 1 - x = 0 := by omega
        simp_all
        sorry
  -- let f := fun (xₙ yₙ : List Pk[F,N]) (γ κ : Pk[F,N]) (m : ℕ) ↦ (G⟦~p₁⟧ ^ m) (α, [], γ) * G⟦~p₁⟧ (γ, xₙ, κ) * (G⟦~p₁⟧ ^ n) (κ, yₙ, β)
  sorry

theorem ωSum_offset_with_ωSum {f : ℕ → 𝒮} (hf : f 0 = 0) : ω∑ (n : ℕ), f n = ω∑ (m : ℕ) (n : ℕ), if n < m then f (m + (n - m)) else 0 := by
  rw [ωSum_nat_eq_succ]
  rw [ωSum_nat_eq_succ]
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 5 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf

  ring_nf
  rw [← ωSum_prod']
  apply ωSum_eq_ωSum_of_ne_one_bij fun ⟨⟨m, n⟩, _⟩ ↦ (m + (n - m))
  · intro ⟨⟨m, n⟩, h⟩; simp_all; simp_all; intro m' n' h' heq
    if n ≤ m ∧ n' ≤ m' then
      simp_all
      subst_eqs
      rcases m with _ | m
      · contradiction
      · sorry
    else
      simp_all

  · simp
  · simp


-- #eval (fun (n k m : ℕ) ↦ n + (k - n) - m = k + (n - m - k)) 2 2 3

theorem asdassd (p₁ : RPol[F,N,𝒮]) {α β} {xₙ} :
    ω∑ (n : ℕ), (𝒜⟦~p₁⟧^n) ⟨α, xₙ, β⟩ = ω∑ (m : ℕ) (n : ℕ), if m < n then (𝒜⟦~p₁⟧^((n - m) + m)) ⟨α, xₙ, β⟩ else 0 := by

  rcases xₙ with _ | ⟨x₀, xₙ⟩
  · sorry

  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 2 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 3 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf
  nth_rw 4 [ωSum_nat_eq_succ]; try simp [← add_assoc]; ring_nf

  rw [ωSum_offset_with_ωSum]
  simp [add_comm]
theorem asdassd'' (p₁ : RPol[F,N,𝒮]) {α β} {xₙ} {m} :
    ω∑ (n : ℕ), (𝒜⟦~p₁⟧^(n - m)) ⟨α, xₙ, β⟩ = ω∑ (k : ℕ) (n : ℕ), (𝒜⟦~p₁⟧^(((n - m) - k) + k)) ⟨α, xₙ, β⟩ := by
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · sorry
  rw [ωSum_offset_with_ωSum]
  simp [add_comm]
  congr! 6 with n k
  rw [Nat.sub_sub]
  nth_rw 2 [add_comm]
  rw [← Nat.sub_sub]






theorem asdassd' (p₁ : RPol[F,N,𝒮]) (h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) {α β} {xₙ} :
    ω∑ (n : ℕ), ((𝒜⟦~p₁⟧)^n) ⟨α, xₙ, β⟩ = sorry := by
  simp [asdassd]
  simp [add_comm, GS.pow_add]
  simp [G.concat_apply, GS.splitAtJoined]
  simp [Finset.sum_range_succ']
  simp [ωSum_add, ωSum_sum_comm, ωSum_mul_left]
  simp [← ωSum_add, ← ωSum_sum_comm]
  conv =>
    enter [1, 1, x, 2, 2, y, 2]
    simp [asdassd]
    simp [add_comm, GS.pow_add]
    simp [G.concat_apply, GS.splitAtJoined]
    simp [Finset.sum_range_succ']
    simp [ωSum_add, ωSum_sum_comm, ωSum_mul_left]
    simp [← ωSum_add, ← ωSum_sum_comm]
  simp

  have {m} {γ} : ω∑ (n : ℕ), (𝒜⟦~p₁⟧ ^ (n - m)) (γ, xₙ, β) = ω∑ (n : ℕ), (𝒜⟦~p₁⟧ ^ n) (γ, xₙ, β) := by
    apply ωSum_eq_ωSum_of_ne_one_bij fun ⟨x, _⟩ ↦ x + m
    · intro ⟨_, _⟩; grind
    · intro x; simp_all
      sorry

  simp [this]
  have {γ} {y} {c} [Decidable c] : ω∑ (m : ℕ) (n : ℕ), (𝒜⟦~p₁⟧ ^ (n - m)) (γ, xₙ[y..], β) = (ω∑ (n : ℕ), (𝒜⟦~p₁⟧ ^ (n + 1)) (γ, xₙ[y..], β)) + ω∑ (m : ℕ), (𝒜⟦~p₁⟧ ^ 0) (γ, xₙ[y..], β) := by

    simp [← ωSum_add]
    nth_rw 2 [ωSum_offset_with_ωSum]
    simp [GS.pow_add]

  conv =>
    enter [1, 1, x, 1, 2, y, 2, y, 2]
    rw [ωSum_offset_with_ωSum]

    simp

  conv =>
    enter [1, 1, x, 2, 2, x, 2]
    rw [asdassd _ h]
    simp [add_comm, GS.pow_add]
    simp [G.concat_apply, GS.splitAtJoined]
    simp [Finset.sum_range_succ' (n:=xₙ.length + 1)]
    simp [ωSum_add, ωSum_sum_comm, ωSum_mul_left]
    simp [← ωSum_add, ← ωSum_sum_comm]
  simp [this]
  simp [← ωSum_add, ← ωSum_sum_comm]
  sorry


noncomputable def currentGoal (p₁ : RPol[F,N,𝒮]) α xₙ β := ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p₁⟧ ⟨γ, xₙ.take i, ξ⟩ * (𝒜⟦~p₁⟧^n) ⟨ξ, List.drop i xₙ, β⟩

theorem Q_star_eq_ωSum_Q_iter_first (p₁ : RPol[F,N,𝒮]) (h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) {α β} {xₙ} :
    𝒜⟦~p₁*⟧ ⟨α, xₙ, β⟩ = currentGoal p₁ α xₙ β := by

  -- TODO: require that xₘ is nonempty
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rw [A_sem_cases]
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
  have 𝒪_heart_eq : ∀ α β, 𝒪_heart p₁ α β = ω∑ (m : ℕ), (𝒜⟦~p₁⟧^m) ⟨α, [], β⟩ := by
    simp [𝒪_heart_eq]
    simp [RPol.Q_eq_A_sem, A_sem_pow]
    intro α β
    congr with m
    induction m with
    | zero => simp [RPol.A_sem]; rw [RPol.wnka_sem_skip]; simp; rfl
    | succ m ih =>
      conv => right; simp [RPol.wnka_sem_seq, h, RPol.A_sem]
      rw [RPol.wnka_sem_seq]
      · sorry
      · simp [← h]; rfl
      · sorry
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · replace 𝒪_heart_eq := 𝒪_heart_eq α β
    simp at 𝒪_heart_eq
    simp [Matrix.coe_unique_left, Q, Matrix.down, ← 𝒪_heart_eq]
    simp [Matrix.mul_apply]
    simp [currentGoal]
    simp [𝒪_heart_eq]
    sorry
  · simp
    simp [crox]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
    calc
      _ = ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀ * xδ (δ p₁) (α₀ :: xₙ) * (𝒪 p₁ ⊟' 𝒪_heart p₁) ((α₀ :: xₙ).getLast?.getD α) β).down +
            ∑ x ∈ Finset.range xₙ.length,
              ∑ x_1,
                ((𝒪_heart p₁ ⊟ ι p₁ ⊡ δ p₁) α α₀ * xδ (δ p₁) (α₀ :: List.take x xₙ) * 𝒪 p₁ ((α₀ :: xₙ)[x]?.getD default) x_1).down *
                        𝒜⟦~p₁*⟧ (x_1, List.drop x xₙ, β) := by
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
      _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart p₁ α γ * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p₁*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [Matrix.mul_apply, Finset.sum_mul, RPol.Q_eq_A_sem]
      _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p₁*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [← ωSum_mul_left, ωSum_sum_comm]
        simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
      _ = _ := by
        simp [ωSum_mul_left, ωSum_sum_comm, currentGoal, List.drop_cons]
        congr!
        rw [ihₙ _ (by simp; omega)]
        simp

theorem Q_star_eq_ωSum_Q_iter (p₁ : RPol[F,N,𝒮]) (h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) : 𝒜⟦~p₁*⟧ = ω∑ (i : ℕ), 𝒜⟦~p₁⟧^i := by
  ext ⟨α, xₙ, β⟩

  -- TODO: require that xₘ is nonempty
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rw [A_sem_cases]
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
  have 𝒪_heart_eq : ∀ α β, 𝒪_heart p₁ α β = ω∑ (m : ℕ), (𝒜⟦~p₁⟧^m) ⟨α, [], β⟩ := by
    simp [𝒪_heart_eq]
    simp [RPol.Q_eq_A_sem, A_sem_pow]
    intro α β
    congr with m
    induction m with
    | zero => simp [RPol.A_sem]; rw [RPol.wnka_sem_skip]; simp; rfl
    | succ m ih =>
      conv => right; simp [RPol.wnka_sem_seq, h, RPol.A_sem]
      rw [RPol.wnka_sem_seq]
      · sorry
      · simp [← h]; rfl
      · sorry
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · replace 𝒪_heart_eq := 𝒪_heart_eq α β
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
                        𝒜⟦~p₁*⟧ (x_1, List.drop x xₙ, β) := by
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
      _ = ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, 𝒪_heart p₁ α γ * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p₁*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [Matrix.mul_apply, Finset.sum_mul, RPol.Q_eq_A_sem]
      _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p₁*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [← ωSum_mul_left, ωSum_sum_comm]
        simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
      _ = ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * (𝒜⟦~p₁⟧^n) ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [ωSum_mul_left, ωSum_sum_comm]
        congr!
        rw [ihₙ _ (by simp; omega)]
        simp
      -- _ = ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1 + 1), ∑ ξ, ∑ γ, (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p₁⟧ ⟨γ, (α₀ :: xₙ).take i, ξ⟩ * (𝒜⟦~p₁⟧^n) ⟨ξ, List.drop i (α₀ :: xₙ), β⟩ := by
      --   simp [ωSum_mul_left, ωSum_sum_comm]
      --   nth_rw 2 [Finset.sum_range_succ']
      --   simp
      --   have : ∀ (m : ℕ) ξ, ∑ γ, (𝒜⟦~p₁⟧ ^ m) (α, [], γ) * 𝒜⟦~p₁⟧ (γ, [], ξ) = (𝒜⟦~p₁⟧ ^ (m + 1)) (α, [], ξ) := by
      --     intro m ξ
      --     simp [GS.pow_succ', G.concat_apply, GS.splitAtJoined]
      --   conv =>
      --     right
      --     right
      --     arg 2; ext
      --     rw [← ωSum_sum_comm]
      --     arg 1; ext
      --     rw [← Finset.sum_mul]
      --     left
      --     rw [this]

      --   sorry
      -- _ = ω∑ (n : ℕ), ω∑ (m : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, ((Q⟦~p₁⟧ [] ^ m) α γ * Q⟦~p₁⟧ (α₀ :: List.take k xₙ) γ ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      --   simp [Matrix.mul_apply]
      --   simp [← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply, Matrix.mul_assoc]
      -- -- _ = ω∑ (n : ℕ) (m : ℕ), ∑ x ∈ Finset.range (xₙ.length + 1), ∑ x_1, ∑ x_2, G⟦~(p₁.iter m)⟧ (α, [], x_2) * G⟦~p₁⟧ (x_2, α₀ :: List.take x xₙ, x_1) * G⟦~(p₁.iter n)⟧ (x_1, List.drop x xₙ, β) := by
      -- --   simp [h]
      -- --   simp [M']
      -- -- _ = ω∑ (n : ℕ), ω∑ (m : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      -- --   simp [← Finset.sum_mul]
      -- --   congr! with n m k hk ξ hξ
      -- --   · sorry
      -- --   · sorry
      -- -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      -- --   sorry
      -- -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, /- -/ ((∑ γ, ω∑ (m : ℕ), (Q⟦~p₁⟧ [] ^ m) α γ * Q⟦~p₁⟧ (α₀ :: List.take k xₙ) γ ξ) /- -/ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      -- --   sorry
      -- -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), ∑ ξ, /- -/ ((Q⟦~p₁⟧ (α₀ :: List.take k xₙ) α ξ)                                  /- -/ * (Q⟦~p₁⟧ (List.drop k xₙ) ^ n) ξ β) := by
      -- --   -- congr!
      -- --   sorry

      -- -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1), (Q⟦~p₁⟧ (α₀ :: List.take k xₙ) * Q⟦~p₁⟧ (List.drop k xₙ) ^ n) α β := by
      -- --   -- simp [← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul, Matrix.mul_apply]
      -- --   sorry
      -- --   simp [h]
      -- --   unfold M'
      -- --   simp
      -- --   sorry
      --   -- simp [← ωSum_mul_left, ωSum_sum_comm]
      --   -- simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1 + 1), ∑ ξ, (Q⟦~p₁⟧ (List.take k (α₀ :: xₙ)) α ξ * (Q⟦~p₁⟧ (List.drop k (α₀ :: xₙ)) ^ n) ξ β) := by
      --   -- simp [h]
      --   -- simp [M']
      --   conv =>
      --     right
      --     arg 1; ext n
      --     rw [Finset.sum_range_succ']
      --   simp
      --   conv =>
      --     left
      --     arg 1; ext n
      --     arg 1; ext m
      --     arg 2; ext m
      --     rw [Finset.sum_comm]
      --   conv =>
      --     left
      --     arg 1; ext n
      --     arg 1; ext m
      --     rw [Finset.sum_comm]

      --   simp [mul_assoc, ← Finset.mul_sum]
      --   sorry
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
      _ = ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (ω∑ (m : ℕ), (𝒜⟦~p₁⟧^m) ⟨α, [], γ⟩) * 𝒜⟦~p₁⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * (𝒜⟦~p₁⟧^n) ⟨ξ, List.drop i xₙ, β⟩ := by
        rw [ωSum_comm]
        simp [ωSum_sum_comm, ωSum_mul_right]
      -- _ = ω∑ (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1 + 1), ∑ ξ, (𝒜⟦~p₁⟧ (α, List.take k (α₀ :: xₙ), ξ) * (𝒜⟦~p₁⟧^n) (ξ, List.drop k (α₀ :: xₙ), β)) := by

      --   congr with n
      --   nth_rw 2 [Finset.sum_range_succ']
      --   simp
      --   nth_rw 2 [Finset.sum_range_succ]
      --   simp
      --   -- have :
      --   --     ∀ β, 𝒜⟦~p₁⟧ (α, [], β) = ω∑ (m : ℕ), (𝒜⟦~p₁⟧ ^ (m + 1)) (α, [], β) := by
      --   --   intro β
      --   --   simp [ωSum_nat_eq_ωSup]
      --   --   apply le_antisymm
      --   --   · simp
      --   --   · simp
      --   --     intro i
      --   --     induction i with
      --   --     | zero => simp
      --   --     | succ i ih =>
      --   --       simp [Finset.sum_range_succ']
      --   --       simp [GS.pow_succ']
      --   -- nth_rw 1 [ωSum_nat_eq_succ]
      --   -- simp
      --   -- rw [ωSum_comm]
      --   -- simp [← ωSum_add]
      --   -- conv => left; simp [ωSum_sum_comm]
      --   -- simp [← Finset.sum_mul]
      --   -- have : ∀ xn β, (∑ i, G⟦skip⟧ (α, [], i) * 𝒜⟦~p₁⟧ (i, xn, β)) = 𝒜⟦~p₁⟧ (α, xn, β) := by
      --   --   intro xn β
      --   --   rw [Finset.sum_eq_single α]
      --   --   · simp [G, GS.mk]
      --   --   · simp [G, GS.mk]; grind
      --   --   · simp
      --   -- simp [this]
      --   -- simp [← Finset.sum_add_distrib]
      --   -- simp [ωSum_mul_right]
      --   sorry
      -- _ = ω∑ (n : ℕ), (𝒜⟦~p₁⟧ ♢ 𝒜⟦~p₁⟧^n : GS F N →c 𝒮) ⟨α, α₀ :: xₙ, β⟩ := by
      --   simp [G.concat_apply, GS.splitAtJoined]

      _ = ω∑ (m : ℕ) (n : ℕ), ∑ ξ, ∑ k ∈ Finset.range (xₙ.length + 1 + 1), ((𝒜⟦~p₁⟧^m) (α, List.take k (α₀ :: xₙ), ξ) * (𝒜⟦~p₁⟧^(n - m)) (ξ, List.drop k (α₀ :: xₙ), β)) := by

        rw [iddkkkk] <;> assumption
        -- sorry
      _ = ω∑ (m : ℕ) (n : ℕ), ∑ k ∈ Finset.range (xₙ.length + 1 + 1), ∑ ξ, ((𝒜⟦~p₁⟧^m) (α, List.take k (α₀ :: xₙ), ξ) * (𝒜⟦~p₁⟧^(n - m)) (ξ, List.drop k (α₀ :: xₙ), β)) := by
        congr!; rw [Finset.sum_comm]
      _ = ω∑ (m : ℕ) (n : ℕ), (𝒜⟦~p₁⟧^((n - m) + m)) ⟨α, α₀ :: xₙ, β⟩ := by
        congr! with m n
        nth_rw 3 [add_comm]
        suffices (𝒜⟦~p₁⟧ ^ (m + (n - m))) = ((𝒜⟦~p₁⟧ ^ m) ♢ (𝒜⟦~p₁⟧ ^ (n - m))) by
          simp [this, G.concat_apply, GS.splitAtJoined]
        sorry
      _ = ω∑ (n : ℕ), (𝒜⟦~p₁⟧^n) ⟨α, α₀ :: xₙ, β⟩ := by
        have : (𝒜⟦~p₁⟧ ^ 0) (α, α₀ :: xₙ, β) = 0 := by simp [G, GS.mk]; grind
        -- OK
        sorry
        -- OLD BEGIN
        -- nth_rw 2 [ωSum_nat_eq_succ]
        -- have : G⟦skip⟧ (α, α₀ :: xₙ, β) = (0 : 𝒮) := sorry
        -- simp [this, GS.pow_succ]
        -- OLD END

        -- have : ∀ n, (Q⟦~p₁⟧ (α₀ :: xₙ) ^ n) = sorry := by
        --   sorry
        -- nth_rw 2 [ωSum_nat_eq_succ]
        -- simp [pow_succ', Matrix.mul_apply]
        -- simp [ωSum_sum_comm, ωSum_mul_left]
        -- rw [Finset.sum_range_succ']
        -- simp

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

theorem 𝒜_star_eq_star_𝒜 (p₁ : RPol[F,N,𝒮]) (h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧) {xₙ} : 𝒜⟦~p₁*⟧ xₙ = (𝒜⟦~p₁⟧ xₙ)^* := by
  rw [Q_star_eq_ωSum_Q_iter _ h]; sorry -- simp [LawfulStar.star_eq_sum]
theorem Q_star_eq_star_Q (p₁ : RPol[F,N,𝒮]) (h : Q⟦~p₁⟧ = M'⟦~p₁⟧) {xₙ} : Q⟦~p₁*⟧ xₙ = (Q⟦~p₁⟧ xₙ)^* := by
  -- TODO
  sorry
  -- replace h : 𝒜⟦~p₁⟧ = G⟦~p₁⟧ := sorry
  -- rw [Q_star_eq_ωSum_Q_iter _ h]; simp [LawfulStar.star_eq_sum]

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


variable (p p' : RPol[F,N,𝒮]) (h : 𝒜⟦~p⟧ = G⟦~p⟧)

def RPol.iterLe (p : RPol[F,N,𝒮]) : ℕ → RPol[F,N,𝒮]
  | 0 => wnk_rpol {skip}
  | n+1 => p.iterLe n + p^(n + 1)
@[simp]
theorem RPol.iterLe_zero : p.iterLe 0 = wnk_rpol {skip} := by
  rfl
@[simp]
theorem RPol.iterLe_one : p.iterLe 1 = wnk_rpol {skip} + wnk_rpol {~p; skip} := by
  simp [iterLe, instHAddRPol]; rfl
@[simp]
theorem RPol.iterLe_succ {n} : p.iterLe (n + 1) = p.iterLe n + p^(n + 1) := by
  induction n with
  | zero => simp; rfl
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
  simp only [Matrix.down, Matrix.zero_mul, ↓reduceIte, Matrix.mul_zero, add_zero, S.I,
    Matrix.mul_one, zero_add, PUnit.default_eq_unit, Matrix.add_apply, Matrix.zero_apply,
    Matrix.mul_apply, Finset.univ_unique, Set.default_coe_singleton, Pi.one_apply, Matrix.up_apply,
    one_mul, Finset.sum_const, Finset.card_singleton, one_smul]
theorem 𝒜_iter_nonempty {α α₀ β} {xₙ} : 𝒜⟦~p*⟧ ⟨α, α₀ :: xₙ, β⟩ = ∑ x ∈ ..=‖xₙ‖, ∑ x_1, ∑ x_2, (ω∑ (x : ℕ), (𝒜⟦~p⟧ ^ x) (α, [], x_2)) * 𝒜⟦~p⟧ (x_2, α₀ :: xₙ[..x], x_1) * 𝒜⟦~p*⟧ (x_1, xₙ[x..], β) := by
  rw [A_sem_cases]
  simp [approx_𝒜]
  simp [ι, 𝒪, approx_ι, approx_𝒪]
  rw [xδ_δ_iter]
  simp
  rw [ι_wProd_δ, ι_wProd_𝒪]
  simp
  have : ∀ (x : 𝒲[S.I {♡}, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  simp [δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr!
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
      have : ∀ (x : 𝒲[S.I {♡}, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
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
    _ = _ := by
      simp [ωSum_mul_left, ωSum_sum_comm, ωSum_mul_right]

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
      · simp [approx_δ.δ', List.head!_eq_head?, Option.getD_default_eq_iget, List.getLast?_drop, hi, hi', List.getLast?_cons]
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
    -- _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xₙ, β⟩ := by
    --   simp only [ωSum_sum_comm]
    --   simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, ← ωSum_mul_right,
    --     ← ωSum_sum_comm]
    --   congr!
    --   sorry
    -- _ = ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * (𝒜⟦~p⟧^n) ⟨ξ, List.drop i xₙ, β⟩ := by
    --   simp [ωSum_mul_left, ωSum_sum_comm]
    --   congr!
    --   rw [ihₙ _ (by simp; omega)]
    --   simp
    -- _ = _ := by
    --   simp [ωSum_mul_left, ωSum_sum_comm, ωSum_mul_right]

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
  simp [𝒪_heart_n]; repeat rw [Finset.sum_apply]
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
  · apply ihₙ; simp; omega
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
      ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr!
    have 𝒪_heart_n_eq {n} : 𝒪_heart_n p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
      ext α γ; simp; congr!
    simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, ωSum_nat_eq_ωSup,
      𝒪_heart_n_eq]
    congr! 3 with n
    rw [Finset.sum_apply, Finset.sum_apply]
  · simp [𝒜_iter_nonempty, approx_𝒜_iter_nonempty]
    conv => enter [1, 2, x, 2, x_1, 2, x_2, 2]; rw [ihₙ _ (by simp; omega)]
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
      rw [Finset.sum_apply, Finset.sum_apply]
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

theorem sum_G_iter_eq {n α β xₙ} : ∑ x ∈ Finset.range n, G⟦~(p.iter x)⟧ (α, xₙ, β) = sorry := by
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · sorry
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ]
    simp [G, G.concat_apply, GS.splitAtJoined, Finset.mul_sum]
    rcases xₙ with _ | ⟨α₁, xₙ⟩
    · simp [Finset.sum_range_succ, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← Finset.sum_add_distrib]
    · rcases xₙ with _ | ⟨α₂, xₙ⟩
      ·
        -- simp [Finset.sum_range_succ, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← Finset.sum_add_distrib]
        let Q' xs := fun a b ↦ G⟦~p⟧ ⟨a, xs, b⟩
        have : ∀ xs a b, G⟦~p⟧ ⟨a, xs, b⟩ = Q' xs a b := by intros; rfl
        simp [this]
        simp [Finset.sum_range_succ, ← Finset.mul_sum, ← Finset.sum_mul, ← Matrix.mul_apply, mul_assoc, ← Matrix.add_apply, Matrix.mul_add, this]
        simp [← add_assoc, ← Matrix.mul_assoc, ← Matrix.add_apply]

      · rcases xₙ with _ | ⟨α₂, xₙ⟩
        · simp [Finset.sum_range_succ, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← Finset.sum_add_distrib]
        · rcases xₙ with _ | ⟨α₂, xₙ⟩
          · simp [Finset.sum_range_succ, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← Finset.sum_add_distrib]
  sorry

theorem approx_𝒜_eq_sum_G {n} {α β} {xₙ} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) (h : ‖xₙ‖ < n) :
    approx_𝒜 p n (α, xₙ, β) = ∑ x ∈ Finset.range n, G⟦~(p.iter x)⟧ (α, xₙ, β) := by
  rcases n with _ | _ | _ | n
  · rcases xₙ with _ | _
    · simp_all
    · simp_all
  · rcases xₙ with _ | _
    · simp_all [𝒪_heart_n]; rfl
    · simp_all
  · rcases xₙ with _ | ⟨x, _ | ⟨y, _ | ⟨_, z | _⟩⟩⟩
    · simp_all [𝒪_heart_n, Finset.sum_range_succ]; rfl
    · simp_all [approx_𝒜_iter_nonempty, 𝒪_heart_n, Finset.sum_range_succ]
      simp [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_add]
      have {α} {f : Pk[F, N] → 𝒮} : (∑ i, (1 : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) α i * f i) = f α := sorry
      have {β} {f : Pk[F, N] → 𝒮} : (∑ i, f i * (1 : 𝒲[Pk[F,N], Pk[F,N], 𝒮]) i β) = f β := sorry
      simp_all
    · simp_all [approx_𝒜_iter_nonempty]
    · simp_all [approx_𝒜_iter_nonempty]
    · simp_all [approx_𝒜_iter_nonempty]
  -- induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  -- rcases xₙ with _ | ⟨α₀, xₙ⟩
  -- · simp [𝒪_heart_n_apply]
  --   clear ihₙ
  --   congr with i
  --   induction i generalizing α with
  --   | zero => simp; rfl
  --   | succ i ih =>
  --     simp; rw [pow_succ']
  --     simp [G.concat_apply, G, GS.splitAtJoined, ih, Matrix.mul_apply, ihp]
  --     congr
  -- · simp [approx_𝒜_iter_nonempty]
  --   conv => enter [1, 2, i, 2, ξ, 2, γ, 2]; rw [ihₙ _ (by simp; omega) (by simp_all; omega)]
  --   clear ihₙ
  --   simp [𝒪_heart_n_apply]
  --   simp [Finset.sum_mul, Finset.mul_sum]
  --   induction n with
  --   | zero => simp
  --   | succ n ih =>
  --     nth_rw 2 [Finset.sum_range_succ']
  --     simp
  --     rcases n with _ | _ | _ | n
  --     · simp_all
  --     · simp_all
  --       simp [Finset.sum_range_succ, ite_and]
  --       rw [Finset.sum_comm]
  --       rw [Finset.sum_eq_single β (by simp; grind) (by simp)]
  --       rw [Finset.sum_comm]
  --       simp [Finset.sum_add_distrib]
  --       rw [Finset.sum_eq_single α (by simp; grind) (by simp)]
  --       rw [Finset.sum_eq_single α (by simp; grind) (by simp)]
  --       rw [Finset.sum_eq_single α (by simp; grind) (by simp)]
  --       rw [Finset.sum_eq_single α (by simp; grind) (by simp)]
  --       rw [Finset.sum_eq_single α (by simp; intro b h; sorry) (by simp)]
  --       simp
  --       rcases xₙ with _ | _
  --       · simp_all
  --       · simp
  --       rw [Finset.sum_eq_zero]
  --       · simp
  --       · simp
  --         rcases xₙ with _ | _
  --         · simp_all

  --         · simp_all; omega


-- f(1, 1) = 1
-- f(2, 1) = 0 + 1 = 1 + 0
-- f(3, 1) = 0 + 0 + 1 = 0 + 1 + 0 = 1 + 0 + 0
-- f(1, 2) = 2
-- f(2, 2) = 0 + 2 = 1 + 1 = 2 + 0
-- f(2, 3) = 0 + 0 + 2 = 0 + 1 + 1 = 0 + 2 + 0

-- f(2, 3) = 0 + f(2, 2) = 1 + f(1, 2) = 2 + f(0, 2)

noncomputable def Z (n m : ℕ) : Finset (List ℕ) :=
  match m with
  | 0 => {}
  | 1 => {[n]}
  | m+1 => (Finset.range (n + 1)).biUnion fun (i : ℕ) ↦ (Z (n - i) m).image (i :: ·)

noncomputable def Y (n m : ℕ) : List (List ℕ) :=
  match m with
  | 0 => []
  | 1 => [[n]]
  | m+1 => (List.range (n + 1)).flatMap fun (i : ℕ) ↦ (Y (n - i) m).map (i :: ·)

theorem Y_nodup {n m} : (Y n m).Nodup := by
  induction m generalizing n with
  | zero => simp [Y]
  | succ m ih =>
    rcases m with _ | m
    · simp [Y]
    · simp [Y, List.nodup_flatMap]
      constructor
      · simp [List.nodup_map_iff_inj_on, ih]
      · have {n} : (List.range (n + 1)) = 0 :: (List.range n).map (· + 1) := by
          ext; simp [List.range_succ]; grind
        simp [this, List.pairwise_map]
        constructor
        · intro i hi; simp [List.disjoint_left]
        · simp [List.disjoint_left]
          induction n with simp
          | succ n ih =>
            simp [this, List.pairwise_map, ih]

theorem mem_Z_iff_mem_Y {x m n} : x ∈ Z n m ↔ x ∈ Y n m := by
  induction m generalizing n x with
  | zero => simp [Z, Y]
  | succ m ih =>
    rcases m with _ | m
    · simp [Z, Y]
    · simp [Z, Y, ih]

theorem Y_complete {n m} {xs : List ℕ} :
    xs ∈ Y n m ↔ xs ≠ [] ∧ xs.length = m ∧ xs.sum = n := by
  constructor
  · induction m generalizing n xs with
    | zero => simp +contextual [Y]
    | succ m ih =>
      rcases m with _ | m
      · simp_all [Y]
      · simp_all [Y]
        rintro i hi l hl ⟨_⟩
        simp
        specialize ih hl
        grind
  · rintro ⟨_, ⟨_⟩, ⟨_⟩⟩
    induction xs with
    | nil => simp_all
    | cons x xs ih =>
      rcases xs with _ | _
      · simp [Y]
      · simp_all [Y]; omega

theorem Z_complete_aux {n m} :
    Z n m = {xs | xs ≠ [] ∧ xs.length = m ∧ xs.sum = n} := by
  ext xs; simp [mem_Z_iff_mem_Y, Y_complete]
noncomputable instance {m n} : Fintype ↑{xs : List ℕ | xs ≠ [] ∧ ‖xs‖ = m ∧ xs.sum = n} := by
  simp [← Z_complete_aux]
  exact (Z n m).fintypeCoeSort
theorem Z_complete {n m} :
    Z n m = {xs | xs ≠ [] ∧ xs.length = m ∧ xs.sum = n}.toFinset := by
  ext xs; simp [mem_Z_iff_mem_Y, Y_complete]

@[simp] theorem Z_right_zero {n} : Z n 0 = ∅ := by simp [Z]
@[simp] theorem Z_right_one {n} : Z n 1 = {[n]} := by simp [Z]

example {Q} : Z 3 3 = Q := by
  simp [Z_complete]


noncomputable def X {α : Type*} [DecidableEq α] (n : ℕ) (xs : List α) : Finset (List (List α)) :=
  Z xs.length n
    -- |>.image fun idxs ↦ idxs.foldl (fun ⟨rem, acc⟩ i ↦ ⟨rem.drop i, acc ++ [rem.take i]⟩) (xs, [])
    |>.image fun idxs ↦ idxs.foldr (fun i ⟨rem, acc⟩ ↦ ⟨rem.drop i, acc ++ [rem.take i]⟩) (xs, [])
    |>.2

example {α β γ δ : ℕ} {Q} : X 3 [α, β, γ] = Q := by
  simp [X, mul_add, ← mul_assoc, ← add_assoc, add_mul, Z, List.range_succ, Finset.range_add_one]
  sorry

theorem X_complete_aux {α : Type*} [DecidableEq α] {n} {l : List α} :
    X n l = {xs : List (List α) | xs ≠ [] ∧ xs.length = n ∧ xs.flatten = l} := by
  sorry
  -- ext xs
  -- simp
  -- simp [X]
  -- simp [Z_complete]
  -- constructor
  -- · simp_all
  --   rintro ys h ⟨_⟩ h' h''
  --   contrapose h''
  --   apply List.foldrRecOn (op:=(fun i x ↦ (x.1[i..], x.2 ++ [x.1[..i]]))) (motive:=fun q ↦ ¬q.2 = xs) (l:=ys) (b:=(l, []))
  --   · simp_all
  --     contrapose h''
  --     simp_all
  --   · contrapose h''
  --     simp_all
  --     obtain ⟨g, f, _, n, hn, ⟨_⟩⟩ := h''
  --     simp_all
  -- · simp_all
  --   rintro _ ⟨_⟩ ⟨_⟩
  --   simp_all
noncomputable instance {α : Type*} [DecidableEq α] {n} {l} : Fintype ↑{xs : List (List α) | xs ≠ [] ∧ ‖xs‖ = n ∧ xs.flatten = l} := by
  rw [← X_complete_aux]
  exact FinsetCoe.fintype (X n l)
theorem X_complete {α : Type*} [DecidableEq α] {n} {l : List α} :
    X n l = {xs : List (List α) | xs ≠ [] ∧ xs.length = n ∧ xs.flatten = l}.toFinset := by
  simp [← X_complete_aux]

@[simp]
theorem X_zero {α : Type*} [DecidableEq α] {xs : List α} : X 0 xs = {} := by simp [X, Z]
@[simp]
theorem X_one {α : Type*} [DecidableEq α] {xs : List α} : X 1 xs = {[xs]} := by simp [X, Z]
theorem X_nil {α : Type*} [DecidableEq α] {m} : X m ([] : List α) = if m = 0 then {} else {List.replicate m []} := by
  ext xs; simp [X_complete]
  constructor
  · simp_all
    rintro h ⟨_⟩ h'
    split_ifs
    · simp_all
    simp only [Finset.mem_singleton]
    apply List.ext_getElem
    · simp
    · simp_all
      intro i hi
      specialize h' xs[i]
      grind
  · split_ifs
    · simp
    · simp_all

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

theorem G_iter_eq_ωSup_approx' {α β} {xₙ} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    G⟦~p*⟧ ⟨α, xₙ, β⟩ = ω∑ n, ∑ xs ∈ X n xₙ, (xs.map (G' p)).prod α β := by
  simp [G]
  congr with n
  induction n generalizing xₙ α β with
  | zero => simp [X, Z]; sorry
  | succ n ih =>
    -- simp [X_complete]
    simp [G, G.concat_apply, GS.splitAtJoined]
    symm at ihp
    simp_all [G_eq_G', ← Matrix.mul_apply, ← Matrix.sum_apply]
    sorry
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
theorem A'_iter_two_nil (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 2 [] = 1 + G' p [] := by
  ext; simp [A', 𝒪_heart_n_eq_G', ihp, Finset.sum_range_succ]
theorem A'_iter_two_single {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 2 [α₀] = G' p [α₀] + G' p [] * G' p [α₀] + G' p [α₀] * G' p [] + G' p [] * G' p [α₀] * G' p [] := by
  ext; simp [A', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
  simp [add_assoc]

noncomputable def G'' (n : ℕ) := ∑ i ∈ Finset.range n, (G' p [])^i
@[simp] theorem G''_zero : G'' p 0 = 0 := by simp [G'']
theorem G''_succ {n} : G'' p (n + 1) = G'' p n + (G' p [])^n := by simp [G'', Finset.sum_range_succ]
theorem G''_succ' {n} : G'' p (n + 1) = (G' p [])^n + G'' p n := by simp [G'', Finset.sum_range_succ, add_comm]

@[simp]
theorem A'_iter_nil {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n [] = G'' p n := by
  ext; simp [A', 𝒪_heart_n_eq_G', ihp, G'']

def List.partitions {α : Type*} [DecidableEq α] (xs : List α) : Finset (List (List α)) :=
  match xs with
  | [] => {[]}
  | x::xs =>
    (List.partitions xs).biUnion fun ys ↦
      match ys with
      | [] => {[[x]]}
      | y::ys => {(x::y)::ys, [x]::y::ys}


@[simp]
theorem List.partitions_nil {α : Type*} [DecidableEq α] : List.partitions ([] : List α) = {[]} := by rfl

theorem List.mem_partitions_iff {α : Type*} [DecidableEq α] {xs : List α} {ys} :
    ys ∈ List.partitions xs ↔ ys.flatten = xs ∧ ∀ y ∈ ys, y ≠ [] := by
  induction xs generalizing ys with
  | nil =>
    simp
    constructor
    · rintro ⟨_⟩; simp
    · simp
      intro h h'
      rcases ys with _ | ⟨y, ys⟩
      · rfl
      · simp_all; grind
  | cons x xs ih =>
    simp_all
    simp [partitions, ih]; clear ih
    constructor
    · simp
      rintro xs ⟨_⟩ h
      split
      · simp_all
      · simp_all
        rename_i xs l zs
        rintro (⟨_, _⟩ | ⟨_, _⟩)
        · simp_all
        · simp_all
    · simp
      intro h h'
      suffices ∃ a, (a.flatten = xs ∧ ∀ y ∈ a, ¬y = []) ∧
              match a with
              | [] => ys = [[x]]
              | z :: zs => ys = (x :: z) :: zs ∨ ys = [x] :: z :: zs by grind
      if ys = [[x]] then
        simp_all
        subst_eqs
        use []
        simp
      else
        simp_all
        rcases ys with _ | ⟨y, ys⟩
        · simp at h
        · simp_all
          rcases y with _ | ⟨a, y⟩
          · simp_all
          · simp_all
            obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
            rcases y with _ | ⟨b, y⟩
            · simp_all
              use ys
              simp_all
              grind
            · simp_all
              apply Exists.intro ((b::y) :: ys)
              simp_all

@[simp]
theorem List.nil_mem_partitions {α : Type*} [DecidableEq α] {xs : List α} : [] ∈ List.partitions xs ↔ xs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all [partitions]
    intro l hl
    split
    · simp
    · simp

theorem List.partitions_cons_eq_split {α : Type*} [DecidableEq α] {x} {xs : List α} {f : List (List α) → 𝒲[Pk[F,N], Pk[F,N], 𝒮]} :
    ∑ ys ∈ List.partitions (x :: xs), f ys =
    ∑ i ∈ ..=‖xs‖, ∑ p ∈ List.partitions (xs[i..]), f ((x :: xs[..i]) :: p) := by
  induction xs generalizing x f with
  | nil => simp [partitions]
  | cons y xs ih =>
    rw [partitions]
    rw [Finset.sum_biUnion]
    · simp
      rw [Finset.sum_range_succ']
      simp
      simp [ih]
      simp [← Finset.sum_add_distrib]
    · intro A hA B hB h

      simp_all [List.mem_partitions_iff]
      intro S hSA hSB t ht
      simp_all
      replace hSA := hSA ht
      replace hSB := hSB ht
      split at hSA <;> split at hSB
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        cases hSA
        · subst_eqs
          simp_all
        · subst_eqs
          simp_all

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
  conv => enter [1, 2, _]; rw [ih _ (by simp; omega)]
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

theorem G'_seq xs : G' (p.Seq p') xs = (∑ c ∈ ..=‖xs‖, G' p (xs[..c]) * G' p' (xs[c..])) := by
  ext
  simp [G', G, G.concat_apply, GS.splitAtJoined]
  simp [G_eq_G', ← Matrix.mul_apply, ← Finset.sum_apply]
theorem G'_skip xs : G' (wnk_rpol {skip} : RPol[F,N,𝒮]) xs = match xs with | [] => 1 | _ => 0 := by
  ext α β
  simp [G']
  split_ifs with h
  · rcases h with ⟨⟨_⟩, ⟨_⟩⟩
    simp
  · split
    · simp_all
    · simp_all

def List.buckets {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) : Finset (List (List α)) :=
  match n with
  | 0 => {}
  | n+1 =>
    match xs with
    | [] => {List.replicate (n+1) []}
    | x::xs =>
      (List.buckets (x::xs) n).map ⟨([] :: ·), List.cons_injective⟩ ∪
      (List.buckets xs (n+1)).image fun bs ↦
        match bs with
        | [] => [] -- NOTE: this case is unreachable
        | b::bs => (x::b)::bs

-- theorem List.buckets_card {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) :
--     (List.buckets xs n).card = Nat.choose (n + ‖xs‖ - 1) ‖xs‖ := by
--   induction xs generalizing n with
--   | nil =>
--     induction n with
--     | zero => simp [buckets]
--     | succ n ih => simp [buckets]
--   | cons x xs ih =>
--     induction n with
--     | zero => simp [buckets]
--     | succ n ih =>
--       simp [buckets]

-- #eval (List.range 10).map (fun n ↦ (Nat.choose (n + 4 - 1) 4, (List.buckets (List.range 4) n).card))

@[simp]
theorem List.buckets_nil {α : Type*} [DecidableEq α] {n} :
    List.buckets ([] : List α) n = if n = 0 then {} else {List.replicate n []} := by
  induction n with
  | zero => simp [buckets]
  | succ n ih => simp [buckets]
@[simp]
theorem List.buckets_zero {α : Type*} [DecidableEq α] (xs : List α) :
    List.buckets xs 0 = {} := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [buckets]
@[simp]
theorem List.buckets_one {α : Type*} [DecidableEq α] (xs : List α) :
    List.buckets xs 1 = {[xs]} := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all [buckets]
theorem List.mem_buckets_iff {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) {ys} :
    ys ∈ List.buckets xs n ↔ n ≠ 0 ∧ ys.flatten = xs ∧ ‖ys‖ = n := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
    induction xs generalizing ys n with
    | nil => simp [List.eq_replicate_iff]; grind
    | cons x xs ih' =>
      simp
      simp [buckets]
      simp_all
      clear ih ih'
      constructor
      · grind
      · simp
        rcases ys with _ | ⟨y, ys⟩
        · simp_all
        · simp_all
          rcases y with _ | ⟨a, y⟩
          · simp_all; grind
          · simp_all
            rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
            use y :: ys
            simp

@[grind =]
theorem List.mem_products' {α : Type*} {x} {xs : List (List α)} [Inhabited α] :
    x ∈ xs.products ↔
      x.length = xs.length ∧ ∀ i < ‖xs‖, x[i]! ∈ xs[i]!
:= by
  simp_all [List.mem_products]

def List.partitions' {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) : Finset (List (ℕ × List α)) :=
  match xs with
  | [] => {[]}
  | x::xs =>
    (List.partitions' xs n).biUnion fun ys ↦
      match ys with
      | [] => (Finset.range (n + 1)).image fun i ↦ [(i, [x])]
      | (i, y)::ys => insert ((i, x::y)::ys) ((Finset.range (n + 1)).image fun j ↦ (j, [x])::(i, y)::ys)

@[simp]
theorem List.partitions'_nil {α : Type*} [DecidableEq α] {n} : List.partitions' ([] : List α) n = {[]} := by rfl

theorem List.partitions_eq_partitions' {α : Type*} [DecidableEq α] {xs : List α} {n} :
    List.partitions xs = (List.partitions' xs n).image fun l ↦ l.map Prod.snd := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [partitions, partitions']
    simp [ih]
    ext l
    simp
    constructor
    · simp
      rintro (_ | ⟨y, ys⟩) h h'
      · simp_all
        subst_eqs
        use 0, [], h
        simp
      · simp at h'
        rcases h' with ⟨_, _⟩ | ⟨_, _⟩
        · use (⟨y.1, x :: y.2⟩ :: ys)
          simp
          use y::ys
          simp [h]
        · use (⟨0, [x]⟩ :: y :: ys)
          constructor
          · use y :: ys
            simp [h]
          · simp
    · simp
      intro as bs hbs has
      rcases bs with _ | ⟨b, bs⟩
      · simp_all
        obtain ⟨i, hi, _, _⟩ := has
        simp
        rintro ⟨_⟩
        use []
        simp_all
      · simp_all
        rintro ⟨_⟩
        use b::bs
        simp [hbs]
        grind

#eval List.partitions' ([1, 2] : List ℕ) 3

theorem List.mem_partitions'_iff {α : Type*} [DecidableEq α] {xs : List α} {n : ℕ} {ys}  :
    ys ∈ List.partitions' xs n ↔ (ys.map Prod.snd).flatten = xs ∧ ∀ a b, (a, b) ∈ ys → a ≤ n ∧ ¬b = [] := by
  induction xs generalizing ys with
  | nil =>
    simp
    constructor
    · rintro ⟨_⟩; simp
    · simp only [and_imp]
      intro h h'
      rcases ys with _ | ⟨⟨i, y⟩, ys⟩
      · simp
      · simp_all
        specialize h' i y
        specialize h y i
        simp_all
  | cons x xs ih =>
    simp only [partitions', Finset.mem_biUnion, ih]
    constructor
    · simp
      rintro ls ⟨_⟩ h h'
      rcases ls with _ | ⟨l, ls⟩
      · simp_all only [List.map_nil, List.flatten_nil, partitions'_nil, Finset.mem_singleton,
        List.flatten_eq_nil_iff, List.mem_map, Prod.exists, exists_eq_right, forall_exists_index,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true, Finset.mem_image, Finset.mem_range]
        obtain ⟨i, hi, ⟨_⟩⟩ := h'
        simp
        omega
      · simp_all
        rcases h' with ⟨⟨_⟩⟩ | ⟨i, hi, _, _⟩
        · simp
          grind
        · simp
          grind
    · simp
      have h₀ (xs : List α) n := List.partitions_eq_partitions' (xs:=xs) (n:=n)
      simp [Finset.ext_iff] at h₀
      replace h₀ xs n := (h₀ xs n (ys.map Prod.snd)).mp
      simp [mem_partitions_iff] at h₀

      intro h h'

      rcases ys with _ | ⟨⟨i, y⟩, ys⟩
      · simp_all only [List.map_nil, List.flatten_nil, List.nil_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, partitions'_nil, Finset.mem_singleton,
        List.map_eq_nil_iff, and_self, exists_eq, imp_self, reduceCtorEq]
      · simp_all
        rcases y with _ | ⟨a, as⟩
        · simp_all only [List.nil_append]
          rcases ys with _ | ⟨⟨j, y⟩, ys⟩
          · simp_all
          · simp_all
            absurd h'; clear h'
            simp
            use i, []
            simp
        · simp_all only [List.cons_append, List.cons.injEq]
          specialize h₀ (x :: xs) n rfl (by grind)
          obtain ⟨p, hp, hp'⟩ := h₀
          simp [partitions'] at hp
          obtain ⟨q, hq, hq'⟩ := hp
          rcases q with _ | ⟨⟨q₀, q₀'⟩, q⟩
          · simp_all only [List.map_nil, List.flatten_nil, List.nil_eq, List.not_mem_nil,
            IsEmpty.forall_iff, implies_true, and_true, Finset.mem_image, Finset.mem_range,
            List.flatten_eq_nil_iff, List.mem_map, Prod.exists, exists_eq_right,
            forall_exists_index, partitions'_nil, Finset.mem_singleton, List.append_eq_nil_iff]
            subst_eqs
            obtain ⟨j, hj, _, _⟩ := hq'
            simp_all
            use ys
            constructor
            · grind
            · rcases ys with _ | ⟨y, ys⟩
              · simp_all; omega
              · simp
                specialize h' i [x]
                simp at h'
                omega
          · simp_all only [List.map_cons, List.flatten_cons, List.mem_cons, Prod.mk.injEq,
            Finset.mem_insert, Finset.mem_image, Finset.mem_range]
            rcases hq' with ⟨_, _⟩ | ⟨j, hj, _, _⟩
            · simp_all
              rcases hp' with ⟨⟨_⟩, hp'⟩
              rcases h with ⟨⟨_⟩, ⟨_⟩⟩
              use ⟨i, as⟩::ys
              simp
              rintro k l (⟨⟨_⟩, ⟨_⟩⟩ | h)
              · specialize hq q₀ as
                simp at hq
                specialize h' i (x :: as)
                simp at h'
                grind
              · specialize h' k l
                simp [h] at h'
                exact h'
            · simp_all
              use ys
              simp_all
              constructor
              · grind
              · rcases ys with _ | ⟨y, ys⟩
                · simp_all
                · simp
                  specialize h' i [x]
                  simp at h'
                  omega


def List.partitionsFill' {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) :=
  ((List.partitions' xs n).image fun x ↦ x.flatMap fun ⟨i, l⟩ ↦ (List.replicate i [] ++ [l])).biUnion (fun q ↦ (Finset.range (n + 1)).image (q ++ List.replicate · []))

def count' (n m : ℕ) : ℕ := (n + 1) * (m + 1)

@[gcongr]
theorem count'_le {n n' m m'} (hn : n ≤ n') (hm : m ≤ m') : count' n m ≤ count' n' m' := by
  simp [count']
  grw [hn, hm]

#eval count' 3 3

-- 2 0 = 3
-- 2 1 = 6
-- 2 2 = 9
-- 2 3 = 12

-- 3 0 = 4
-- 3 1 = 8
-- 3 2 = 12
-- 3 3 = 16

#eval (List.partitionsFill' ([] : List ℕ) 3)
#eval (Finset.range 11).biUnion (List.buckets ([] : List ℕ))
-- #eval (List.partitionsFill' [1, 2, 3] 4) ⊆ (Finset.range (count' ‖[1, 2, 3]‖ 4)).biUnion (List.buckets [1, 2, 3])

#print axioms List.mem_buckets_iff
#print axioms List.partitionsFill'
#print axioms List.mem_partitions'_iff

theorem List.sum_le {α : Type*} (xs : List α) (f : α → ℕ) (cap : ℕ) (h : ∀ x ∈ xs, f x ≤ cap) : (xs.map f).sum ≤ cap * ‖xs‖ := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all
    grw [ih]
    grind

theorem List.le_sum {α : Type*} (xs : List α) (f : α → ℕ) (cap : ℕ) (h : ∀ x ∈ xs, cap ≤ f x) : ‖xs‖ * cap ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all
    grw [← ih]
    grind

theorem List.partitionsFill'_subset_buckets {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) (h : xs ≠ []) :
    List.partitionsFill' xs n ⊆ (Finset.range (count' ‖xs‖ n)).biUnion (List.buckets xs) := by
  intro l
  simp [mem_buckets_iff, partitionsFill']
  simp [List.mem_partitions'_iff]
  rintro xs ⟨_⟩ h' i hi ⟨_⟩
  simp_all only [List.length_append, List.length_flatMap, List.length_replicate, List.length_cons,
    List.length_nil, zero_add, List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul,
    mul_one, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.replicate_eq_nil_iff,
    List.cons_ne_self, and_false, imp_false, Prod.forall, not_and, List.flatten_append,
    List.flatten_replicate_nil, List.append_nil]
  induction xs generalizing n i with
  | nil => simp_all
  | cons x xs ih =>
    obtain ⟨a, bs⟩ := x

    simp_all
    have : (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) xs).flatten = (List.map Prod.snd xs).flatten := by
      clear a h h' hi ih bs
      induction xs with simp_all
    simp [this]; clear this
    have : ((∀ (a_1 : ℕ) (b : List α), (a_1 = a → ¬b = bs) ∧ (a_1, b) ∉ xs) → ¬i = 0) := by
      rintro h ⟨_⟩
      specialize h a bs
      simp at h
    simp_all only [not_false_eq_true, implies_true, and_self, and_true, gt_iff_lt]
    have := h' a bs
    simp at this
    rcases xs with _ | ⟨⟨a', bs'⟩, xs⟩
    · simp_all
      simp [count']
      rcases n with _ | n
      · simp_all
        grind [List.length_pos_iff]
      · rcases bs with _ | _
        · simp_all
        · simp_all
          ring_nf
          omega
    · simp_all only [List.mem_cons, Prod.mk.injEq, List.map_cons, List.sum_cons, List.length_cons,
      Function.comp_apply, not_or, not_and, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.flatten_append, List.flatten_replicate_nil, List.flatten_cons,
      List.append_cancel_left_eq, not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and,
      implies_true, gt_iff_lt]
      specialize ih n bs' a'
      simp at ih
      rcases bs' with _ | _
      · simp_all
        have := h' a' []
        simp at this
      · simp_all
        specialize ih (by grind) i (by omega)
        ring_nf at ih
        replace ih := ih.left
        simp [Nat.lt_iff_add_one_le] at ih
        ring_nf
        ring_nf at ih
        have : 2 + a + a' + (List.map Prod.fst xs).sum + ‖xs‖ + i = a + (2 + a' + (List.map Prod.fst xs).sum + ‖xs‖ + i) := by omega
        rw [this]; clear this
        grw [ih]
        have : 1 ≤ ‖bs‖ := by grind [List.length_pos_iff]
        grw [← this]
        ring_nf
        set m := (List.map (List.length ∘ Prod.snd) xs).sum
        simp [count']
        ring_nf
        rename_i h _ _
        grw [h.left]
        ring_nf
        simp

#print axioms List.partitionsFill'_subset_buckets

def List.corep {α : Type*} (xs : List (List α)) : List (ℕ × List α) :=
  match xs with
  | [] => []
  | []::xs =>
    match List.corep xs with
    | [] => []
    | (n, y) :: ys => (n + 1, y) :: ys
  | x::xs => (0, x) :: (List.corep xs)

#eval List.corep [[], [1, 2], [3], [], []]

@[simp]
theorem List.corep_nil {α : Type*} : corep ([] : List (List α)) = [] := by simp [corep]

@[simp]
theorem List.corep_mem_ne_nil {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    ls ≠ [] := by rintro ⟨_⟩; simp [corep] at h

@[simp]
theorem List.corep_mem_ne_nil' {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    x.2 ≠ [] := by
  induction ls generalizing x with
  | nil => simp_all
  | cons l ls ih =>
    simp_all
    rcases l with _ | ⟨i, l⟩
    · simp_all [corep]
      split at h
      · simp_all
      · grind
    · simp_all [corep]
      grind

@[simp]
theorem List.corep_mem_lt {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    x.1 < ‖ls‖ := by
  induction ls generalizing x with
  | nil => simp_all
  | cons l ls ih =>
    simp_all
    rcases l with _ | ⟨i, l⟩
    · simp_all [corep]
      split at h
      · simp_all
      · grind
    · simp_all [corep]
      grind

@[simp]
theorem List.corep_flatten {α : Type*} {ls : List (List α)} :
    (List.map Prod.snd (corep ls)).flatten = ls.flatten := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    rcases l with _ | ⟨a, l⟩
    · simp_all [corep]
      split
      · simp_all; assumption
      · simp_all
    · simp_all [corep]

@[simp]
theorem List.corep_replicate_nil {α : Type*} {i} :
    corep (List.replicate i ([] : List α)) = [] := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [corep, List.replicate]
    split
    · rfl
    · simp_all

@[simp]
theorem List.corep_append_replicate_nil {α : Type*} {ls : List (List α)} {i} :
    corep (ls ++ List.replicate i []) = corep ls := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    simp_all
    rcases l with _ | _
    · simp_all [corep]
    · simp_all [corep]

theorem List.corep_reconstruct {α : Type*} {ls : List (List α)} :
    List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) (corep ls) ++ List.rtakeWhile (·.length = 0) ls = ls := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    rcases l with _ | ⟨a, l⟩
    · simp [corep]
      split
      · simp_all; exact ih
      · simp_all
        rename_i ys i ys' l h
        simp [List.replicate]
        suffices List.rtakeWhile (fun x ↦ decide (‖x‖ = 0)) ([] :: ls) = List.rtakeWhile (fun x ↦ decide (‖x‖ = 0)) ls by
          simp [this, ih]
        clear ih
        induction ls using List.reverseRecOn with
        | nil => simp_all
        | append_singleton ls l' ih =>
          rcases l' with _ | _
          · simp_all
            rw [← List.cons_append]
            rw [List.rtakeWhile_concat]
            simp
            apply ih
            have := List.corep_append_replicate_nil (ls:=ls) (i:=1)
            simp at this
            grind
          · simp_all
    · simp_all [corep]
      nth_rw 3 [← ih]; clear ih
      simp
      induction ls using List.reverseRecOn with
      | nil => simp
      | append_singleton ls l' ih =>
        rw [← List.cons_append]
        repeat rw [List.rtakeWhile_concat]
        simp_all

def count'' (n m : ℕ) : ℕ := (n + 1) * (m + 1)

@[gcongr]
theorem count''_le {n n' m m'} (hn : n ≤ n') (hm : m ≤ m') : count'' n m ≤ count'' n' m' := by
  simp [count'']
  grw [hn, hm]

#eval count'' 3 3

theorem List.exists_nil_tail {α : Type*} (xs : List (List α)) :
    ∃ ys, (∃ x, ys ++ List.replicate x [] = xs) ∧ ∀ (h : ¬ys = []), ¬ys.getLast h = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨ys, ⟨n, _, _⟩, ih⟩ := ih
    rcases x with _ | ⟨a, x⟩
    · rcases ys with _ | ⟨y, ys⟩
      · simp_all
        use []
        simp
        use n + 1
        simp [List.replicate]
      · simp_all
        use []::y::ys
        constructor
        · use n
          simp
        · simp_all
    · use (a::x)::ys
      simp_all
      rcases ys
      · simp_all
      · simp_all

theorem List.buckets_subset_partitionsFill' {α : Type*} [DecidableEq α] (xs : List α) (n : ℕ) (h : xs ≠ []) :
    (Finset.range n).biUnion (List.buckets xs) ⊆ List.partitionsFill' xs (count'' ‖xs‖ n) := by
  intro ls
  simp [mem_buckets_iff, partitionsFill']
  simp [List.mem_partitions'_iff]
  rintro h₁ h₂ ⟨_⟩
  simp_all
  obtain ⟨xs, hxs, hxs'⟩ := h
  use List.corep ls
  simp_all [Nat.lt_iff_add_one_le]
  constructor
  · intro i as h
    have : as ≠ [] := by have := List.corep_mem_ne_nil' h; grind
    simp [this]
    have := List.corep_mem_lt h
    simp at this
    grw [this, ← h₁]
    simp [count'', mul_add, add_mul]
    omega
  · obtain ⟨ls, ⟨i, _, _⟩, h⟩ := List.exists_nil_tail ls
    simp_all
    use i
    simp
    have := List.corep_reconstruct (ls:=ls)
    constructor
    · grw [← h₁]
      simp [count'']
      simp [mul_add, add_mul]
      ring_nf
      omega
    · nth_rw 2 [← this]
      simp
      apply h

#print axioms List.buckets_subset_partitionsFill'
#print axioms List.partitionsFill'_subset_buckets

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

theorem List.buckets_succ {α : Type*} [DecidableEq α] {xs : List ℕ} {n} {f : List ℕ → 𝒲[Pk[F,N], Pk[F,N], 𝒮]} (hn : n ≠ 0) :
    ∑ b ∈ List.buckets xs (n + 1), (List.map f b).prod =
    ∑ i ∈ ..=‖xs‖, ∑ b ∈ List.buckets (xs[i..]) n, (List.map f (xs[..i] :: b)).prod := by
  -- have : xs = [1, 2, 3] := by sorry
  -- have : n = 0 := by sorry
  -- subst_eqs
  -- simp [buckets, Finset.sum_range_succ]
  -- simp [← mul_assoc, ← add_assoc]
  -- ring_nf

  induction xs generalizing n f with
  | nil =>
    simp; rcases n with _ | n <;> simp
    · contradiction
    · simp [pow_succ']
  | cons x xs ih =>
    rw [List.buckets]
    rw [Finset.sum_union]
    · simp
      rw [Finset.sum_range_succ']
      simp
      rw [add_comm]
      congr! 1
      rw [Finset.sum_image]
      ·
        simp at ih
        simp_all
        rcases n with _ | n
        · contradiction
        · simp_all
          rcases xs with _ | _
          · simp
          · rw [buckets]
            simp
        simp [ih]
        sorry
      · sorry
    · intro A h₁ h₂ B hBA
      simp_all only [Finset.le_eq_subset, Finset.bot_eq_empty, Finset.notMem_empty]
      specialize h₁ hBA
      specialize h₂ hBA
      simp_all
      grind

theorem List.buckets_succ {α : Type*} [DecidableEq α] {xs : List α} {x} {n} {f : List α → 𝒲[Pk[F,N], Pk[F,N], 𝒮]} :
    ∑ b ∈ List.buckets (x :: xs) (n + 1 + 1), (List.map f b).prod =
    ∑ i ∈ ..=‖xs‖ + 1, ∑ b ∈ List.buckets ((x :: xs)[i..]) (n + 1), (List.map f ((x :: xs)[..i] :: b)).prod := by
  rw [← Finset.sum_biUnion (s:=..=‖xs‖ + 1)]
  induction xs generalizing x n f with
  | nil =>
    simp [Finset.sum_range_succ]
    simp [← Finset.mul_sum]
    sorry
  | cons x₁ xs ih =>
    simp
    rw [buckets]
    rw [Finset.sum_union]
    · simp
      rw [Finset.sum_image]
      · rw [Finset.sum_range_succ']
        simp
        rw [add_comm]
        congr
        have : (‖xs‖ + 2) = ‖xs‖ + 1 + 1 := by rfl
        simp [this]
        simp [← List.prod_cons, ← List.map_cons]
        rw [ih]
        simp at ih


        sorry
      · sorry
    · sorry

attribute [- simp] RPol.iter in
theorem G'_iter_succ_eq {xs} {n} :
    G' (p.iter (n + 1)) xs = ∑ b ∈ List.buckets xs (n + 1), (b.map (G' p)).prod := by
  induction xs using Nat.strongRecMeasure List.length generalizing n; next xs ih =>
  rcases xs with _ | ⟨α₀, xs⟩
  · simp [RPol.iter, G'_seq, pow_succ']
  · -- ext α β
    induction n with
    | zero =>
      simp [RPol.iter, G'_seq]
      have ih' := ih (n:=0)
      clear ih
      simp_all
      rw [Finset.sum_range_succ']
      simp
      conv => enter [1, 2, 2]; simp [G'_skip]
      simp
      simp [List.buckets]
      rw [Finset.sum_eq_single ‖xs‖]
      · simp_all [G'_skip]
      · simp_all [G'_skip]
        intro _ _
        split
        · simp_all
          omega
        · simp_all
      · simp_all
    | succ n ihn =>
      rw [RPol.iter]
      simp only [G'_seq, List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero]
      conv =>
        enter [1, 1, 2, c]
        rw [ih _ (by simp; omega)]
      clear ih
      rw [ihn]; clear ihn
      simp [Finset.mul_sum]
      calc
        _ = ∑ x ∈ ..=‖xs‖ + 1,
                ∑ i ∈ List.buckets ((α₀ :: xs)[x..]) (n + 1),
                  G' p ((α₀ :: xs)[..x]) * (List.map (G' p) i).prod := by
          nth_rw 2 [Finset.sum_range_succ']
          simp
        _ = _ := by
          simp [← List.prod_cons, ← List.map_cons, List.buckets_succ]

attribute [- simp] RPol.iter in
theorem G'_iter_eq {xs} {n} :
    G' (p.iter n) xs = if n = 0 ∧ xs = [] then 1 else ∑ b ∈ List.buckets xs n, (b.map (G' p)).prod := by
  rcases n with _ | n
  · simp [RPol.iter, G'_skip]
    rcases xs with _ | _
    · simp
    · simp_all
  · simp [G'_iter_succ_eq]

theorem ωSup_nat_eq_with_map {f g : Chain 𝒮} (m : ℕ → ℕ) (h : ∀ i, i ≤ m i) (h' : ∀ i, f i = g (m i)) : ωSup f = ωSup g := by
  apply le_antisymm
  · simp
    intro i
    apply le_ωSup_of_le (m i)
    grind
  · simp
    intro j
    obtain ⟨i, hi⟩ : ∃ i, j ≤ m i := ⟨j, h j⟩
    grw [hi]
    apply le_ωSup_of_le i
    grind

theorem G'_eq_A' {xs} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) : G' p.Iter xs = ωSup ⟨fun n ↦ A' p n xs, sorry⟩ := by
  simp [A'_iter_eq, ihp]
  ext α β
  simp [G', G]
  simp [G_eq_G', G'_iter_eq]
  rw [ωSum_nat_eq_ωSup_succ]
  -- TODO: use antisymm and find the appropriate upperbound in both directions
  -- symm
  -- let g : ℕ → ℕ := sorry
  -- have hg : ∀ i, i ≤ g i := sorry
  -- apply ωSup_nat_eq_with_map g hg fun n ↦ ?_
  -- simp
  -- simp [DFunLike.coe]
  -- simp [← Finset.sum_apply]
  -- congr!
  -- clear α β
  -- rcases xs with _ | ⟨α₀, xs⟩
  -- · sorry
  -- · rcases xs with _ | ⟨α₀, xs⟩
  --   · simp
  --     simp [Finset.sum_range_succ']
  --     rcases n with _ | _ | _ | _ | _ | _ | n
  --     · simp
  --     · simp [G''_succ', List.partitions]
  --     · sorry
  --     · sorry
  --     · sorry
  --     · simp [G''_succ']
  --       have : g = fun _ ↦ 7 := sorry
  --       simp [this, Finset.sum_range_succ, List.partitions]
  --       simp [List.buckets]
  --       simp [pow_succ]
  --       simp [mul_add, add_mul, ← mul_assoc, ← add_assoc]
  --       grind
  -- simp
  -- simp only [G'_iter_eq, ihp]




theorem A'_iter_cons {α₀} {xs} {n} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p n (α₀::xs) = List.partitions := by
  induction n with
  | zero => simp; sorry
  | succ n ih =>
    ext
    simp [A']
    rw [approx_𝒜_iter_eq]
    simp
    simp [𝒪_heart_n_eq_G', ihp, 𝒜_eq_G', approx_𝒜_eq_A']
    simp [← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
    simp [← Matrix.sum_apply]
    simp [Matrix.mul_assoc, ← Matrix.mul_sum]
    nth_rw 2 [Finset.sum_range_succ]
    simp [mul_add, ← mul_assoc, ihp]
    have : (∑ x ∈ ..=n, G' p [] ^ x) = G'' p (n + 1) := by simp [G'']
    simp [this]


theorem A'_iter_two_single' {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 2 [α₀] = G'' p 2 * G' p [α₀] * G'' p 2 := by
  ext; simp [A', G'', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
theorem A'_iter_three_single {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 3 [α₀] = G'' p 3 * G' p [α₀] * G'' p 3 := by
  ext; simp [A', G'', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
theorem A'_iter_four_single {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 4 [α₀] = G'' p 4 * G' p [α₀] * G'' p 4 := by
  ext; simp [A', G'', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
theorem A'_iter_two_pair {α₀ α₁} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 2 [α₀, α₁] = G' p [α₀] + G' p [] * G' p [α₀] + G' p [α₀] * G' p [] + G' p [] * G' p [α₀] * G' p [] := by
  ext; simp [A', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
  simp [← add_assoc, ← mul_assoc, ← Matrix.add_apply]
  sorry
theorem A'_iter_three_single {α₀} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 3 [α₀] = sorry := by
  ext; simp [A', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
  simp [← add_assoc, ← mul_assoc, ← Matrix.add_apply]
theorem A'_iter_three_pair {α₀ α₁} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    A' p 3 [α₀, α₁] = sorry := by
  ext; simp [A', 𝒪_heart_n_eq_G', approx_𝒜_iter_nonempty, 𝒜_eq_G', ihp, mul_assoc, Finset.sum_range_succ, mul_add, add_mul, Finset.sum_add_distrib]
  simp [← mul_assoc]
  simp [← Finset.sum_mul]
  simp [← Matrix.mul_apply]
  simp [← add_assoc, ← mul_assoc, ← Matrix.add_apply]


theorem approx_𝒜_iter_eq_ωSup_approx' {α β} {n} {xₙ} (h : ‖xₙ‖ ≤ n) (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    approx_𝒜 p n ⟨α, xₙ, β⟩ = sorry := by-- if n = 0 then 0 else ∑ m ∈ Finset.range (count n ‖xₙ‖), ∑ xs ∈ X m xₙ, (xs.map (G' p)).prod α β := by
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  clear ihₙ
  rcases n with _ | _ | _ | _ | n
  · simp [𝒪_heart_n_eq_G', ihp]
    rw [approx_𝒜_iter_eq]
    simp [𝒪_heart_n]
  · sorry
  · simp
    clear h
    rcases xₙ with _ | ⟨α₀, xₙ⟩
    · simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ]
      sorry
    · rcases xₙ with _ | ⟨α₁, xₙ⟩
      · rw [approx_𝒜_iter_eq]
        simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
        simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul, add_mul, mul_add, Finset.sum_add_distrib]
        simp [← add_assoc, ← Matrix.add_apply]
        sorry
      · rcases xₙ with _ | ⟨α₂, xₙ⟩
        · rw [approx_𝒜_iter_eq]
          simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
          conv =>
            enter [1, 2, 2, _, 2, _]; rw [approx_𝒜_iter_eq]
          simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
          simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul, add_mul, mul_add, Finset.sum_add_distrib]
          simp [← add_assoc, ← Matrix.add_apply, ← Matrix.mul_assoc]
          sorry
      -- simp [Finset.sum_range_succ]
  --   · rcases xₙ with _ | ⟨α₁, xₙ⟩
  --     · -- simp [Finset.sum_range_succ]
  --       rw [approx_𝒜_iter_eq]
  --       simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       sorry
  --     · rcases xₙ with _ | ⟨α₂, xₙ⟩
  --       · -- simp [Finset.sum_range_succ]
  --         rw [approx_𝒜_iter_eq]
  --         simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --         simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --         simp [approx_𝒜_iter_eq]
  --         simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --         simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       -- · rcases xₙ with _ | ⟨α₃, xₙ⟩
  --       --   · -- simp [Finset.sum_range_succ]
  --       --     rw [approx_𝒜_iter_eq]
  --       --     simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --     simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --     conv =>
  --       --       enter [1, 2, 1, 2, x]
  --       --       rw [approx_𝒜_iter_eq]
  --       --     simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --     simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --     conv =>
  --       --       enter [1, 2, 2, 2, x]
  --       --       rw [approx_𝒜_iter_eq]
  --       --     simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --     simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --     conv =>
  --       --       enter [1, 2, 2, 2, x, 2, 2, 2, _]
  --       --       rw [approx_𝒜_iter_eq]
  --       --     simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --     simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  --       --     simp [← add_assoc, ← Matrix.add_apply, ← Matrix.mul_assoc]
  --       --   · rcases xₙ with _ | ⟨α₄, xₙ⟩
  --       --     · -- simp [Finset.sum_range_succ]
  --       --       rw [approx_𝒜_iter_eq]
  --       --       simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --       simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --       conv =>
  --       --         enter [1, 2, 1, 2, x]
  --       --         rw [approx_𝒜_iter_eq]
  --       --       simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --       simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --       conv =>
  --       --         enter [1, 2, 2, 2, x]
  --       --         rw [approx_𝒜_iter_eq]
  --       --       simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --       simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul]
  --       --       conv =>
  --       --         enter [1, 2, 2, 2, x, 2, 2, 2, _]
  --       --         rw [approx_𝒜_iter_eq]
  --       --       simp [𝒪_heart_n_eq_G', 𝒜_eq_G', ihp, X, Z, Finset.range_add_one]
  --       --       simp_all [𝒪_heart_n_eq_G', ihp, X_nil, Finset.sum_range_succ, 𝒜_eq_G', ← Matrix.mul_apply, ← Finset.mul_sum, ← Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  --       --       simp [← add_assoc, ← Matrix.add_apply, ← Matrix.mul_assoc]

          sorry
      simp [X, Z, Finset.range_add_one]
      simp_all [𝒪_heart_n_eq_G', ihp, X_nil]

  -- induction n generalizing xₙ α β with
  -- | zero =>
  --   simp_all; subst_eqs
  --   symm
  --   simp [𝒪_heart_n_apply]
  -- | succ n ih =>
  --   rcases xₙ with _ | ⟨α₀, xₙ⟩
  --   · simp_all
  --     simp [𝒪_heart_n_eq_G', ihp, X_nil]
  --     simp [Finset.sum_range_succ']
  --     rw [Finset.sum_apply]
  --     simp
  --   · symm at ihp
  --     simp [approx_𝒜_iter_nonempty, ihp]
  --     simp [𝒪_heart_n_eq_G', ihp, X_nil]
  --     simp_all [G_eq_G', ← Matrix.mul_apply, ← Finset.sum_mul]
  --     simp [← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.sum_apply]
  --     conv =>
  --       enter [1, 2, x, 2, x, 2]
  --       rw [ihₙ _ (by simp; omega) (by simp; omega)]
  --     simp [Finset.sum_comm (γ:=Pk[F,N]), Finset.mul_sum, ← Matrix.mul_apply]
  --     rcases xₙ with _ | ⟨α₁, xₙ⟩
  --     · simp
  --       simp [← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.sum_apply]
  --       sorry
  --     · sorry

theorem G_iter_eq_ωSup_approx {α β} {xₙ} (ihp : G⟦~p⟧ = 𝒜⟦~p⟧) :
    G⟦~p*⟧ ⟨α, xₙ, β⟩ = ωSup ⟨fun n ↦ approx_𝒜 p n ⟨α, xₙ, β⟩, approx_𝒜_apply_monotone p⟩ := by
  conv =>
    enter [2, 1, 1, n]
    rw [approx_𝒜_iter_eq]
    enter [3, 2, i, 2, _, 2, _]
    rw [approx_𝒜_iter_eq]
    enter [2, 3, 2, i, 2, _, 2, _]
    rw [approx_𝒜_iter_eq]
    -- enter [2, 3, 2, i, 2, _, 2, _]
    -- rw [approx_𝒜_iter_eq]
    -- enter [2, 3, 2, i, 2, _, 2, _]
    -- rw [approx_𝒜_iter_eq]
    -- enter [2, 3, 2, i, 2, _, 2, _]
    -- rw [approx_𝒜_iter_eq]
    -- enter [2, 3, 2, i, 2, _, 2, _]
    -- rw [approx_𝒜_iter_eq]
  simp only [List.drop_eq_nil_iff, List.length_drop, List.drop_drop, mul_ite, Finset.sum_ite_irrel]
  -- simp [approx_𝒜_eq_sum_G _ ihp]
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · sorry
  · rcases xₙ with _ | ⟨α₁, xₙ⟩
    · sorry
    · rcases xₙ with _ | ⟨α₂, xₙ⟩
      · sorry
      · rcases xₙ with _ | ⟨α₃, xₙ⟩
        · simp only [reduceCtorEq, ↓reduceIte, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Nat.reduceLeDiff, List.take_succ_cons, ← Finset.sum_mul, Nat.reduceSubDiff,
          List.drop_succ_cons, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, List.take_zero, tsub_zero, List.drop_zero,
          Nat.reduceSub, List.take_nil, List.drop_nil, approx_𝒜_iter_empty, le_refl,
          Nat.not_ofNat_le_one, Nat.add_one_sub_one]
          simp only [G, RPol.instHPow, Countsupp.ωSum_apply]
          let Q n xs := fun a b ↦ if xs = [] then 𝒪_heart_n p n a b else 𝒜⟦~p⟧ ⟨a, xs, b⟩
          -- have {A B : Pk[F,N] → Pk[F,N] → 𝒮} :
          have : ∀ n xs a b, 𝒜⟦~p⟧ ⟨a, xs, b⟩ = Q n xs a b := by intros; simp [Q]; rintro ⟨_⟩; sorry
          conv =>
            enter [2, 1, 1, n]
            simp only [this n]
          have : ∀ n a b, 𝒪_heart_n p n a b = Q n [] a b := by intros; simp [Q]
          simp [this]
          simp only [← Matrix.mul_apply, ← mul_assoc, ← Matrix.add_apply, Matrix.mul_add]
          simp only [Matrix.add_apply]
          let Q' xs := fun a b ↦ G⟦~p⟧ ⟨a, xs, b⟩
          have : ∀ xs a b, G⟦~p⟧ ⟨a, xs, b⟩ = Q' xs a b := by intros; rfl
          rw [ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ, ωSum_nat_eq_succ]
          conv =>
            left
            simp [G, G.concat_apply, GS.splitAtJoined]
            enter [2, 2, 1]
            simp [Finset.sum_range_succ]
            simp [← Matrix.mul_apply, ← mul_assoc, ← Matrix.add_apply, Matrix.mul_add, this]
            simp
        · rcases xₙ with _ | ⟨α₀, xₙ⟩
          · simp
    simp [G, ωSum_nat_eq_ωSup, Chain.map]; unfold Function.comp; simp
    apply le_antisymm
    · simp
      intro n
      apply le_ωSup_of_le n
      simp [𝒪_heart_n_apply]
      gcongr with i
      induction i generalizing α β with
      | zero => simp; rfl
      | succ i ih =>
        simp [pow_succ', G, G.concat_apply, GS.splitAtJoined, Matrix.mul_apply, ihp]
        gcongr
        · rfl
        · apply ih; simp_all; omega
    · simp
      intro n
      apply le_ωSup_of_le n
      simp [𝒪_heart_n_apply]
      gcongr with i
      induction i generalizing α β with
      | zero => simp; rfl
      | succ i ih =>
        simp [pow_succ', G, G.concat_apply, GS.splitAtJoined, Matrix.mul_apply, ihp]
        gcongr
        · rfl
        · apply ih; simp_all; omega
  · simp [approx_𝒜_iter_nonempty, 𝒪_heart_n_apply]
    rw [← ωSup_ωSup_eq_ωSup' (f:=fun n m ↦
        ∑ x ∈ ..=‖xₙ‖,
          ∑ x_1,
            ∑ x_2,
              (∑ i ∈ Finset.range n, ((ι p ⊠ 𝒪 p) ^ i) α x_2) * 𝒜⟦~p⟧ (x_2, α₀ :: xₙ[..x], x_1) *
                approx_𝒜 p m (x_1, xₙ[x..], β))]
    rotate_left
    · refine monotone_nat_of_le_succ fun n m ↦ (by simp; gcongr <;> simp)
    · refine fun _ ↦ monotone_nat_of_le_succ (fun _ ↦ by gcongr; omega)
    simp [G]
    apply le_antisymm
    · simp
      intro n
    · simp

theorem new_approach'' {n} {α β} {xs} (h : ‖xs‖ ≤ n) : 𝒜⟦~(p.iterLe n)⟧ ⟨α, xs, β⟩ = approx_𝒜 p (n + 1) ⟨α, xs, β⟩ := by
  induction n generalizing α xs β with
  | zero => simp_all [𝒪_heart_n]; rfl
  | succ n ih =>
    simp_all
    simp [approx_𝒜, approx_ι, approx_𝒪]
    rw [xδ_approx_δ_iter]
    rw [ι_wProd_δ, ι_wProd_𝒪]
    simp
    have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
    simp [this]
    simp [δ.δ', approx_δ.δ']
    rw [xδ_δ'_as_sum_unfolded]
    simp
    have 𝒪_heart_eq {n} : 𝒪_heart_n p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
      ext α γ; simp [𝒪_heart_n, LawfulStar.star_eq_sum]; congr!
    rcases xs with _ | ⟨α₀, xs⟩
    · simp
      simp [Matrix.coe_unique_left, Q, Matrix.down, 𝒪_heart_eq]
      rw [Finset.sum_range_succ]
      simp
      congr
      · sorry
      · sorry
    · simp
      simp only [crox, Listed.array_sum_eq_finset_sum]
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
      simp [List.getLast?_cons]
      simp only [List.length_cons, add_le_add_iff_right] at h
      symm
      calc
        -- _ = ((𝒪_heart_n p (n + 1 + 1) ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xs) * (𝒪 p ⊟' 𝒪_heart_n p (n + 1 + 1)) ((α₀ :: xs).getLast?.getD α) β).down +
        --       ∑ x ∈ Finset.range xs.length,
        --         ∑ x_1,
        --           ((𝒪_heart_n p (n + 1 + 1) ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: List.take x xs) * 𝒪 p ((α₀ :: xs)[x]?.getD default) x_1).down *
        --                   𝒜⟦~p*⟧ (x_1, List.drop x xs, β) := by
        --   rcases xs with _ | ⟨α₁, xs⟩
        --   · simp
        --   simp only [List.getLast?_cons_cons, List.length_cons]
        --   congr! with i hi γ hγ
        --   nth_rw 2 [Matrix.mul_assoc]
        --   nth_rw 1 [Matrix.mul_assoc]
        --   simp
        --   congr
        --   simp [A_sem_cases]
        --   simp [ι, 𝒪]
        --   rw [xδ_δ_iter]
        --   simp
        --   rw [ι_wProd_δ, ι_wProd_𝒪]
        --   simp
        --   have : ∀ (x : 𝒲[S.I {♡}, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
        --   simp [this]
        --   simp at hi
        --   split_ifs with hi'
        --   · omega
        --   · simp [approx_δ.δ', List.head!_eq_head?, Option.getD_default_eq_iget, List.getLast?_drop, hi, hi', List.getLast?_cons]
        -- _ = ((𝒪_heart_n p (n + 1 + 1) ⊟ ι p ⊡ δ p) α α₀ * xδ (δ p) (α₀ :: xs) * (𝒪 p ⊟' 𝒪_heart_n p (n + 1 + 1)) ((α₀ :: xs).getLast?.getD α) β).down +
        --       ∑ i ∈ Finset.range xs.length,
        --         ∑ γ,
        --           (𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs.take i)) α γ *
        --                   Q⟦~p*⟧ (List.drop i xs) γ β := by
        --   congr! with i hi γ hγ
        --   simp only [Finset.mem_range] at hi
        --   nth_rw 1 [Matrix.mul_apply]
        --   simp [Q, sox, Matrix.sum_mul]
        --   congr! with ξ hξ
        --   simp [RPol.wnka_sem_case]
        --   simp [xδ, fox, ← Matrix.mul_assoc]
        --   congr! 3
        --   rcases i with _ | i
        --   · simp [List.getLast?_cons]
        --   · have : i < xs.length := by omega
        --     simp [List.getLast?_cons, List.getLast?_take, this]
        _ = (𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs) * 𝒪_heart_n p (n + 1 + 1)) α β +
              ∑ i ∈ Finset.range xs.length, ∑ γ,
                  (𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs.take i)) α γ * 𝒜⟦~(p.iterLe n)⟧ ⟨γ, List.drop i xs, β⟩ := by
          conv =>
            enter [2, 2, 2, i, 2, γ, 2]
            rw [ih (by grind)]

          sorry
          -- congr! with i hi γ hγ
          -- · nth_rw 2 [Matrix.mul_assoc]
          --   nth_rw 1 [Matrix.mul_apply]
          --   conv => right; arg 2; ext; rw [Matrix.mul_apply]
          --   simp [Q, sox, sox', Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum, Matrix.mul_assoc, mul_assoc]
          --   rw [Finset.sum_comm]
          --   congr! 4 with γ hγ ξ hξ
          --   simp [RPol.wnka_sem_case]
          --   simp [xδ, fox, ← Matrix.mul_assoc]
          --   congr! 3
          -- · nth_rw 2 [Matrix.mul_assoc]
          --   nth_rw 1 [Matrix.mul_apply]
          --   conv => right; arg 2; ext; rw [Matrix.mul_apply]
          --   simp [Q, sox, sox', Matrix.sum_mul, Matrix.mul_sum, Finset.sum_mul, Finset.mul_sum, Matrix.mul_assoc, mul_assoc]
          --   rw [Finset.sum_comm]
          --   congr! 4 with γ hγ ξ hξ
          --   simp [RPol.wnka_sem_case]
          --   simp [xδ, fox, ← Matrix.mul_assoc]
          --   congr! 3
        _ = (𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs) * 𝒪_heart_n p (n + 1 + 1)) α β +
              ∑ i ∈ Finset.range xs.length,
                  ((𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs.take i)) * Q⟦~p*⟧ (List.drop i xs)) α β := by
          simp [Matrix.mul_apply]
        _ = ∑ i ∈ Finset.range (xs.length + 1), ((𝒪_heart_n p (n + 1 + 1) * Q⟦~p⟧ (α₀ :: xs.take i)) * Q⟦~p*⟧ (List.drop i xs)) α β := by
          simp [Finset.sum_range_succ]
          rw [add_comm]
          congr!
          ext
          simp [Q]
          rw [RPol.wnka_sem_case]
          simp [ι, xδ, 𝒪]
          rw [ι_wProd_𝒪]
          simp [Matrix.down, Matrix.mul_apply]
        _ = ∑ i ∈ Finset.range (xs.length + 1), ∑ ξ, ∑ γ, 𝒪_heart_n p (n + 1 + 1) α γ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xs.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xs, β⟩ := by
          simp [Matrix.mul_apply, Finset.sum_mul, RPol.Q_eq_A_sem]
        _ = ω∑ (m : ℕ), ∑ i ∈ Finset.range (xs.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xs.take i, ξ⟩ * 𝒜⟦~p*⟧ ⟨ξ, List.drop i xs, β⟩ := by
          simp [← ωSum_mul_left, ωSum_sum_comm]
          simp [𝒪_heart_eq, ← ωSum_mul_left, ← ωSum_mul_right, ← ωSum_sum_comm]
          congr!
          sorry
        _ = ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xs.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xs.take i, ξ⟩ * (𝒜⟦~p⟧^n) ⟨ξ, List.drop i xs, β⟩ := by
          simp [ωSum_mul_left, ωSum_sum_comm]
          congr!
          rw [← ihₙ _ (by simp; omega)]
          simp


    -- simp [approx_𝒜, approx_ι, approx_𝒪]
    -- rw [xδ_approx_δ_iter]
    -- rw [ι_wProd_δ, ι_wProd_𝒪]
    -- simp
    -- have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
    -- simp [this]
    -- simp [approx_δ.δ']
    -- rw [xδ_δ'_as_sum_unfolded]
    -- simp
    -- have 𝒪_heart_eq {n} : 𝒪_heart_n p n = ∑ m ∈ Finset.range n, (Q⟦~p⟧^m) [] := by
    --   ext α γ; simp [𝒪_heart_n, LawfulStar.star_eq_sum]; congr!
    -- rcases xₙ with _ | ⟨α₀, xₙ⟩
    -- · simp
    --   simp [Matrix.coe_unique_left, Q, Matrix.down, 𝒪_heart_eq]
    --   rfl
    -- · simp
    --   simp [crox, Listed.array_sum_eq_finset_sum]
    --   simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]

theorem new_approach : 𝒜⟦~p*⟧ = ωSup ⟨fun n ↦ approx_𝒜 p n, sorry⟩ := by
  ext ⟨α, xₙ, β⟩
  induction xₙ using Nat.strongRecMeasure List.length generalizing α β; next xₙ ihₙ =>
  rw [A_sem_cases]
  simp [Chain.map]; unfold Function.comp; simp
  simp [approx_𝒜]
  simp [ι, 𝒪, approx_ι, approx_𝒪]
  rw [xδ_δ_iter]
  conv =>
    enter [2, 1, 1, x]
    rw [xδ_approx_δ_iter]
  simp
  rw [ι_wProd_δ, ι_wProd_𝒪]
  conv =>
    enter [2, 1, 1, x]
    rw [ι_wProd_δ, ι_wProd_𝒪]
  simp
  have : ∀ (x : 𝒲[S.I {♡}, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  have : ∀ (x : 𝒲[𝟙, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, 𝟙, 𝒮] 𝒲[𝟙, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
  simp [this]
  simp [δ.δ', approx_δ.δ']
  rw [xδ_δ'_as_sum_unfolded]
  conv =>
    enter [2, 1, 1, x]
    rw [xδ_δ'_as_sum_unfolded]
  simp
  have 𝒪_heart_eq : 𝒪_heart p = ω∑ (m : ℕ), (Q⟦~p⟧^m) [] := by
    ext α γ; simp [𝒪_heart, LawfulStar.star_eq_sum]; congr!
  rcases xₙ with _ | ⟨α₀, xₙ⟩
  · simp
    simp [Matrix.coe_unique_left, Q, Matrix.down, 𝒪_heart_eq]
    simp [Matrix.mul_apply]
  · simp
    simp only [crox, Listed.array_sum_eq_finset_sum]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.sum_mul, Matrix.sum_apply, Matrix.mul_sum, Finset.sum_mul, ← Matrix.mul_assoc]
    -- symm
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
        have : ∀ (x : 𝒲[S.I {♡}, S p, 𝒮]), @HMul.hMul 𝒲[𝟙, S.I {♡}, 𝒮] 𝒲[S.I {♡}, S p, 𝒮] 𝒲[𝟙, S p, 𝒮] _ ((fun x ↦ 1)) x = x.coe_unique_left := by intro x; ext; simp [Matrix.mul_apply]
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
        simp only [𝒪_heart_eq, Pi.pow_apply, Matrix.ωSum_apply, ωSum_apply, ← ωSum_mul_right,
          ← ωSum_sum_comm]
        congr!
        sorry
      _ = ω∑ (m : ℕ), ω∑ (n : ℕ), ∑ i ∈ Finset.range (xₙ.length + 1), ∑ ξ, ∑ γ, (𝒜⟦~p⟧^m) ⟨α, [], γ⟩ * 𝒜⟦~p⟧ ⟨γ, α₀ :: xₙ.take i, ξ⟩ * (𝒜⟦~p⟧^n) ⟨ξ, List.drop i xₙ, β⟩ := by
        simp [ωSum_mul_left, ωSum_sum_comm]
        congr!
        rw [ihₙ _ (by simp; omega)]
        simp
        -- simp [ωSum_nat_eq_ωSup_succ, Chain.map, Function.comp]
        -- unfold Function.comp
        -- simp

    sorry


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
