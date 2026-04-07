import Batteries.Data.Array.Pairwise
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Data.List.DropRight
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Order.ScottTopology
import WeightedNetKAT.ComputableSemiring
import WeightedNetKAT.EMatrix
import WeightedNetKAT.FinsuppExt
import WeightedNetKAT.Language
import WeightedNetKAT.ListExt
import WeightedNetKAT.MatrixExt
import WeightedNetKAT.MatrixStar
import WeightedNetKAT.Star
import WeightedNetKAT.Star.EMatrix
import WeightedNetKAT.WNKA

open OmegaCompletePartialOrder
open scoped RightActions

open WeightingNotation

namespace WeightedNetKAT

variable {F : Type} [Listed F]
variable {N : Type}
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

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

def S.Eι {X Y : Type} [Listed X] [Listed Y] : (EMatrix 𝟙 X 𝒮) → (EMatrix 𝟙 Y 𝒮) → (EMatrix 𝟙 (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "Eι[" a "," b"]" => S.Eι a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[grind, simp]
theorem S.Eι_eq_ι {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix 𝟙 X 𝒮} {m₂ : EMatrix 𝟙 Y 𝒮} {i} {j} :
    Eι[m₁, m₂] i j = ι m₁.asMatrix m₂.asMatrix i j := by
  simp [Eι, ι]

def S.E𝒪_lambda {X Y : Type} [Listed X] [Listed Y] : (EMatrix X 𝟙 𝒮) → (EMatrix Y 𝟙 𝒮) → (EMatrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "E𝒪_lambda[" a "," b"]" => S.E𝒪_lambda a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem S.E𝒪_lambda_eq_𝒪 {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix X 𝟙 𝒮} {m₂ : EMatrix Y 𝟙 𝒮} {i} {j} :
    E𝒪_lambda m₁ m₂ i j = 𝒪 m₁.asMatrix m₂.asMatrix i j := by
  simp [E𝒪_lambda, 𝒪]

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem S.E𝒪_lambda_eq_𝒪' {X Y : Type} [Listed X] [Listed Y] {m₁ : Matrix X 𝟙 𝒮} {m₂ : Matrix Y 𝟙 𝒮} {i} {j} :
    𝒪 m₁ m₂ i j = E𝒪_lambda (EMatrix.ofMatrix m₁) (EMatrix.ofMatrix m₂) i j := by
  simp [E𝒪_lambda, 𝒪]

section delta

variable {X Y Z W : Type*} [Listed X] [Listed Y] [Listed Z] [Listed W]

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

abbrev Eη₂ {X Y : Type} [DecidableEq X] [DecidableEq Y] [instX : Listed X] [instY : Listed Y] (i : X) (j : Y) : EMatrix X Y 𝒮 :=
  let i := Listed.encode i; let j := Listed.encode j;
  .ofFn fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def Eι (p : RPol[F,N,𝒮]) : EMatrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    Eη₂ () ()
  | wnk_rpol {dup} => Eη₂ () ♡
  | wnk_rpol {~w ⨀ ~p₁} => w • Eι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => Eι[Eι p₁, Eι p₂]
  | wnk_rpol {~p₁ ; ~_} => Eι[Eι p₁, 0]
  | wnk_rpol {~_*} => Eι[0, .ofFn fun 0 ↦ 1]



variable [Star 𝒮]

def E𝒪_lambda [Listed N] [DecidableEq N] (p : RPol[F,N,𝒮]) :
    EMatrix Pk[F,N] Pk[F,N] (EMatrix (S p) 𝟙 𝒮) :=
  match _ : p with
  | wnk_rpol {drop} => 0
  | wnk_rpol {skip} =>
    .ofFn fun α β ↦ if α = β then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {@test ~γ} =>
    let γ := Listed.encode γ
    .ofFn fun α β ↦ if α = β ∧ β = γ then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {@mod ~π} => let π := Listed.encode π; .ofFn fun _ β ↦ if β = π then .ofFn fun _ ↦ 1 else 0
  | wnk_rpol {dup} => let v := Eη₂ ♣ (); .ofFn fun α β ↦ if α = β then v else 0
  | wnk_rpol {~_ ⨀ ~p₁} => let 𝒪₁ := E𝒪_lambda p₁; .ofFn fun α β ↦ 𝒪₁.getN α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
    let 𝒪₁ := E𝒪_lambda p₁
    let 𝒪₂ := E𝒪_lambda p₂
    .ofFn fun α β ↦ E𝒪_lambda[𝒪₁.getN α β, 𝒪₂.getN α β]
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

def E𝒪_heart [Listed N] [DecidableEq N] (p₁ : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] 𝒮 :=
  let ι₁ := EMatrix.asNatMatrix (Eι p₁)
  let 𝒪₁ := EMatrix.asNatMatrix₂ (E𝒪_lambda p₁)
  let X := EMatrix.ofNatMatrix (ι₁ ⊠ 𝒪₁) |>.asNMatrix
  let Y : N𝒲[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮] := X^*
  Y

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem E𝒪_lambda_iter [Listed N] [DecidableEq N] (p₁ : RPol[F,N,𝒮]) :
    E𝒪_lambda wnk_rpol {~p₁*} = .ofFn fun α β ↦
      E𝒪_lambda[
        (Listed.array.map fun γ ↦ (E𝒪_lambda p₁ |>.asNatMatrix) α γ <• (E𝒪_heart p₁ |>.asNatMatrix) γ β).sum,
        .ofFn fun _ _ ↦ (E𝒪_heart p₁ |>.asNatMatrix) α β
      ] :=
  rfl

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
@[simp]
theorem Eι_eq_ι {p : RPol[F,N,𝒮]} : Eι p = EMatrix.ofMatrix (ι p) := by
  classical
  induction p
  next =>
    ext i j
    simp [ι, Eι, η₂]
  next =>
    ext i j
    simp [ι, Eι, η₂]
  next =>
    ext i j
    simp [ι, Eι, η₂]
  next =>
    ext i j
    simp [ι, Eι, η₂]
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

variable [DecidableEq F]

variable [Listed N] [DecidableEq N] [LawfulStar N𝒲[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮]]

theorem E𝒪_heart_eq_𝒪_heart {p : RPol[F,N,𝒮]} (h : E𝒪_lambda p = EMatrix.ofMatrix₂ (𝒪 p)) :
    E𝒪_heart p = EMatrix.ofMatrix (𝒪_heart p) := by
  simp [E𝒪_heart, 𝒪_heart]
  simp [LawfulStar.star_eq_sum]
  ext α β
  simp
  convert EMatrix.ωSum_apply (ι:=ℕ) (x:=α) (y:=β) (f:=fun n ↦ (EMatrix.ofNatMatrix ((EMatrix.ofMatrix (ι p)).asNatMatrix ⊠ (E𝒪_lambda p).asNatMatrix₂)).asNMatrix ^ n)
  symm
  rename_i n
  ext α β
  induction n generalizing α β with
  | zero =>
    simp
    show (1 : NMatrix _ _ _) (Listed.encodeFin α) (Listed.encodeFin β) = (1 : Matrix _ _ _) α β
    simp
    if α = β then
      subst_eqs
      simp_all
    else
      simp_all
  | succ n ih =>
    simp [pow_succ, ih, NMatrix.hmul_def, Matrix.mul_apply, box]
    congr!
    simp [h]
    simp [EMatrix.asNMatrix, Matrix.down, box]

@[simp]
theorem E𝒪_lambda_eq_𝒪 {p : RPol[F,N,𝒮]} : E𝒪_lambda p = EMatrix.ofMatrix₂ (𝒪 p) := by
  induction p
  next =>
    ext
    simp [𝒪, E𝒪_lambda]
  next =>
    ext i j i' j'
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
    simp [E𝒪_lambda_iter, 𝒪, sox', ih, E𝒪_heart_eq_𝒪_heart]
    congr! with γ
    ext
    simp [HSMul.hSMul, SMul.smul]

def ι_aux (p : RPol[F,N,𝒮]) : Matrix 𝟙 (S p) 𝒮 := Eι p |>.asMatrix

-- @[csimp] theorem ι_csimp : @ι = @ι_aux := by
--   funext p x _ _ _ _ _ p
--   simp [ι_aux, Eι_eq_ι]

def 𝒪_aux (p : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p) 𝟙 𝒮) := E𝒪_lambda p |>.asMatrix₂

-- @[csimp] theorem 𝒪_csimp : @𝒪 = @𝒪_aux := by
--   ext; simp [𝒪_aux, E𝒪_lambda_eq_𝒪]

def Eδ_delta (p : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] (EMatrix (S p) (S p) 𝒮) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} => .ofFn fun _ _ ↦
    0
  | wnk_rpol {dup} => .ofFn fun α β ↦ .ofFnSlow fun s ↦ if s = ♡ ∧ α = β then η₁ ♣ else 0
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

@[simp]
theorem Eδ_delta_eq_δ {p : RPol[F,N,𝒮]} : Eδ_delta p = EMatrix.ofMatrix₂ (δ p) := by
  classical
  induction p
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp_all [Eδ_delta, δ, S]; congr!; ext; simp
  next => ext; simp_all [Eδ_delta, δ, S]
  next => ext; simp_all [Eδ_delta, δ]
  next p ih =>
    ext α β i j; simp_all [Eδ_delta, δ, δ.δ', E𝒪_heart_eq_𝒪_heart]
    congr!
    · ext i' j'; simp_all
      simp [EMatrix.ofNatMatrix₂]
      simp [sox, fox, crox, Matrix.sum_apply, Matrix.mul_apply]
    · ext i j
      simp_all only [EMatrix.ofNatMatrix_asMatrix]
      simp [sox, fox, -Matrix.coe_unique_left_apply, Matrix.sum_apply]

def δ_aux (p : RPol[F,N,𝒮]) : 𝒲[Pk[F,N],Pk[F,N],𝒲[S p,S p,𝒮]] := Eδ_delta p |>.asMatrix₂

-- @[csimp] theorem δ_csimp : @δ = @δ_aux := by
--   ext
--   simp [δ_aux, Eδ_delta_eq_δ]

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

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq F] in
@[simp] theorem WNKA.toWNKA_toEWNKA : 𝒜.toEWNKA.toWNKA = 𝒜 := by simp [WNKA.toEWNKA, EWNKA.toWNKA]; congr <;> ext <;> simp
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] [DecidableEq F] in
@[simp] theorem EWNKA.toEWNKA_toWNKA : ℰ.toWNKA.toEWNKA = ℰ := by simp [WNKA.toEWNKA, EWNKA.toWNKA]

-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.wnka_toEWNKA (p : RPol[F,N,𝒮]) : p.wnka.toEWNKA = p.ewnka := by
  simp [wnka, ewnka, WNKA.toEWNKA]
-- omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem RPol.ewnka_toWNKA (p : RPol[F,N,𝒮]) : p.ewnka.toWNKA = p.wnka := by
  simp [wnka, ewnka, EWNKA.toWNKA]
  constructor <;> ext <;> simp

def RPol.wnka_fast (p : RPol[F,N,𝒮]) := p.ewnka.toWNKA

-- @[csimp] theorem RPol.wnka_csimp : @RPol.wnka = @RPol.wnka_fast := by ext; simp [wnka_fast]

@[simp]
def EWNKA.toEWNKA_ι_apply {α β} : ℰ.toWNKA.ι α β = ℰ.ι α β := by
  simp [EWNKA.toWNKA]
@[simp]
def EWNKA.toEWNKA_δ_apply {α β} : ℰ.toWNKA.δ α β = (ℰ.δ α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl
@[simp]
def EWNKA.toEWNKA_𝒪_apply {α β} : ℰ.toWNKA.𝒪 α β = (ℰ.𝒪 α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl

abbrev _root_.Listed.Li (α : Type*) [Listed α] : Type := Fin (Listed.size α)
notation "Li[" α "]" => Listed.Li α

instance {α : Type*} [Listed α] : Listed Li[α] := inferInstanceAs (Listed <| Fin (Listed.size α))

def EWNKA.compute (𝒜 : EWNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    EMatrix Q 𝟙 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => .fill 1
  | [α, α'] => 𝒜.𝒪 α α'
  | α::α'::s => 𝒜.δ α α' * 𝒜.compute (α' :: s)

-- def EWNKA.Li𝒪 (ℰ : EWNKA[F,N,S,Q]) : E𝒲[Li[Pk[F,N]], Li[Pk[F,N]], E𝒲[Q, 𝟙, 𝒮]] := ℰ.𝒪

def EWNKA.compute.go (𝒜 : EWNKA[F,N,𝒮,Q]) (acc : E𝒲[Q, Q, 𝒮]) (s : List Pk[F,N]) :
    EMatrix Q 𝟙 𝒮 :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 1 is okay by idempotency
  | [] | [_] => .fill 1
  | [α, α'] => acc * 𝒜.𝒪 α α'
  | α::α'::s => EWNKA.compute.go 𝒜 (𝒜.δ α α' * acc) (α' :: s)
def EWNKA.compute''' (𝒜 : EWNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    EMatrix Q 𝟙 𝒮 :=
  EWNKA.compute.go 𝒜 1 s


-- def EWNKA.compute'' (𝒜 : EWNKA[F,N,𝒮,Q]) (s : List Li[Pk[F,N]]) (n : ℕ) :
--     EMatrix Q 𝟙 𝒮 :=
--   if h : n ≤ 1 then
--     .fill 1
--   else
--     let α₀ : Li[Pk[F,N]] := ⟨0, by sorry⟩
--     Id.run do
--     let mut A := 𝒜.𝒪.asNMatrix (s[n - 2]?.getD α₀) (s[n - 1]?.getD α₀)
--     for h : i in 3...=n do
--       A := 𝒜.δ.asNMatrix (s[n - i]?.getD α₀) (s[n - i + 1]?.getD α₀) * A
--     return A

-- def EWNKA.compute' (𝒜 : EWNKA[F,N,𝒮,Q]) (s : Array Li[Pk[F,N]]) (n : ℕ) :
--     EMatrix Q 𝟙 𝒮 :=
--   if h : n ≤ 1 then
--     .fill 1
--   else
--     let α₀ : Li[Pk[F,N]] := ⟨0, by sorry⟩
--     Id.run do
--     let mut A := 𝒜.𝒪.asNMatrix (s[n - 2]?.getD α₀) (s[n - 1]?.getD α₀)
--     for h : i in 3...=n do
--       A := 𝒜.δ.asNMatrix (s[n - i]?.getD α₀) (s[n - i + 1]?.getD α₀) * A
--     return A

-- @[simp]
-- theorem EMatrix.asNMatrix_apply {α β 𝒮 : Type*} [Listed α] [Listed β] (A : EMatrix α β 𝒮) (a : α) (b : β) :
--     (@DFunLike.coe E𝒲[α, β, 𝒮] α (fun x ↦ β → 𝒮) EMatrix.instFunLikeForall A.asNMatrix a b : 𝒮) = A a b := by
--   rfl

-- theorem EWNKA.compute'_eq_compute'' {𝒜 : EWNKA[F,N,𝒮,Q]} {xs} {n : ℕ} (hn : xs.length = n) :
--     𝒜.compute'' xs n = 𝒜.compute' xs.toArray n := by
--   induction n generalizing xs with
--   | zero => simp [compute'', compute']
--   | succ n ih =>
--     simp_all only [compute'', EMatrix.nmatrix_apply_eq_apply, EMatrix.asNMatrix_apply,
--       bind_pure_comp, map_pure, forIn'_eq_forIn, bind_pure, dite_eq_ite, compute',
--       List.getElem?_toArray, List.getElem?_map, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
--       Nat.reduceSubDiff, Order.lt_add_one_iff, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
--       getElem?_pos, Option.getD_some, add_tsub_cancel_right, lt_add_iff_pos_right, Order.lt_one_iff,
--       List.size_toArray, List.length_map, List.getElem_toArray, List.getElem_map]

-- theorem EWNKA.compute_eq_compute' {𝒜 : EWNKA[F,N,𝒮,Q]} {xs : List Pk[F,N]} (acc : E𝒲[Q, Q, 𝒮]) :
--     acc * 𝒜.compute xs = EWNKA.compute.go acc xs := by
--   induction xs with
--   | nil => rfl
--   | cons x₀ xs ih =>
--     rcases xs with _ | ⟨x₁, xs⟩
--     · rfl
--     · rcases xs with _ | ⟨x₂, xs⟩
--       · sorry
--       rcases xs with _ | ⟨x₃, xs⟩
--       · unfold compute''' compute compute.go at ih ⊢
--         simp at ih ⊢
--         rfl
--       · unfold compute''' compute compute.go at ih ⊢
--         simp at ih ⊢
--         rcases xs with _ | ⟨x₄, xs⟩
--         · unfold compute compute.go at ih ⊢
--           simp
--         simp at ih



--       simp
--       rw [ih]
--     sorry
--     simp_all [compute, compute'''. compute.go]

-- theorem EWNKA.compute_eq_compute' {𝒜 : EWNKA[F,N,𝒮,Q]} {xs} {n : ℕ} (hn : xs.length = n) :
--     𝒜.compute xs = 𝒜.compute' (xs.map Listed.encodeFin).toArray n := by
--   rw [← EWNKA.compute'_eq_compute'' (by simp [hn])]
--   induction n using Nat.strongRec generalizing xs with
--   | ind n ih =>
--     rcases n with _ | n
--     · have : xs = [] := (by grind); subst_eqs; rfl
--     rcases xs with _ | ⟨x₀, xs⟩
--     · subst_eqs
--     rcases xs with _ | ⟨x₁, xs⟩
--     · subst_eqs; simp_all; rfl
--     rcases xs with _ | ⟨x₂, xs⟩
--     · simp_all
--       simp [compute, compute'']
--       rw [forIn_eq_forIn', Std.Rcc.forIn'_eq_if]
--       simp
--     · simp_all only [Order.lt_add_one_iff, List.length_cons, Nat.add_right_cancel_iff,
--       List.map_cons]
--       replace ih := ih (xs := (x₁ :: x₂ :: xs)) n
--       simp [hn] at ih
--       simp_all [compute, compute']
--       rcases n with _ | n
--       · simp_all only [Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false,
--         and_self]
--       · simp_all only [Nat.add_right_cancel_iff, compute'', add_le_iff_nonpos_left,
--         nonpos_iff_eq_zero, Nat.reduceSubDiff, List.length_cons, List.length_map,
--         Order.lt_add_one_iff, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, getElem?_pos,
--         Option.getD_some, add_tsub_cancel_right, lt_add_iff_pos_right, Order.lt_one_iff,
--         EMatrix.nmatrix_apply_eq_apply, EMatrix.asNMatrix_apply, List.getElem?_cons_succ,
--         bind_pure_comp, map_pure, forIn'_eq_forIn, bind_pure, dite_eq_ite, Nat.add_eq_zero_iff,
--         one_ne_zero, and_false, ↓reduceDIte, List.getElem_cons_succ]
--         clear ih
--         nth_rw 2 [forIn_eq_forIn']
--         rw [Std.Rcc.forIn'_eq_if]
--         simp_all
--         nth_rw 1 [forIn_eq_forIn']
--         rw [Std.Rcc.forIn'_eq_if]
--         simp
--         rcases n with _ | _ | n
--         · simp_all
--           omega
--         · simp_all
--           rw [forIn_eq_forIn', Std.Roc.forIn'_eq_forIn'_toList]
--           simp
--         · simp
--           rw [forIn_eq_forIn', Std.Roc.forIn'_eq_forIn'_toList]
--           rw [forIn_eq_forIn', Std.Roc.forIn'_eq_forIn'_toList]
--           simp
--           have : (3<...=n + 1 + 1 + 1 + 1).toList = (List.range (n + 1)).map (· + 4) := by
--             apply List.ext_getElem
--             · simp
--             · simp; omega
--           simp [this, List.range_succ]
--           have : (3<...=n + 1 + 1 + 1).toList = (List.range n).map (· + 4) := by
--             apply List.ext_getElem
--             · simp
--             · simp; omega
--           simp [this, List.range_succ]
--           congr! 1
--           clear this
--           clear this
--           simp [List.foldl_map]
--           simp_all
--           congr
--           · ext
--             simp
--             rcases n with _ | n
--             · simp_all
--             · simp_all

--             congr! 3
--           simp
--           induction n generalizing xs with
--           | zero => simp
--           | succ n ih =>
--             simp [List.range_succ]
--             congr! 1

--             congr
--           · ext A i p ⟨⟩
--             simp
--             rcases i with _ | _ | _ | _ | _ | i
--             · simp
--             · simp
--             · simp
--             · simp
--             · simp
--               rcases n with _ | n
--               · simp
--               · simp
--             have : n + 1 + 1 + 1 - i = n + 1 + 1 - i + 1 := by sorry
--             simp [this]
--           · congr!
--             grind
def EWNKA.sem (𝒜 : EWNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨(fun x ↦ (𝒜.ι * 𝒜.compute x.pks) () ()), SetCoe.countable _⟩

theorem RPol.ewnka_sem_eq_wnka_sem (p : RPol[F,N,𝒮]) : p.ewnka.sem = p.wnka.sem := by
  ext ⟨α, xs, β⟩
  simp [ewnka, wnka, EWNKA.sem, WNKA.sem]
  simp [Matrix.mul_apply, GS.pks]
  congr! with s _
  ext s' ⟨⟩
  induction xs generalizing α s' with simp_all [Matrix.mul_apply, EWNKA.compute, WNKA.compute]

end
