module

public import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Array.Subarray
public import Std.Data.Iterators.Lemmas
public import Std.Data.Iterators.Combinators.Zip
public import Batteries.Data.Array.Pairwise
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Data.List.DropRight
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Topology.Order.ScottTopology
public import WeightedNetKAT.EMatrix
public import WeightedNetKAT.FinsuppExt
public import WeightedNetKAT.Language
public import WeightedNetKAT.ListExt
public import WeightedNetKAT.MatrixExt
public import WeightedNetKAT.Star.EMatrix
public import WeightedNetKAT.WNKA

@[expose] public section

open OmegaCompletePartialOrder
open scoped RightActions

open MatrixNotation

@[simp]
theorem Listed.array_sum_eq_finset_sum {ι α : Type*} [Listed ι] [AddCommMonoid α] (f : ι → α) :
    ((Listed.array : Array ι).map f).sum = ∑ i, f (Listed.decodeFin i) := by
  letI : DecidableEq ι := Listed.decidableEq
  convert_to _ = ∑ i ∈ Listed.array.toList.toFinset, f i
  · apply Finset.sum_equiv Listed.equivFin.symm <;> simp [equivFin]
  · generalize h : (Listed.array : Array ι) = A
    have hn : A.Nodup := by simp [← h]
    obtain ⟨A⟩ := A
    replace hn : A.Nodup := List.nodup_iff_pairwise_ne.mpr hn
    clear h
    induction A with simp_all

namespace WeightedNetKAT

variable {F : Type} [Listed F]
variable {N : Type}
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

/-- An efficient version of [`WNKA`] that uses explicit matrices. -/
structure EWNKA (F N 𝒮 Q: Type)
    [Semiring 𝒮]
    [Listed F] [Listed N]
    [Listed Q]
where
  /-- `ι` is the initial weightings. -/
  ι : E𝕄[𝟙,Q,𝒮]
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : E𝕄[Pk[F,N], Pk[F,N], E𝕄[Q,Q,𝒮]]
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : E𝕄[Pk[F,N], Pk[F,N], E𝕄[Q,𝟙,𝒮]]
notation "EWNKA[" F "," N "," 𝒮 "," Q "]" => EWNKA F N 𝒮 Q

def S.Eι {X Y : Type} [Listed X] [Listed Y] : (EMatrix 𝟙 X 𝒮) → (EMatrix 𝟙 Y 𝒮) → (EMatrix 𝟙 (X ⊕ Y) 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow (fun () x ↦ x.elim (m₁ () ·) (m₂ () ·))
notation "Eι[" a "," b"]" => S.Eι a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[grind =, simp]
theorem S.Eι_eq_ι {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix 𝟙 X 𝒮} {m₂ : EMatrix 𝟙 Y 𝒮} {i} {j} :
    Eι[m₁, m₂] i j = C[m₁.asMatrix, m₂.asMatrix] i j := by
  simp [Eι]; rfl

def S.E𝒪_lambda {X Y : Type} [Listed X] [Listed Y] : (EMatrix X 𝟙 𝒮) → (EMatrix Y 𝟙 𝒮) → (EMatrix (X ⊕ Y) 𝟙 𝒮) :=
  fun m₁ m₂ ↦ .ofFnSlow fun x () ↦ x.elim (m₁ · ()) (m₂ · ())
notation "E𝒪_lambda[" a "," b"]" => S.E𝒪_lambda a b

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem S.E𝒪_lambda_eq_𝒪 {X Y : Type} [Listed X] [Listed Y] {m₁ : EMatrix X 𝟙 𝒮} {m₂ : EMatrix Y 𝟙 𝒮} {i} {j} :
    E𝒪_lambda m₁ m₂ i j = R[m₁.asMatrix, m₂.asMatrix] i j := by
  rcases i <;> simp [E𝒪_lambda, Matrix.fromRows]

omit [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem S.E𝒪_lambda_eq_𝒪' {X Y : Type} [Listed X] [Listed Y] {m₁ : Matrix X 𝟙 𝒮} {m₂ : Matrix Y 𝟙 𝒮} {i} {j} :
    R[m₁, m₂] i j = E𝒪_lambda (EMatrix.ofMatrix m₁) (EMatrix.ofMatrix m₂) i j := by
  rcases i <;> simp [E𝒪_lambda]

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
    Eδ_delta mxy mxw mzy mzw i j = B[[mxy.asMatrix, mxw.asMatrix], [mzy.asMatrix, mzw.asMatrix]] i j := by
  simp [Eδ_delta]
  rcases i <;> rcases j <;> simp


end delta

abbrev Eη₂ {X Y : Type} [instX : Listed X] [instY : Listed Y] (i : X) (j : Y) : EMatrix X Y 𝒮 :=
  let i := Listed.encode i; let j := Listed.encode j;
  .ofFn fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0

def Eι (p : RPol[F,N,𝒮]) : EMatrix 𝟙 (S p) 𝒮 := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    Eη₂ () ()
  | wnk_rpol {dup} => Eη₂ () ♡
  | wnk_rpol {~w ⨀ ~p₁} => w • Eι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => Eι[Eι p₁, Eι p₂]
  | wnk_rpol {~p₁ ; ~_} => Eι[Eι p₁, 0]
  | wnk_rpol {~_*} => Eι[0, 1]

section Operators

variable {Pk : Type} [Listed Pk]

def boxₑ {X} [Listed X] {Q : Type} [Mul Q] [AddCommMonoid Q] {Z : Type} [Listed Z] [Unique Z]
    (l : E𝕄[Z, X, Q]) (r : E𝕄[Pk, Pk, E𝕄[X, Z, Q]]) :
    E𝕄[Pk,Pk,Q] :=
  .ofFn fun α β ↦ (l * r.asNMatrix α β).asNMatrix ⟨0, by simp⟩ ⟨0, by simp⟩

infixr:50 " ⊠ₑ " => boxₑ

@[simp]
theorem _root_.Liste.decodeFin_unique {α : Type*} [Listed α] [Unique α] (i : Fin (Listed.size α)) :
    Listed.decodeFin i = default := by
  exact Unique.eq_default (Listed.decodeFin i)

@[simp]
theorem boxₑ_eq_box {X} [Listed X] [Fintype X] {Q : Type} [Mul Q] [AddCommMonoid Q] {Z : Type} [Listed Z] [Unique Z]
    (l : E𝕄[Z, X, Q]) (r : E𝕄[Pk, Pk, E𝕄[X, Z, Q]]) :
    boxₑ l r = EMatrix.ofMatrix (box l.asMatrix r.asMatrix₂) := by
  ext
  simp only [boxₑ, EMatrix.asNMatrix_apply, Liste.decodeFin_unique, EMatrix.mul_apply,
    EMatrix.ofFn_apply, Listed.encodeFin_decodeFin, EMatrix.ofMatrix_apply, box, Matrix.down,
    Matrix.mul_apply, EMatrix.asMatrix_apply₂, EMatrix.asMatrix₂]

def foxₑ {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B] [Listed C]
    (l : E𝕄[A, B, Q]) (r : E𝕄[Pk, Pk, E𝕄[B, C, Q]]) :
    E𝕄[Pk, Pk, E𝕄[A, C, Q]] :=
  .ofFn fun α β ↦ l * r.asNMatrix α β

infixr:50 " ⊡ₑ " => foxₑ

@[simp]
theorem foxₑ_eq_fox{A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B] [Listed C] [Fintype A]
    [Fintype B] [Fintype C]
    (l : E𝕄[A, B, Q]) (r : E𝕄[Pk, Pk, E𝕄[B, C, Q]]) :
    foxₑ l r = EMatrix.ofMatrix₂ (fox l.asMatrix r.asMatrix₂) := by
  ext
  simp [foxₑ, fox, Matrix.mul_apply, EMatrix.mul_apply, EMatrix.asMatrix₂]

@[specialize, inline]
def soxₑ {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B]
    (l : E𝕄[Pk, Pk, Q]) (r : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) :
    E𝕄[Pk, Pk, E𝕄[A, B, Q]] :=
  .ofFn fun α β ↦ ∑ m, l.asNMatrix α m •> r.asNMatrix m β

infixr:50 " ⊟ₑ " => soxₑ

@[simp]
theorem soxₑ_eq_sox {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B]
    [Fintype A] [Fintype B]
    [Fintype Pk]
    (l : E𝕄[Pk, Pk, Q]) (r : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) :
    soxₑ l r = EMatrix.ofMatrix₂ (sox l.asMatrix r.asMatrix₂) := by
  ext
  simp [soxₑ, sox, Matrix.sum_apply, EMatrix.sum_apply]
  simp [HSMul.hSMul]
  congr

def sox'ₑ {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B]
    (l : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) (r : E𝕄[Pk, Pk, Q]) :
    E𝕄[Pk, Pk, E𝕄[A, B, Q]] :=
  .ofFn fun α β ↦ ∑ m, l.asNMatrix α m <• r.asNMatrix m β

infixr:50 " ⊟'ₑ " => sox'ₑ

@[simp]
theorem sox'ₑ_eq_sox' {A B : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B]
    [Fintype A] [Fintype B]
    [Fintype Pk]
    (l : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) (r : E𝕄[Pk, Pk, Q]) :
    sox'ₑ l r = EMatrix.ofMatrix₂ (sox' l.asMatrix₂ r.asMatrix) := by
  ext
  simp [sox'ₑ, sox', Matrix.sum_apply, EMatrix.sum_apply]
  simp [HSMul.hSMul, EMatrix.asMatrix₂]

def croxₑ {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B] [DecidableEq C] [Listed C]
    (l : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) (r : E𝕄[Pk, Pk, E𝕄[B, C, Q]]) :
    E𝕄[Pk, Pk, E𝕄[A, C, Q]] :=
  .ofFn fun α β ↦ ∑ m, l.asNMatrix α m * r.asNMatrix m β

infixr:50 " ⊞ₑ " => croxₑ

@[simp]
theorem croxₑ_eq_crox {A B C : Type} {Q : Type} [AddCommMonoid Q] [Mul Q]
    [Listed A] [Listed B] [DecidableEq C] [Listed C]
    [Fintype A] [Fintype B] [Fintype C]
    [Fintype Pk]
    (l : E𝕄[Pk, Pk, E𝕄[A, B, Q]]) (r : E𝕄[Pk, Pk, E𝕄[B, C, Q]]) :
    croxₑ l r = EMatrix.ofMatrix₂ (crox l.asMatrix₂ r.asMatrix₂) := by
  ext
  simp only [croxₑ, EMatrix.asNMatrix_apply, Listed.sum_fin, Listed.encodeFin_decodeFin,
    EMatrix.ofFn_apply, EMatrix.sum_apply, EMatrix.mul_apply, EMatrix.ofMatrix₂_apply, crox,
    EMatrix.ofMatrix_apply, Matrix.sum_apply, Matrix.mul_apply, EMatrix.asMatrix₂]

end Operators

namespace RPol

variable [Star 𝒮]

def E𝒪_lambda [Listed N] (p : RPol[F,N,𝒮]) :
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
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNMatrix₂
    let M₂ := E𝒪_lambda p₂ |>.asNMatrix₂
    let M₃ := Eι p₂ |>.asNMatrix
    .ofFn fun α β ↦
      E𝒪_lambda[∑ γ, 𝒪₁ α γ * M₃ * M₂ γ β, M₂ α β]
  | wnk_rpol {~p₁*} =>
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNMatrix
    let M₂ :=
      let ι₁ := Eι p₁
      let 𝒪₁ := E𝒪_lambda p₁
      let X := ι₁ ⊠ₑ 𝒪₁
      let Y : N𝕄[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮] := X^*
      Y
    .ofFn fun α β ↦
      E𝒪_lambda[
        ∑ γ, 𝒪₁ α γ <• M₂ γ β,
        .ofFn fun _ _ ↦ M₂ α β
      ]

def E𝒪_heart [Listed N] [DecidableEq N] (p₁ : RPol[F,N,𝒮]) : EMatrix Pk[F,N] Pk[F,N] 𝒮 :=
  let ι₁ := Eι p₁
  let 𝒪₁ := E𝒪_lambda p₁
  let X := ι₁ ⊠ₑ 𝒪₁
  let Y : N𝕄[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮] := X^*
  Y

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem E𝒪_lambda_iter [Listed N] [DecidableEq N] (p₁ : RPol[F,N,𝒮]) :
    E𝒪_lambda wnk_rpol {~p₁*} = .ofFn fun α β ↦
      E𝒪_lambda[
        (∑ γ, (E𝒪_lambda p₁).asNMatrix α γ <• (E𝒪_heart p₁).asNMatrix γ β),
        .ofFn fun _ _ ↦ (E𝒪_heart p₁).asNMatrix α β
      ] :=
  rfl

@[simp]
theorem EMatrix.asMatrix_one {X α : Type*} [Listed X] [DecidableEq X] [Zero α] [One α] : (EMatrix.asMatrix 1 : Matrix X X α) = 1 := by
  ext i j
  simp [EMatrix.one_apply, Matrix.one_apply]

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [Star 𝒮] in
@[simp]
theorem Eι_eq_ι {p : RPol[F,N,𝒮]} : Eι p = EMatrix.ofMatrix (ι p) := by
  classical
  induction p
  all_goals ext i j; simp [ι, Eι, η₂]
  next p q ihp ihq =>
    have := S.Eι_eq_ι (m₁:=Eι p) (m₂:=0) (i:=i) (j:=j)
    simp only [EMatrix.zero_asMatrix] at this
    simp only [S.Eι_eq_ι] at this
    convert this
    · simp
    · simp [ihp]
  next p ih => simp [ih, HSMul.hSMul]
  next p q ihp ihq => simp [ihp, ihq]

variable [DecidableEq F]

variable [Listed N] [DecidableEq N] [LawfulStar N𝕄[Listed.size Pk[F,N], Listed.size Pk[F,N], 𝒮]]

theorem E𝒪_heart_eq_𝒪_heart {p : RPol[F,N,𝒮]} (h : E𝒪_lambda p = EMatrix.ofMatrix₂ (𝒪 p)) :
    E𝒪_heart p = EMatrix.ofMatrix (𝒪_heart p) := by
  simp [E𝒪_heart, 𝒪_heart]
  simp [LawfulStar.star_eq_sum]
  ext α β
  simp
  convert EMatrix.ωSum_apply (ι:=ℕ) (x:=α) (y:=β) (f:=fun n ↦ EMatrix.ofMatrix (ι p ⊠ (E𝒪_lambda p).asMatrix₂) ^ n)
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
      simp [OfNat.ofNat, One.one, EMatrix.instOneOfZero._aux_1]
    else
      simp_all [OfNat.ofNat, One.one, EMatrix.instOneOfZero._aux_1, Matrix.diagonal]
  | succ n ih =>
    simp [pow_succ, ih, Matrix.mul_apply, box, EMatrix.mul_apply]
    congr!
    simp [h]

theorem _root_.EMatrix.apply_encodeFin {m n α : Type*} [Listed m] [Listed n] {M : N𝕄[Listed.size m, Listed.size n, α]} {i j} :
      (@DFunLike.coe E𝕄[m, n, α] m (fun _ ↦ n → α) EMatrix.instFunLikeForall M i j : α)
    = M (Listed.encodeFin i) (Listed.encodeFin j) := by
  rfl

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
    congr
    · ext γ u ⟨_⟩
      simp only [EMatrix.asMatrix_apply₂]
      simp only [_root_.EMatrix.apply_encodeFin]
      simp only [Listed.encodeFin_subsingleton, Fin.zero_eta, Fin.isValue, NMatrix.mul_coe]
      simp [Matrix.mul_apply]
      congr! with κ
      · convert EMatrix.ext_iff.mp (EMatrix.ofMatrix₂_apply (M:=𝒪 p) (i:=α) (j:=γ)) u default
        ext; simp
      · convert EMatrix.ext_iff.mp (EMatrix.ofMatrix₂_apply (M:=𝒪 q) (i:=γ) (j:=β)) κ 0
        ext; simp
    · ext
      simp
      letI : Fintype Pk[F,N] := Listed.fintype
      letI : DecidableEq Pk[F,N] := Listed.decidableEq
      simp only [EMatrix.asNMatrix₂, EMatrix.ofMatrix₂, EMatrix.map, EMatrix.getN_eq,
        EMatrix.ofFnSlow_apply]
      show ((NMatrix.ofFn fun i j ↦ EMatrix.ofMatrix _) _ _) _ _ = _
      simp
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

def 𝒪_aux (p : RPol[F,N,𝒮]) : Matrix Pk[F,N] Pk[F,N] (Matrix (S p) 𝟙 𝒮) := E𝒪_lambda p |>.asMatrix₂

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
    let ι₂ := Eι p₂
    let δ₁ := Eδ_delta p₁ |>.asNMatrix
    let δ₂ := Eδ_delta p₂ |>.asNMatrix
    let 𝒪₁ := E𝒪_lambda p₁ |>.asNMatrix
    .ofFn fun α β ↦
      Eδ_delta[[δ₁ α β, ∑ γ, 𝒪₁ α γ * ι₂ * δ₂ γ β],
               [0,      δ₂ α β]]
  | wnk_rpol {~p₁*} =>
    let ι₁ := Eι p₁
    let δ₁ := Eδ_delta p₁
    let 𝒪_heart₁ := E𝒪_heart p₁
    let X := 𝒪_heart₁ ⊟ₑ ι₁ ⊡ₑ δ₁
    let Eδ' : E𝕄[Pk[F,N], Pk[F,N], E𝕄[S p₁, S p₁, 𝒮]] := δ₁ + ((E𝒪_lambda p₁) ⊞ₑ X)
    .ofFn fun α β ↦
      Eδ_delta[[Eδ'.getN α β, 0],
               [X.asNMatrix α β, 0]]

@[simp]
theorem Eδ_delta_eq_δ {p : RPol[F,N,𝒮]} : Eδ_delta p = EMatrix.ofMatrix₂ (δ p) := by
  classical
  induction p
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next => ext; simp [Eδ_delta, δ]
  next p q ih₁ ih₂ =>
    ext α β i j; simp_all [Eδ_delta, δ, S]
    congr! with γ
    ext p' q'
    simp [Matrix.mul_apply, EMatrix.mul_apply]
  next => ext; simp_all [Eδ_delta, δ, S]
  next => ext; simp_all [Eδ_delta, δ]
  next p ih =>
    ext α β i j; simp_all [Eδ_delta, δ, δ.δ', E𝒪_heart_eq_𝒪_heart]

def δ_aux (p : RPol[F,N,𝒮]) : 𝕄[Pk[F,N],Pk[F,N],𝕄[S p,S p,𝒮]] := Eδ_delta p |>.asMatrix₂

def ewnka (p : RPol[F,N,𝒮]) : EWNKA[F,N,𝒮,S p] := ⟨Eι p, Eδ_delta p, E𝒪_lambda p⟩

end RPol

variable [Listed N]

section

variable {Q : Type} [Listed Q]
variable (𝔄 : WNKA[F,N,𝒮,Q]) (𝔈 : EWNKA[F,N,𝒮,Q])

def WNKA.toEWNKA : EWNKA[F,N,𝒮,Q] where
  ι := EMatrix.ofMatrix 𝔄.ι
  δ := EMatrix.ofMatrix₂ 𝔄.δ
  𝒪 := EMatrix.ofMatrix₂ 𝔄.𝒪

def EWNKA.toWNKA : WNKA[F,N,𝒮,Q] where
  ι := EMatrix.asMatrix 𝔈.ι
  δ := EMatrix.asMatrix₂ 𝔈.δ
  𝒪 := EMatrix.asMatrix₂ 𝔈.𝒪

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem WNKA.toWNKA_toEWNKA : 𝔄.toEWNKA.toWNKA = 𝔄 := by simp [WNKA.toEWNKA, EWNKA.toWNKA]
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp] theorem EWNKA.toEWNKA_toWNKA : 𝔈.toWNKA.toEWNKA = 𝔈 := by simp [WNKA.toEWNKA, EWNKA.toWNKA]

variable [DecidableEq F] [DecidableEq N]
variable [Star 𝒮] [LawfulStar 𝒮] [StarIter 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

@[simp] theorem RPol.wnka_toEWNKA (p : RPol[F,N,𝒮]) : p.wnka.toEWNKA = p.ewnka := by
  simp [wnka, ewnka, WNKA.toEWNKA]
@[simp] theorem RPol.ewnka_toWNKA (p : RPol[F,N,𝒮]) : p.ewnka.toWNKA = p.wnka := by
  simp [wnka, ewnka, EWNKA.toWNKA]

def RPol.wnka_fast (p : RPol[F,N,𝒮]) := p.ewnka.toWNKA

@[simp]
def EWNKA.toEWNKA_ι_apply {α β} : 𝔈.toWNKA.ι α β = 𝔈.ι α β := by
  simp [EWNKA.toWNKA]
@[simp]
def EWNKA.toEWNKA_δ_apply {α β} : 𝔈.toWNKA.δ α β = (𝔈.δ α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl
@[simp]
def EWNKA.toEWNKA_𝒪_apply {α β} : 𝔈.toWNKA.𝒪 α β = (𝔈.𝒪 α β).asMatrix := by
  simp [EWNKA.toWNKA]; rfl

notation "Li[" α "]" => Fin (Listed.size α)

def EWNKA.sem (𝒜 : EWNKA[F,N,𝒮,Q]) : GS[F,N] →c 𝒮 :=
  ⟨fun ⟨α, xs, β⟩ ↦
    (((α :: xs).zip xs).foldl (fun acc (γ, κ) ↦ acc * 𝒜.δ γ κ) 𝒜.ι * 𝒜.𝒪 (xs.getLast?.getD α) β) () (),
    SetCoe.countable _⟩

/-- Stores partial computation of the weight of a trace.

We want to compute the prefix as little as possible, and reuse it the final computation with `𝒪`.
This structure turned out to be crucial for performance, as Lean would push the computation of the
prefix into the lambda where the final `β` was given, leading it to recomputing the prefix for every
final packet.

This gives roughly a `|Pk[F,N]|` times speed up.
-/
structure EWNKA.Precompute (𝔈 : EWNKA[F,N,𝒮,Q]) where
  m : E𝕄[𝟙, Q, 𝒮]
  γ : Pk[F,N]

@[specialize, inline]
def EWNKA.Precompute.finish {𝔈 : EWNKA[F,N,𝒮,Q]} (p : 𝔈.Precompute) (β : Pk[F,N]) : 𝒮 :=
  (p.m * 𝔈.𝒪 p.γ β) () ()

@[specialize, noinline]
def EWNKA.semArray_aux (𝒜 : EWNKA[F,N,𝒮,Q]) (α_xs : Array Pk[F,N]) (h : 0 < α_xs.size) : 𝒜.Precompute :=
  let m := (Fin.foldl (α_xs.size - 1) · 𝒜.ι) <| fun acc i ↦
    let γ := α_xs[i]
    let κ := α_xs[i.val + 1]
    acc * 𝒜.δ γ κ
  let γ := α_xs[α_xs.size - 1]
  ⟨m, γ⟩

@[specialize, inline]
def EWNKA.semArray (𝒜 : EWNKA[F,N,𝒮,Q]) (α_xs : Array Pk[F,N]) (h : 0 < α_xs.size) : 𝒜.Precompute :=
  𝒜.semArray_aux α_xs h

universe u

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq F] [Star 𝒮] [LawfulStar 𝒮] [StarIter 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem EWNKA.semArray_eq_sem {𝔈 : EWNKA[F,N,𝒮,Q]} {α_xs : Array Pk[F,N]} {β : Pk[F,N]} (h : 0 < α_xs.size) :
    (𝔈.semArray α_xs h).finish β = 𝔈.sem ⟨α_xs.toList.head (by grind [Array.ne_empty_of_size_pos]), α_xs.toList.tail, β⟩ := by
  rcases α_xs with ⟨_ | ⟨α, xs⟩⟩
  · simp at h
  simp [semArray, semArray_aux, sem, Precompute.finish]
  generalize 𝔈.ι = ι
  induction xs generalizing α ι with
  | nil => simp
  | cons x xs ih => simp at ih; simp [List.getLast?_cons, ← ih, Fin.foldl_succ]

theorem RPol.ewnka_sem_eq_wnka_sem (p : RPol[F,N,𝒮]) : p.ewnka.sem = 𝒜⟦~p⟧ := by
  ext ⟨α, xs, β⟩
  simp [ewnka, EWNKA.sem, RPol.𝒜_def, Matrix.mul_apply, EMatrix.mul_apply]
  congr! with s _
  ext ⟨⟩ s'
  generalize ι p = i
  symm
  induction xs generalizing α i s' with simp_all
  | cons x xs ih => congr!; ext; simp [EMatrix.mul_apply, Matrix.mul_apply]

/--
info: 'WeightedNetKAT.RPol.ewnka_sem_eq_wnka_sem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Matrix.Star.axiomNMatrixStarLeωSum]
-/
#guard_msgs in
#print axioms RPol.ewnka_sem_eq_wnka_sem

end
