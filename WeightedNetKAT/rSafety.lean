import WeightedNetKAT.WNKA
import WeightedNetKAT.WNKA.Explicit

open OmegaCompletePartialOrder
open scoped RightActions

open scoped WeightingNotation

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [Listed F] [DecidableEq F]
variable {N : Type} [Listed N] [DecidableEq N]
variable {𝒮 : Type} [Semiring 𝒮]

namespace rSafety

variable {Q 𝒮 : Type}
variable [Listed Q] [Fintype Q] [DecidableEq Q]
variable [Semiring 𝒮]
variable (𝒜 : WNKA F N 𝒮 Q)
variable (ℰ : EWNKA F N 𝒮 Q)
variable [Star 𝒮]

@[grind]
inductive Q'₀ where | qι | q𝒪 deriving DecidableEq, Fintype

instance : Listed Q'₀ where
  array := #[.qι, .q𝒪]
  size := 2
  nodup := by simp
  complete := by grind
  encode | .qι => 0 | .q𝒪 => 1

abbrev Q' (F N Q : Type) [Listed F] := (Q × Pk[F,N]) ⊕ Q'₀

def I : 𝒲[𝟙, Q' F N Q, 𝒮] := η₂ () (.inr .qι)
def Δ (β : Pk[F,N]) : 𝒲[Q' F N Q, Q' F N Q, 𝒮]
  | .inl (q, α), .inl (q', β') => if β = β' then 𝒜.δ α β q q' else 0
  | .inr .qι, .inl (q, β') => if β = β' then 𝒜.ι () q else 0
  | .inl (q, α), .inr .q𝒪 => 𝒜.𝒪 α β q ()

  | (.inr .q𝒪), (.inr .q𝒪) => 0
  | (.inr .q𝒪), (.inr .qι) => 0
  | (.inr .q𝒪), (.inl _) => 0
  | (.inr .qι), (.inr .q𝒪) => 0
  | (.inr .qι), (.inr .qι) => 0
  | (.inl _), (.inr .qι) => 0
def Λ : 𝒲[Q' F N Q, 𝟙, 𝒮] := η₂ (.inr .q𝒪) ()

def Δ_star : List Pk[F,N] → 𝒲[Q' F N Q, Q' F N Q, 𝒮]
  | [] => 1
  | α::x => Δ 𝒜 α * Δ_star x

-- def sem : List Pk[F,N] → 𝒮 := fun x ↦ (I * Δ_star 𝒜 x * Λ : 𝒲[_, _, 𝒮]) () ()

def M : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), Δ 𝒜 α

variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

noncomputable def M_star : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := Star.star (M 𝒜)

noncomputable def sem' :=
    ((I : 𝒲[𝟙, Q' F N Q, 𝒮]) * M_star 𝒜 * (Λ : 𝒲[Q' F N Q, 𝟙, 𝒮]) : 𝒲[_, _, 𝒮]) () ()

def EI : E𝒲[𝟙, Q' F N Q, 𝒮] := Eη₂ () (.inr .qι)
def EΔ (β : Pk[F,N]) : E𝒲[Q' F N Q, Q' F N Q, 𝒮] :=
  .ofFnSlow fun q q' ↦ match q, q' with
    | .inl (q, α), .inl (q', β') => if β = β' then ℰ.δ α β q q' else 0
    | .inr .qι, .inl (q, β') => if β = β' then ℰ.ι () q else 0
    | .inl (q, α), .inr .q𝒪 => ℰ.𝒪 α β q ()

    | (.inr .q𝒪), (.inr .q𝒪) => 0
    | (.inr .q𝒪), (.inr .qι) => 0
    | (.inr .q𝒪), (.inl _) => 0
    | (.inr .qι), (.inr .q𝒪) => 0
    | (.inr .qι), (.inr .qι) => 0
    | (.inl _), (.inr .qι) => 0
def EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮] := Eη₂ (.inr .q𝒪) ()

def EΔ_star : List Pk[F,N] → E𝒲[Q' F N Q, Q' F N Q, 𝒮]
  | [] => 1
  | α::x => EΔ ℰ α * EΔ_star x

def Esem : List Pk[F,N] → 𝒮 := fun x ↦
    ((EI : E𝒲[𝟙, Q' F N Q, 𝒮]) * EΔ_star ℰ x * (EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮]) : E𝒲[_, _, 𝒮]) () ()

def EM : E𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), EΔ ℰ α

def EM_star : E𝒲[Q' F N Q, Q' F N Q, 𝒮] :=
  let R := (EM ℰ)^*
  R

def Esem' :=
    ((EI : E𝒲[𝟙, Q' F N Q, 𝒮]) * EM_star ℰ * (EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮]) : E𝒲[_, _, 𝒮]) () ()

omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EI_eq_I : EI (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix I := by
  ext; simp [EI, I, η₂]
omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EΔ_eq_Δ {β} : EΔ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) ℰ β = EMatrix.ofMatrix (Δ ℰ.toWNKA β) := by
  ext; simp [EΔ, Δ]
omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EΛ_eq_Λ : EΛ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix Λ := by
  ext; simp [EΛ, Λ, η₂]

variable [LawfulStar 𝒮] [StarIter 𝒮]

omit [Fintype F] in
@[simp]
theorem Esem'_eq_sem' : Esem' ℰ = sem' ℰ.toWNKA := by
  simp [Esem', sem', EM_star, M_star]
  congr!
  ext i j
  simp only [EM, EΔ_eq_Δ, ← EMatrix.ofMatrix_sum, LawfulStar.star_eq_sum, EMatrix.asMatrix_apply₂,
    M, Matrix.ωSum_apply, ωSum_apply]
  show (ω∑ (n : ℕ), EMatrix.ofMatrix (∑ i, Δ ℰ.toWNKA i) ^ n) i j = _
  simp only [← EMatrix.ofMatrix_pow, EMatrix.ωSum_apply, EMatrix.ofMatrix_apply₂]

def sem'_fast := Esem' 𝒜.toEWNKA

variable [DecidableEq 𝒮]

def extraction_len (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let x := Listed.arrayOf (Pk[F,N] × Vector Pk[F,N] n × Pk[F,N])
  let y : Array (GS[F,N]) := x.map fun (α, xs, β) ↦ GS.mk α xs.toList β
  y.find? (ℰ.sem · = r)

partial def extraction_go [Inhabited F] [Inhabited N] (n : ℕ) (r : 𝒮) : GS[F,N] :=
  match extraction_len ℰ n r with
  | some ρ => ρ
  | none => extraction_go (n + 1) r

def extraction [Inhabited F] [Inhabited N] (r : 𝒮) : GS[F,N] := extraction_go ℰ 0 r

end rSafety

end WeightedNetKAT
