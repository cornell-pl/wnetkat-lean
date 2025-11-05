import WeightedNetKAT.WNKA

open OmegaCompletePartialOrder
open scoped RightActions

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [Listed F] [DecidableEq F]
variable {N : Type} [Listed N] [DecidableEq N]
variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

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

def sem : List Pk[F,N] → 𝒮 := fun x ↦ (I * Δ_star 𝒜 x * Λ : 𝒲[_, _, 𝒮]) () ()

def M : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), Δ 𝒜 α

def M_star : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := (M 𝒜)^*

def sem' :=
    ((I : 𝒲[𝟙, Q' F N Q, 𝒮]) * M_star 𝒜 * (Λ : 𝒲[Q' F N Q, 𝟙, 𝒮]) : 𝒲[_, _, 𝒮]) () ()

def EI : E𝒲[𝟙, Q' F N Q, 𝒮] := Eη₂ () (.inr .qι)
def EΔ (β : Pk[F,N]) : E𝒲[Q' F N Q, Q' F N Q, 𝒮] :=
  .ofFnSlow fun q q' ↦ match q, q' with
    | .inl (q, α), .inl (q', β') => if β = β' then (ℰ.δ.get α β).get q q' else 0
    | .inr .qι, .inl (q, β') => if β = β' then ℰ.ι.get () q else 0
    | .inl (q, α), .inr .q𝒪 => (ℰ.𝒪.get α β).get q ()

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
    ((EI : E𝒲[𝟙, Q' F N Q, 𝒮]) * EΔ_star ℰ x * (EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮]) : E𝒲[_, _, 𝒮]).get () ()

def EM : E𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), EΔ ℰ α

def EM_star : E𝒲[Q' F N Q, Q' F N Q, 𝒮] :=
  let R := (EM ℰ |>.asNMatrix)^*
  R

def Esem' :=
    ((EI : E𝒲[𝟙, Q' F N Q, 𝒮]) * EM_star ℰ * (EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮]) : E𝒲[_, _, 𝒮]).get () ()

omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EI_eq_I : EI (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix I := by
  ext; simp [EI, I, η₂]
omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EΔ_eq_Δ {β} : EΔ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) ℰ β = EMatrix.ofMatrix (Δ ℰ.toWNKA β) := by
  ext; simp [EΔ, Δ]
  split <;> try simp_all [EMatrix.get_eq_asMatrix]
omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EΛ_eq_Λ : EΛ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix Λ := by
  ext; simp [EΛ, Λ, η₂]

omit [Fintype F] in
@[simp]
theorem Esem'_eq_sem' : Esem' ℰ = sem' ℰ.toWNKA := by
  simp [Esem', sem', EM_star, EM, M_star]
  congr! 2
  simp [Star.star, Matrix.listedEquivNat, Matrix.Star.star_fin]
  ext
  simp [EMatrix.asMatrix, NMatrix.asMatrix]
  congr
  ext
  simp [M]
  simp [EMatrix.get_eq_asMatrix]

def sem'_fast := Esem' 𝒜.toEWNKA

@[csimp] theorem sem'_csimp : @sem' = @sem'_fast := by ext; simp [sem'_fast]

end rSafety

end WeightedNetKAT
