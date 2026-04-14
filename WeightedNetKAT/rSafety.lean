import WeightedNetKAT.WNKA
import WeightedNetKAT.WNKA.Explicit

open OmegaCompletePartialOrder
open scoped RightActions

open scoped WeightingNotation

namespace Listed

variable {α β : Type*} [Listed α] [Listed β]

def Li.getSum : Li[α ⊕ β] ≃ Li[α] ⊕ Li[β] where
  toFun i :=
    if hi : i < size α then .inl ⟨i, hi⟩ else .inr ⟨i - size α, by
      obtain ⟨i, hi'⟩ := i
      simp_all only [not_lt]
      simp [size] at hi'
      omega⟩
  invFun
  | .inl i => ⟨i, by simp [size]; omega⟩
  | .inr i => ⟨i + size α, by simp [size]; omega⟩
  left_inv := by
    intro ⟨i, hi⟩; simp
    split_ifs with h
    · simp
    · simp; omega
  right_inv := by rintro (_ | _) <;> simp

def Li.getProd : Li[α × β] ≃ Li[α] × Li[β] where
  toFun i := ⟨
    ⟨i / size β, (Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left i.isLt)).mpr i.isLt⟩,
    ⟨i % size β, Nat.mod_lt i (Nat.pos_of_lt_mul_left i.isLt)⟩⟩
  invFun := fun ⟨a, b⟩ ↦ ⟨a * size β + b, by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp_all [size]
    simp only [Nat.lt_iff_add_one_le] at *
    rw [add_assoc]
    grw [hb, ← ha]
    rw [← Nat.succ_mul]⟩
  left_inv := by intro ⟨i, hi⟩; simp [size] at hi ⊢; exact Nat.div_add_mod' i (size β)
  right_inv := by
    intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp [Nat.mod_eq_of_lt hb, Nat.div_eq_iff, Nat.zero_lt_of_lt hb]
    omega

theorem decodeFin_getSum (i : Li[α ⊕ β]) : decodeFin i = (Li.getSum i).map decodeFin decodeFin := by
  rw [← encodeFin_eq_iff]
  simp [Li.getSum]
  split_ifs <;> simp_all [encodeFin, encode, decodeFin]
  grind

theorem decodeFin_getProd (i : Li[α × β]) : decodeFin i = (Li.getProd i).map decodeFin decodeFin := by
  rw [← encodeFin_eq_iff]
  simp [Li.getProd]
  simp_all [encodeFin, encode, decodeFin, Nat.div_add_mod']

@[simp]
theorem Li.getSum_encodeFin (i : α ⊕ β) : Li.getSum (encodeFin i) = i.map encodeFin encodeFin := by
  rcases i with a | b
  · simp [Li.getSum]
    split_ifs with h
    · simp; rfl
    · contrapose! h; simp [encodeFin, encode, encode_lt_size]
  · simp [Li.getSum]
    split_ifs with h
    · contrapose! h; simp [encodeFin, encode]
    · simp_all [encodeFin, encode]

@[simp]
theorem Li.getProd_encodeFin (i : α × β) : Li.getProd (encodeFin i) = i.map encodeFin encodeFin := by
  obtain ⟨a, b⟩ := i
  simp [Li.getProd]
  simp [encodeFin, encode]
  have ha := encode_lt_size a
  have hb := encode_lt_size b
  simp +arith [Nat.div_eq_of_lt_le, Nat.mod_eq_of_lt, add_mul, hb]

end Listed

def EMatrix.ofFn_eq_ofFnSlow {m n α : Type*} [Listed m] [Listed n] (f : Li[m] → Li[n] → α) :
    EMatrix.ofFn f = EMatrix.ofFnSlow (m:=m) (n:=n) (fun a b ↦ f (Listed.encodeFin a) (Listed.encodeFin b)) := by
  ext
  simp

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

def M : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), Δ 𝒜 α

variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

noncomputable def M_star : 𝒲[Q' F N Q, Q' F N Q, 𝒮] := Star.star (M 𝒜)

noncomputable def sem' :=
    ((I : 𝒲[𝟙, Q' F N Q, 𝒮]) * M_star 𝒜 * (Λ : 𝒲[Q' F N Q, 𝟙, 𝒮]) : 𝒲[_, _, 𝒮]) () ()

def EI : E𝒲[𝟙, Q' F N Q, 𝒮] := Eη₂ () (.inr .qι)
def EΔ (β : Li[Pk[F,N]]) : E𝒲[Q' F N Q, Q' F N Q, 𝒮] :=
  .ofFn fun q q' ↦ match (Listed.Li.getSum q).map Listed.Li.getProd id, (Listed.Li.getSum q').map Listed.Li.getProd id with
    | .inl (q, α), .inl (q', β') => if β = β' then ℰ.δ.asNMatrix₂ α β q q' else 0
    | .inr 0, .inl (q, β') => if β = β' then ℰ.ι.asNMatrix 0 q else 0
    | .inl (q, α), .inr 1 => ℰ.𝒪.asNMatrix₂ α β q 0

    | (.inr 1), (.inr 1) => 0
    | (.inr 1), (.inr 0) => 0
    | (.inr 1), (.inl _) => 0
    | (.inr 0), (.inr 1) => 0
    | (.inr 0), (.inr 0) => 0
    | (.inl _), (.inr 0) => 0
def EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮] := Eη₂ (.inr .q𝒪) ()

def EΔ_star : List Li[Pk[F,N]] → E𝒲[Q' F N Q, Q' F N Q, 𝒮]
  | [] => 1
  | α::xs => EΔ ℰ α * EΔ_star xs
def EΔ_star' (acc : E𝒲[𝟙, Q' F N Q, 𝒮]) : List Li[Pk[F,N]] → E𝒲[𝟙, Q' F N Q, 𝒮]
  | [] => acc
  | α::xs => EΔ_star' (acc * EΔ ℰ α) xs

def Esem : List Li[Pk[F,N]] → 𝒮 := fun x ↦
    (EΔ_star' ℰ EI x * (EΛ : E𝒲[Q' F N Q, 𝟙, 𝒮]) : E𝒲[_, _, 𝒮]) () ()

def EM : E𝒲[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Li[Pk[F,N]]), EΔ ℰ α

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
theorem EΔ_eq_Δ {β} : EΔ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) ℰ β = EMatrix.ofMatrix (Δ ℰ.toWNKA (Listed.decodeFin β)) := by
  simp [EΔ, Δ]
  rw [EMatrix.ofFn_eq_ofFnSlow]
  simp
  ext i j; simp [EΔ, Δ]
  let β₀ := Listed.decodeFin β
  have : β = Listed.encodeFin β₀ := by simp [β₀]
  simp [this]
  have : (Listed.encodeFin Q'₀.qι) = 0 := by rfl
  have : (Listed.encodeFin Q'₀.q𝒪) = 1 := by rfl
  rcases i with i | i <;> rcases j with j | j
  · simp
    rfl
  · rcases j with _ | _ <;> simp_all
    rfl
  · rcases i with _ | i <;> simp_all
    rfl
  · rcases i with _ | _ <;> rcases j with _ | _ <;> simp_all

omit [Fintype F] [Fintype Q] [Star 𝒮] in
@[simp]
theorem EΛ_eq_Λ : EΛ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix Λ := by
  ext; simp [EΛ, Λ, η₂]

variable [LawfulStar 𝒮] [StarIter 𝒮]

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

omit [Fintype F] in
@[simp]
theorem Esem'_eq_sem' : Esem' ℰ = sem' ℰ.toWNKA := by
  simp [Esem', sem', EM_star, M_star]
  congr!
  ext i j
  simp only [EM, EΔ_eq_Δ, ← EMatrix.ofMatrix_sum, Listed.sum_fin, Listed.encodeFin_decodeFin,
    LawfulStar.star_eq_sum, EMatrix.asMatrix_apply₂, EMatrix.ωSum_apply, M, Matrix.ωSum_apply,
    ωSum_apply]
  simp only [← EMatrix.ofMatrix_pow, EMatrix.ofMatrix_apply₂]

def sem'_fast := Esem' 𝒜.toEWNKA

variable [DecidableEq 𝒮]

def extraction_len (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let x := Listed.arrayOf (Pk[F,N] × Vector Pk[F,N] n × Pk[F,N])
  let y : Array (GS[F,N]) := x.map fun (α, xs, β) ↦ GS.mk α xs.toList β
  y.find? (ℰ.sem · = r)
def extraction_len' (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let pks := Listed.arrayOf Pk[F,N]
  let x := Listed.arrayOf (Vector Pk[F,N] (n + 1))
  x.findSome?
    (fun α_xs ↦
      let ⟨m, γ⟩ := ℰ.semArray'' α_xs.toArray (by simp)
      pks.findSome? (fun β ↦ if (m * ℰ.𝒪 γ β) () () = r then some (α_xs, β) else none)
      )
  |>.map fun (α_xs, β) ↦ GS.mk α_xs.head α_xs.tail.toList β

partial def extraction_go [Inhabited F] [Inhabited N] (n : ℕ) (r : 𝒮) : GS[F,N] :=
  match extraction_len' ℰ n r with
  | some ρ => ρ
  | none => extraction_go (n + 1) r

def extraction [Inhabited F] [Inhabited N] (r : 𝒮) : GS[F,N] := extraction_go ℰ 0 r

end rSafety

end WeightedNetKAT
