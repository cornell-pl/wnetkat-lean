module

public import WeightedNetKAT.WNKA
public import WeightedNetKAT.WNKA.Explicit

@[expose] public section

open OmegaCompletePartialOrder
open scoped RightActions
open scoped Computability

open scoped MatrixNotation

def EMatrix.ofFn_eq_ofFnSlow {m n α : Type*} [Listed m] [Listed n] (f : Li[m] → Li[n] → α) :
    EMatrix.ofFn f = EMatrix.ofFnSlow (m:=m) (n:=n) (fun a b ↦ f (Listed.encodeFin a) (Listed.encodeFin b)) := by
  ext
  simp

namespace WeightedNetKAT

variable {F : Type*} [Fintype F] [Listed F] [DecidableEq F]
variable {N : Type*} [Listed N] [DecidableEq N]
variable {𝒮 : Type*} [Semiring 𝒮]

def rSafety [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] (p : Pol[F,N,𝒮]) (r : 𝒮) : Prop :=
  ∀ (π : Pk[F,N]) (h : H[F,N]), p.sem ⟨π, []⟩ h ≤ r

namespace rSafety

variable {Q 𝒮 : Type*}
variable [Listed Q] [Fintype Q] [DecidableEq Q]
variable [Semiring 𝒮]
variable (𝔄 : WNKA F N 𝒮 Q)
variable (𝔈 : EWNKA F N 𝒮 Q)
variable [KStar 𝒮]

@[grind]
inductive Q'₀ where | qι | q𝒪 deriving DecidableEq, Fintype

instance : Listed Q'₀ where
  array := #[.qι, .q𝒪]
  size := 2
  nodup := by simp
  complete := by grind
  encode | .qι => 0 | .q𝒪 => 1

abbrev Q' (F N Q : Type*) [Listed F] := (Q × Pk[F,N]) ⊕ Q'₀

def I : 𝕄[𝟙, Q' F N Q, 𝒮] := η₂ () (.inr .qι)
def Δ (β : Pk[F,N]) : 𝕄[Q' F N Q, Q' F N Q, 𝒮]
  | .inl (q, α), .inl (q', β') => if β = β' then 𝔄.δ α β q q' else 0
  | .inr .qι, .inl (q, β') => if β = β' then 𝔄.ι () q else 0
  | .inl (q, α), .inr .q𝒪 => 𝔄.𝒪 α β q ()

  | (.inr .q𝒪), (.inr .q𝒪) => 0
  | (.inr .q𝒪), (.inr .qι) => 0
  | (.inr .q𝒪), (.inl _) => 0
  | (.inr .qι), (.inr .q𝒪) => 0
  | (.inr .qι), (.inr .qι) => 0
  | (.inl _), (.inr .qι) => 0
def Λ : 𝕄[Q' F N Q, 𝟙, 𝒮] := η₂ (.inr .q𝒪) ()

def Δ_star : List Pk[F,N] → 𝕄[Q' F N Q, Q' F N Q, 𝒮]
  | [] => 1
  | α::x => Δ 𝔄 α * Δ_star x

def M : 𝕄[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Pk[F,N]), Δ 𝔄 α

variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [KStar 𝒮]

noncomputable def M_star : 𝕄[Q' F N Q, Q' F N Q, 𝒮] := KStar.kstar (M 𝔄)

noncomputable def sem' [Listed Q] [KStar 𝒮] :=
    ((I : 𝕄[𝟙, Q' F N Q, 𝒮]) * M_star 𝔄 * (Λ : 𝕄[Q' F N Q, 𝟙, 𝒮]) : 𝕄[_, _, 𝒮]) () ()

def EI : E𝕄[𝟙, Q' F N Q, 𝒮] := Eη₂ () (.inr .qι)
def EΔ (β : Li[Pk[F,N]]) : E𝕄[Q' F N Q, Q' F N Q, 𝒮] :=
  .ofFn fun q q' ↦ match (Listed.Li.getSum q).map Listed.Li.getProd id, (Listed.Li.getSum q').map Listed.Li.getProd id with
    | .inl (q, α), .inl (q', β') => if β = β' then 𝔈.δ.asNMatrix₂ α β q q' else 0
    | .inr 0, .inl (q, β') => if β = β' then 𝔈.ι.asNMatrix 0 q else 0
    | .inl (q, α), .inr 1 => 𝔈.𝒪.asNMatrix₂ α β q 0

    | (.inr 1), (.inr 1) => 0
    | (.inr 1), (.inr 0) => 0
    | (.inr 1), (.inl _) => 0
    | (.inr 0), (.inr 1) => 0
    | (.inr 0), (.inr 0) => 0
    | (.inl _), (.inr 0) => 0
def EΛ : E𝕄[Q' F N Q, 𝟙, 𝒮] := Eη₂ (.inr .q𝒪) ()

def EΔ_star : List Li[Pk[F,N]] → E𝕄[Q' F N Q, Q' F N Q, 𝒮]
  | [] => 1
  | α::xs => EΔ 𝔈 α * EΔ_star xs
def EΔ_star' (acc : E𝕄[𝟙, Q' F N Q, 𝒮]) : List Li[Pk[F,N]] → E𝕄[𝟙, Q' F N Q, 𝒮]
  | [] => acc
  | α::xs => EΔ_star' (acc * EΔ 𝔈 α) xs

def Esem : List Li[Pk[F,N]] → 𝒮 := fun x ↦
    (EΔ_star' 𝔈 EI x * (EΛ : E𝕄[Q' F N Q, 𝟙, 𝒮]) : E𝕄[_, _, 𝒮]) () ()

def EM : E𝕄[Q' F N Q, Q' F N Q, 𝒮] := ∑ (α : Li[Pk[F,N]]), EΔ 𝔈 α

def EM_star : E𝕄[Q' F N Q, Q' F N Q, 𝒮] :=
  let R := (EM 𝔈)∗
  R

def Esem' :=
    ((EI : E𝕄[𝟙, Q' F N Q, 𝒮]) * EM_star 𝔈 * (EΛ : E𝕄[Q' F N Q, 𝟙, 𝒮]) : E𝕄[_, _, 𝒮]) () ()

omit [Fintype F] [Fintype Q] [KStar 𝒮] in
@[simp]
theorem EI_eq_I : EI (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix I := by
  ext; simp [EI, I, η₂]
omit [Fintype F] [Fintype Q] [KStar 𝒮] in
@[simp]
theorem EΔ_eq_Δ {β} : EΔ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) 𝔈 β = EMatrix.ofMatrix (Δ 𝔈.toWNKA (Listed.decodeFin β)) := by
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
  · rcases i with _ | _ <;> rcases j with _ | _ <;> simp_all

omit [Fintype F] [Fintype Q] [KStar 𝒮] in
@[simp]
theorem EΛ_eq_Λ : EΛ (F:=F) (N:=N) (𝒮:=𝒮) (Q:=Q) = EMatrix.ofMatrix Λ := by
  ext; simp [EΛ, Λ, η₂]

variable [LawfulKStar 𝒮] [KStarIter 𝒮]

variable [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]

omit [Fintype F] in
@[simp]
theorem Esem'_eq_sem' : Esem' 𝔈 = sem' 𝔈.toWNKA := by
  simp [Esem', sem', EM_star, M_star, EMatrix.mul_apply, Matrix.mul_apply]
  suffices DFunLike.coe (EM 𝔈)∗ = (M 𝔈.toWNKA)∗ by congr!
  ext
  simp [LawfulKStar.kstar_eq_sum, EM, M]
  congr! with n
  ext α β
  induction n generalizing α β with
  | zero =>
    simp
    show (1 : NMatrix _ _ 𝒮) (Listed.encodeFin α) (Listed.encodeFin β) = _
    simp
    rfl
  | succ n ih =>
    simp [pow_succ, ih, EMatrix.mul_apply, Matrix.mul_apply, Matrix.sum_apply]


def ErSafety [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [LawfulKStar 𝒮] (p : Pol[F,N,𝒮]) (r : 𝒮) : Prop :=
  Esem' p.toRPol.ewnka ≤ r

def sem'_fast {F : Type*} [Listed F] [DecidableEq F] {N : Type*} [Listed N] [DecidableEq N] {Q 𝒮 : Type*}
  [Fintype Q] [DecidableEq Q] [Semiring 𝒮] (𝔄 : WNKA[F,N,𝒮,Q]) [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮] [Listed Q] [KStar 𝒮] := Esem' 𝔄.toEWNKA

def _root_.WeightedNetKAT.RPol.wnkaFast {F : Type*} [Listed F] {N : Type*} [Listed N] {𝒮 : Type*} [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [DecidableEq N] [DecidableEq F] [KStar 𝒮] [LawfulKStar 𝒮]
  (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] := p.ewnka.toWNKA

theorem rSafety_iff [Inhabited Pk[F,N]] {p : Pol[F,N,𝒮]} {r} :
    rSafety p r ↔ ∀ (x : GS[F,N]), 𝒜⟦~p.toRPol⟧ x ≤ r := by
  simp [rSafety, Pol.sem_eq_toRPol_𝒜]
  constructor
  · intro h ⟨π, x, γ⟩
    specialize h π γ x.reverse

    grind
  · intro h π x γ
    grind
theorem rSafety_iff' [Inhabited Pk[F,N]] {p : Pol[F,N,𝒮]} {r} :
    rSafety p r ↔ ω∑ (x : GS[F,N]), 𝒜⟦~p.toRPol⟧ x ≤ r := by
  rw [rSafety_iff]
  constructor
  · intro h
    apply ωSum_le_of_finset fun S ↦ ?_
    sorry
  · intro h x
    grw [← h, ← le_ωSum_of_finset (S:={x})]
    simp

section

local instance {n} : Fintype (Vector Pk[F,N] n) := Listed.fintype

theorem ωSum_GS_eq_ωSum_nat {f : GS[F,N] → 𝒮} : ω∑ (x : GS F N), f x = ω∑ n, ∑ (α : Pk[F,N]) (xs : Vector Pk[F,N] n) (β : Pk[F,N]), f ⟨α, xs.toList, β⟩ := by
  sorry

end

theorem rSafety_iff'' [Inhabited Pk[F,N]] {p : Pol[F,N,𝒮]} {r} :
    rSafety p r ↔ sem' p.toRPol.wnka ≤ r := by
  rw [rSafety_iff']
  congr!
  simp [sem']
  simp [I, Λ, M_star, M, Δ]
  simp [Matrix.mul_apply]
  rw [LawfulKStar.kstar_eq_sum]
  simp
  rw [ωSum_GS_eq_ωSum_nat]
  nth_rw 2 [ωSum_nat_eq_succ]
  simp
  nth_rw 2 [ωSum_nat_eq_succ]
  simp [Matrix.sum_apply, Δ]
  congr with n
  induction n with
  | zero =>
    simp [Matrix.sum_apply, Δ, pow_succ, Matrix.mul_apply]
    sorry
  | succ n ih =>
    simp [Matrix.sum_apply, pow_succ, Matrix.mul_apply]
    sorry

theorem rSafety_iff_ErSafety [Inhabited Pk[F,N]] {p : Pol[F,N,𝒮]} {r} : rSafety p r ↔ ErSafety p r := by
  rw [rSafety_iff'']
  simp [ErSafety]

instance [DecidableRel (· ≤ · : 𝒮 → 𝒮 → Prop)] {p : Pol[F,N,𝒮]} {r} : Decidable (ErSafety p r) := by
  rw [ErSafety]
  exact inferInstance

variable [DecidableEq 𝒮]

/-- Enumerate _all_ GS and check their weight

Example execution time: **N/A**
-/
def extraction_len (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let x := Listed.arrayOf (Pk[F,N] × Vector Pk[F,N] n × Pk[F,N])
  let y : Array (GS[F,N]) := x.map fun (α, xs, β) ↦ ⟨α, xs.toList, β⟩
  y.find? (𝔈.sem · = r)
/-- Enumerate _all_ GS and check their weight, reusing computation up to the exit weight

Example execution time: **113.988409s**
-/
def extraction_len' (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let pks := Listed.arrayOf Pk[F,N]
  let x := Listed.arrayOf (Vector Pk[F,N] (n + 1))
  x.findSome?
    (fun α_xs ↦
      let f := 𝔈.semArray α_xs.toArray (by simp)
      pks.findSome? (fun β ↦ if f.finish β = r then some (α_xs, β) else none))
  |>.map fun (α_xs, β) ↦ ⟨α_xs.head, α_xs.tail.toList, β⟩

def extraction_len'' (acc : E𝕄[𝟙, Q, 𝒮]) (n : ℕ) (γ : Li[Pk[F,N]]) (r : 𝒮) : Option GS[F,N] :=
  let pks := Listed.arrayOf Li[Pk[F,N]]
  match n with
  | 0 =>
    pks.findSome? (fun β ↦ if (acc * 𝔈.𝒪.asNMatrix γ β) () () = r then some ⟨Listed.decodeFin γ, [], Listed.decodeFin β⟩ else none)
  | n + 1 =>
    pks.findSome? (fun β ↦ if let some gs := extraction_len'' (acc * 𝔈.δ.asNMatrix γ β) n β r then (some ⟨Listed.decodeFin γ, gs.1 :: gs.2.1, gs.2.2⟩) else none)

/-- Enumerate _all_ GS and check their weight, reusing computation up for every prefix

Example execution time: **30.157497s**
-/
def extraction_len₀ (n : ℕ) (r : 𝒮) : Option GS[F,N] :=
  let pks := Listed.arrayOf Li[Pk[F,N]]
  pks.findSome? (extraction_len'' 𝔈 𝔈.ι n · r)

partial def extraction_go [Inhabited F] [Inhabited N] (n : ℕ) (r : 𝒮) : GS[F,N] :=
    match extraction_len₀ 𝔈 n r with
    | some ρ => ρ
    | none => extraction_go (n + 1) r

def extraction [Inhabited F] [Inhabited N] (r : 𝒮) : GS[F,N] := extraction_go 𝔈 0 r

end rSafety

end WeightedNetKAT
