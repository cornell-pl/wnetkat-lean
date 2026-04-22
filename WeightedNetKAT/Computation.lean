module

public import WeightedNetKAT.Approximate
public import WeightedNetKAT.FinsuppExt

@[expose] public section

variable {X : Type*} {𝒮 : Type*}
  [Semiring 𝒮]
  [PartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]
  [DecidableEq 𝒮]

variable {F : Type*} [Listed F] [DecidableEq F]
variable {N : Type*} [DecidableEq N]

namespace WeightedNetKAT

open Finsupp (η')

def Pred.compute (p : Pred[F,N]) : H[F,N] → H[F,N] →₀ 𝒮 := fun ⟨π, h⟩ ↦ if p.test π then η' ⟨π, h⟩ else 0

def Pol.compute (p : Pol[F,N,𝒮]) (n : ℕ) : H[F,N] → H[F,N] →₀ 𝒮 := match p with
  | wnk_pol {@filter ~t} => t.compute
  | wnk_pol {~f ← ~n} => fun (π, h) ↦ η' (π[f ↦ n], h)
  | wnk_pol {dup} => fun (π, h) ↦ η' (π, π::h)
  | wnk_pol {~p; ~q} => fun h ↦ (p.compute n h).bind (q.compute n)
  | wnk_pol {~w ⨀ ~p}=> fun h ↦ w * p.compute n h
  | wnk_pol {~p ⨁ ~q} => fun h ↦ p.compute n h + q.compute n h
  | wnk_pol {~p*} => fun h ↦ ∑ i ∈ Finset.range n, (p ^ i).compute n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

end WeightedNetKAT

section

def Finset.toList' {α : Type*} [Encodable α] [DecidableEq α] (s : Finset α) : List α := s.val.rep

def Finsupp.pretty [DecidableEq X] (m : X →₀ 𝒮) : Finset (X × 𝒮) := m.support.image (fun s ↦ (s, m s))
unsafe instance 𝒞.repr [DecidableEq X] [Repr X] [Repr 𝒮] : Repr (X →₀ 𝒮) where
  reprPrec m n := reprPrec m.pretty n

end

section

variable {X : Type*} {𝒮 : Type*}
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [Semiring 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [DecidableEq 𝒮]
variable {F : Type*} [Listed F] [DecidableEq F]
variable {N : Type*} [DecidableEq N]

def Finsupp.to𝒲 (m : H[F,N] →₀ 𝒮) : H[F,N] →c 𝒮 := ⟨m.toFun, Set.Finite.countable m.hasFiniteSupport⟩

@[simp] def Finsupp.to𝒲_apply (m : H[F,N] →₀ 𝒮) (x : H[F,N]) : m.to𝒲 x = m x := rfl
@[simp] def Finsupp.to𝒲_eq_zero (m : H[F,N] →₀ 𝒮) : m.to𝒲 = 0 ↔ m = 0 := by
  constructor
  · intro h
    ext x
    exact congrFun (congrArg DFunLike.coe h) x
  · simp_all [to𝒲]; intro _; rfl

noncomputable instance (m : H[F,N] →₀ 𝒮) : Fintype ↑m.to𝒲.support := m.hasFiniteSupport.fintype

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem 𝒲.bind_of_𝒞' [Listed N] (m : H[F,N] →₀ 𝒮) (f : H[F,N] → H[F,N] →c 𝒮) :
    (m.to𝒲.bind fun h ↦ f h) = ∑ h ∈ m.support, ⟨fun h' ↦ m h * f h h', SetCoe.countable (Function.support fun h' ↦ m h * (f h) h')⟩ := by
  have : Finite m.to𝒲.support := by
    refine Set.Finite.ofFinset m.support fun x ↦ ?_
    simp_all
  ext h
  simp
  rw [ωSum_fintype]
  refine Finset.sum_bij (fun x _ ↦ x) (fun a ↦ ?_) ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := a; simp_all; exact ha
  · simp
  · simp
  · simp_all

open WeightedNetKAT (η)
open Finsupp (η')

omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem 𝒲.η_eq_η' (x : H[F,N]) : η (α:=𝒮) x = (η' x).to𝒲 := by ext; simp

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
@[simp]
theorem 𝒲.bind_of_𝒞 [Listed N] (m : H[F,N] →₀ 𝒮) (f : H[F,N] → H[F,N] →₀ 𝒮) :
    (m.to𝒲.bind fun h ↦ (f h).to𝒲) = (m.bind f).to𝒲 := by
  ext; simp [bind_of_𝒞', ne_eq, Finsupp.bind]
  rw [← Finset.sum_attach]

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem 𝒲.η_bind [Listed N] (x : H[F,N]) (f : H[F,N] → H[F,N] →c 𝒮) :
    (η x).bind f = ⟨fun h ↦ η x x * f x h, SetCoe.countable _⟩ := by
  simp [𝒲.η_eq_η']
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm]; rfl
  else simp_all

namespace WeightedNetKAT

attribute [local simp] Pred.sem Pred.compute in
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
omit [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
theorem Pred.compute_eq_sem_n (p : Pred[F,N]) :
    p.sem (𝒮:=𝒮) = fun h ↦ (p.compute h).to𝒲 := by
  ext
  rw [Pred.sem]
  simp
  split_ifs <;> simp_all

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮] in
variable [Listed N] in
attribute [local simp] Pol.sem_n Pol.compute in
theorem Pol.compute_eq_sem_n (p : Pol[F,N,𝒮]) (n : ℕ) : p.sem_n n = fun h ↦ (p.compute n h).to𝒲 := by
  induction p with
  | Filter t => simp [sem_n, compute]; apply Pred.compute_eq_sem_n
  | Mod f e => ext; simp
  | Dup => ext; simp
  | Seq p q ihp ihq => simp_all only [sem_n, 𝒲.bind_of_𝒞, compute]
  | Weight w p =>
    simp_all
    congr
  | Add p q ihp ihq =>
    ext h
    simp_all
  | Iter p ih =>
    simp_all
    congr with h h'
    simp
    congr with x
    suffices (p.iter x).sem_n n = (fun h ↦ (p.iter x).compute n h |>.to𝒲) by simp [this]
    induction x with
    | zero => ext; simp [Pred.sem, Pred.compute, η', Pred.test]
    | succ x ihx => simp_all only [iter, sem_n, 𝒲.bind_of_𝒞, compute]

end WeightedNetKAT

end
