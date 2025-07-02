import WeightedNetKAT.Semantics
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Order

section

variable {X : Type} {𝒮 : Type} [WeightedPartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮]
variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]

instance : FunLike (𝒞 𝒮 X) X 𝒮 where
  coe m := m.toFun
  coe_injective' := by
    intro a b h
    rcases a with ⟨⟨a, a_countable⟩, asupp, ah⟩
    rcases b with ⟨⟨b, b_cpuntable⟩, bsupp, bh⟩
    congr
    simp_all only
    apply Set.ext_iff.mp at ah
    apply Set.ext_iff.mp at bh
    ext
    simp_all only [Finset.mem_coe, W.supp_mem_iff, ne_eq]

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem 𝒞.to𝒲_apply {m : 𝒞 𝒮 X} (x : X) : m.to𝒲 x = m x := by rfl

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem 𝒞.mk_apply {to𝒲 : 𝒲 𝒮 X} {finSupp} {finSupp_eq_supp} (x : X) :
    (𝒞.mk to𝒲 finSupp finSupp_eq_supp) x = to𝒲 x := by rfl

omit [DecidableEq 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem 𝒞.mem_supp_iff {m : 𝒞 𝒮 X} (x : X) : x ∈ m.supp ↔ m x ≠ 𝟘 := by
  simp_all
omit [DecidableEq 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem 𝒞.mem_finSupp_iff {m : 𝒞 𝒮 X} (x : X) : x ∈ m.finSupp ↔ m x ≠ 𝟘 := by
  have := m.finSupp_eq_supp
  apply Set.ext_iff.mp at this
  simp_all

instance {m : 𝒞 𝒮 X} : Countable m.supp := m.countable
noncomputable instance {m : 𝒞 𝒮 X} : Encodable m.supp := Encodable.ofCountable _

omit [DecidableEq 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[ext]
theorem 𝒞.ext (C₁ C₂ : 𝒞 𝒮 X)
    (h : ∀ i, C₁ i = C₂ i) : C₁ = C₂ := DFunLike.coe_injective <| funext h

instance : DecidableEq (𝒞 𝒮 H[F,N]) := fun m m' ↦
  if h : m.finSupp = m'.finSupp ∧ m.finSupp.filter (fun x ↦ m x ≠ m' x) = ∅ then
    .isTrue (by
      obtain ⟨h, h'⟩ := h
      ext i
      simp [Finset.filter_eq_empty_iff] at h'
      if hi : i ∈ m.finSupp then exact h' ((𝒞.mem_finSupp_iff i).mp hi)
      else grind [𝒞.mem_finSupp_iff])
  else
    .isFalse (by contrapose! h; simp_all)

open WeightedPreSemiring in
instance : WeightedZero (𝒞 𝒮 X) where
  wZero := ⟨𝟘, ∅, by ext; simp⟩

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
@[simp]
theorem 𝒞.wZero_to𝒲 : (𝟘 : 𝒞 𝒮 X).to𝒲 = 𝟘 := rfl
omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
@[simp]
theorem 𝒞.wZero_apply {x : X} : (𝟘 : 𝒞 𝒮 X) x = 𝟘 := rfl

open WeightedPreSemiring in
instance [DecidableEq X] : WeightedAdd (𝒞 𝒮 X) where
  wAdd a b := ⟨a.to𝒲 ⨁ b.to𝒲, a.finSupp ∪ b.finSupp, by
    ext; simp [WeightedAdd.wAdd]
    grind⟩

omit [DecidableEq 𝒮] in
@[simp]
theorem 𝒞.wAdd_apply [DecidableEq X] {m m' : 𝒞 𝒮 X} {x : X} : (m ⨁ m') x = m x ⨁ m' x := rfl

open WeightedPreSemiring in
instance [DecidableEq X] : WeightedPreSemiring (𝒞 𝒮 X) where
  wMul a b := ⟨a.to𝒲 ⨀ b.to𝒲, (a.finSupp ∩ b.finSupp).filter fun x ↦ a.to𝒲 x ⨀ b.to𝒲 x ≠ 𝟘 , by
    ext; simp [WeightedMul.wMul]
    contrapose!
    simp
    intro h
    apply Decidable.not_or_of_imp at h
    rcases h with (h | h) <;> simp_all⟩
  wNsmul n m := if h0 : n = 0 then 𝟘 else ⟨wNsmul n m.to𝒲, m.finSupp.filter (fun x ↦ wNsmul n (m.to𝒲 x) ≠ 𝟘), by
    ext x; simp_all [wNsmul, instPi]
    constructor
    · contrapose!
      intro h h0'
      clear h0
      induction n with
      | zero => simp only [wNsmul_wZero]
      | succ => simp_all only [ne_eq, 𝒲.wNsmul, WeightedAdd.wAdd, 𝒞.to𝒲_apply, 𝒲.mk_apply,
        wAdd_eq_zero_iff, and_false]
    · contrapose!
      intro h
      apply Decidable.not_or_of_imp at h
      clear h0
      rcases h with h | h
      · induction n with
        | zero => simp only [𝒲.wNsmul, WeightedZero.instCountablePi, 𝒲.mk_apply]
        | succ n ih => simp_all only [ne_eq, Decidable.not_not, 𝒲.wNsmul, WeightedAdd.wAdd,
          𝒞.to𝒲_apply, 𝒲.mk_apply, add_wZero]
      · induction n with
        | zero => simp only [𝒲.wNsmul, WeightedZero.instCountablePi, 𝒲.mk_apply]
        | succ n ih =>
          simp_all only [wNsmul_succ, wAdd_eq_zero_iff, 𝒲.wNsmul, WeightedAdd.wAdd, 𝒞.to𝒲_apply,
            𝒲.mk_apply, add_wZero]
          apply ih
          clear ih h
          induction n with
          | zero => simp [wNsmul_wZero]
          | succ => simp_all [wNsmul_wZero, wNsmul_succ]
    ⟩
  wAdd_assoc _ _ _ := by ext; apply wAdd_assoc
  wZero_add _ := by ext; apply wZero_add
  add_wZero _ := by ext; apply add_wZero
  wNsmul_wZero _ := by simp
  wNsmul_succ _ _ := by
    ext x
    simp; split_ifs
    · simp_all [wNsmul_wZero, wNsmul_succ]
    · simp_all [wNsmul_succ, WeightedAdd.wAdd]
  wAdd_comm a b := by ext; apply wAdd_comm
  left_distrib a b c := by ext; apply WeightedPreSemiring.left_distrib
  right_distrib a b c := by ext; apply WeightedPreSemiring.right_distrib
  wZero_mul := by intro; simp only [𝒞.wZero_to𝒲, wZero_mul, WeightedZero.instCountablePi_apply,
    𝒞.to𝒲_apply, ne_eq, not_true_eq_false, Finset.filter_False]; rfl
  mul_wZero := by intro; simp only [𝒞.wZero_to𝒲, mul_wZero, 𝒞.to𝒲_apply,
    WeightedZero.instCountablePi_apply, ne_eq, not_true_eq_false, Finset.filter_False]; rfl
  mul_assoc a b c := by ext; apply WeightedPreSemiring.mul_assoc

@[simp]
def 𝒞.mk' (f : X → 𝒮) (finSupp : Finset X) (h : ∀ x, x ∈ W.supp f ↔ x ∈ finSupp) : 𝒞 𝒮 X :=
  let h : finSupp = W.supp f := by ext; simp_all
  ⟨⟨f, by rw [← h]; exact Finite.to_countable⟩, finSupp, h⟩

instance 𝒞.instwProdWeightedOne {𝒮 X : Type} [Fintype X] [WeightedSemiring 𝒮] [DecidableEq 𝒮] :
    WeightedOne (𝒞 𝒮 X) where
  wOne :=
    if h : ¬(𝟙 : 𝒮) = 𝟘 then 𝒞.mk' (fun _ ↦ 𝟙) Fintype.elems (by simp [h, Fintype.complete])
    else 𝟘

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem 𝒞.wOne_apply {X : Type} [Fintype X] (x) : (𝟙 : 𝒞 𝒮 X) x = 𝟙 := by
  simp [WeightedOne.wOne]
  split_ifs <;> grind [𝒞.wZero_apply, 𝒞.mk_apply, 𝒲.mk_apply]

def 𝒞.bind {X Y : Type} [DecidableEq X] [DecidableEq Y] (m : 𝒞 𝒮 X) (f : X → 𝒞 𝒮 Y) :
    𝒞 𝒮 Y :=
  𝒞.mk' (fun y ↦ ⨁ᶠ x ∈ m.finSupp, m x ⨀ f x y)
    (m.finSupp.biUnion (fun x ↦ (f x).finSupp.filter (fun y ↦ m x ⨀ f x y ≠ 𝟘)))
    (by
      intro y
      simp
      congr! 2 with x
      simp
      contrapose!
      simp
      intro h₁ h₂
      simp_all)

def η' {X : Type} [DecidableEq X] (x : X) : 𝒞 𝒮 X := 𝒞.mk'
  (fun y ↦ if x = y then 𝟙 else 𝟘)
  (if (𝟙 : 𝒮) = 𝟘 then ∅ else {x})
  (by intro; split_ifs <;> simp_all [eq_comm])

notation "η'[" 𝒮 "]" => η' (𝒮:=𝒮)

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem η'_apply {X : Type} [DecidableEq X] (x y : X) :
    η'[𝒮] x y = if x = y then 𝟙 else 𝟘 :=
  rfl

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem η'_finSupp {X : Type} [DecidableEq X] (x : X) :
    (η'[𝒮] x).finSupp = if (𝟙 : 𝒮) = 𝟘 then ∅ else {x} := rfl

instance {X : Type} : SMul 𝒮 (𝒞 𝒮 X) where
  smul w m := 𝒞.mk' (fun h' ↦ w ⨀ m h')
    (m.finSupp.filter (fun h' ↦ w ⨀ m h' ≠ 𝟘))
    (by
      intro h'
      simp_all only [W.supp_mem_iff, ne_eq, Finset.mem_filter, 𝒞.mem_finSupp_iff, iff_and_self]
      contrapose!
      simp_all)

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp] theorem 𝒞.sMul_apply {X : Type} (m : 𝒞 𝒮 X) (w : 𝒮) (x : X) : (w • m) x = w ⨀ m x := rfl
omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp] theorem 𝒞.one_sMul {X : Type} (m : 𝒞 𝒮 X) : (𝟙 : 𝒮) • m = m := by ext; simp
omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp] theorem 𝒞.zero_sMul {X : Type} (m : 𝒞 𝒮 X) : (𝟘 : 𝒮) • m = 𝟘 := by ext; simp

namespace WeightedNetKAT

def Predicate.compute (p : Predicate[F,N]) (n : ℕ) : H[F,N] → 𝒞 𝒮 H[F,N] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η'
  | wnk_pred {~f = ~n} => fun (π, h) ↦ if π f = n then η' (π, h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.compute n h |>.bind (fun h ↦ η' h ⨁ ((if t.compute n h = 𝟘 then η' h else 𝟘).bind (u.compute n))))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ (t.compute n h).bind (u.compute n)
  | wnk_pred {¬~t} => fun h ↦ if t.compute n h = 𝟘 then η' h else 𝟘
def Policy.compute (p : Policy[F,N,𝒮]) (n : ℕ) : H[F,N] → 𝒞 𝒮 H[F,N] := match p with
  | .Filter t => t.compute n
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η' (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η' (π, π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.compute n h).bind (q.compute n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w • p.compute n h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.compute n h ⨁ q.compute n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁ᶠ i ∈ Finset.range n, (p ^ i).compute n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

end WeightedNetKAT

end

section

variable {X : Type} {𝒮 : Type} [WeightedPartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮]
variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

def Finset.toList' {α : Type} [Encodable α] [DecidableEq α] (s : Finset α) : List α := s.val.rep

instance {F : Type} [i : Fintype F] [e : Encodable F] [Repr F] [Repr N] : Repr Pk[F,N] where
  reprPrec x _ := s!"\{{List.range i.card |>.filterMap e.decode |>.map (fun k ↦ s!"{reprStr k}↦{reprStr (x k)}") |> ",".intercalate}}"

def 𝒞.pretty [DecidableEq X] (m : 𝒞 𝒮 X) : Finset (X × 𝒮) := m.finSupp.image (fun s ↦ (s, m s))
unsafe instance 𝒞.repr [DecidableEq X] [Repr X] [Repr 𝒮] : Repr (𝒞 𝒮 X) where
  reprPrec m n := reprPrec m.pretty n

end

section

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮]
variable {F : Type} [Fintype F]
variable {N : Type} [Fintype N] [DecidableEq N]

omit [DecidableEq 𝒮] in
@[simp]
theorem 𝒲.bind_of_𝒞' (m : 𝒞 𝒮 H[F,N]) (f : H[F,N] → 𝒲 𝒮 H[F,N]) :
    (m.to𝒲 ≫= fun h ↦ f h) = ⨁ᶠ h ∈ m.finSupp, ⟨fun h' ↦ m h ⨀ f h h', SetCoe.countable (W.supp fun h' ↦ m h ⨀ (f h) h')⟩ := by
  simp [𝒲.bind]
  have : Finite m.to𝒲.supp := by
    refine Set.Finite.ofFinset m.finSupp fun x ↦ ?_
    simp_all
  ext h
  simp
  rw [WeightedSum_finite]
  refine WeightedFinsum_bij (fun x _ ↦ x) (fun a ↦ ?_) ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := a; simp_all; exact ha
  · simp
  · simp
  · simp_all [𝒞.to𝒲]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype N] in
theorem 𝒲.η_eq_η' (x : H[F,N]) : η (𝒮:=𝒮) x = (η' x).to𝒲 := by
  rfl

@[simp]
theorem 𝒲.bind_of_𝒞 (m : 𝒞 𝒮 H[F,N]) (f : H[F,N] → 𝒞 𝒮 H[F,N]) :
    (m.to𝒲 ≫= fun h ↦ (f h).to𝒲) = (m.bind f).to𝒲 := by
  ext; simp only [bind_of_𝒞', 𝒞.to𝒲_apply, WeightedFinsum_apply_𝒲, mk_apply, 𝒞.bind, 𝒞.mk', ne_eq]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_zero_is_one_collapse (h : (𝟘 : 𝒮) = 𝟙) (a : 𝒮) : a = 𝟘 := by
  have := WeightedSemiring.mul_wOne a
  rw [← h] at this
  simp at this
  exact this.symm

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_one_is_zero_collapse (h : (𝟙 : 𝒮) = 𝟘) (a : 𝒮) : a = 𝟘 := by
  have := WeightedSemiring.mul_wOne a
  rw [h] at this
  simp at this
  exact this.symm

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_zero_is_one_elim (h : (𝟘 : 𝒮) = 𝟙) (a b : 𝒮) : a = b := by
  simp [if_zero_is_one_collapse h]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_one_is_zero_elim (h : (𝟙 : 𝒮) = 𝟘) (a b : 𝒮) : a = b := by
  simp [if_one_is_zero_collapse h]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_zero_is_one_subsingleton (h : (𝟘 : 𝒮) = 𝟙) : Subsingleton 𝒮 := by
  constructor
  simp [if_zero_is_one_collapse h]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_one_is_zero_subsingleton (h : (𝟙 : 𝒮) = 𝟘) : Subsingleton 𝒮 := by
  constructor
  simp [if_one_is_zero_collapse h]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem 𝒲.if_zero_is_one_elim (h : (𝟘 : 𝒮) = 𝟙) (a b : 𝒲 𝒮 X) :
    a = b := by ext; apply WeightedSemiring.if_zero_is_one_elim h
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem 𝒲.if_one_is_zero_elim (h : (𝟙 : 𝒮) = 𝟘) (a b : 𝒲 𝒮 X) :
    a = b := by ext; apply WeightedSemiring.if_one_is_zero_elim h

theorem 𝒲.η_bind (x : H[F,N]) (f : H[F,N] → 𝒲 𝒮 H[F,N]) :
    (η x ≫= f) = ⟨fun h ↦ η x x ⨀ f x h, SetCoe.countable _⟩ := by
  simp [𝒲.η_eq_η']
  if (𝟙 : 𝒮) = 𝟘 then apply 𝒲.if_one_is_zero_elim ‹𝟙 = 𝟘›
  else simp_all

namespace WeightedNetKAT

attribute [local simp] Predicate.sem Predicate.compute in
theorem Predicate.compute_eq_sem_n (p : Predicate[F,N]) (n : ℕ):
    p.sem (𝒮:=𝒮) = fun h ↦ (p.compute n h).to𝒲 := by
  induction p with
  | Bool b =>
    cases b <;> simp
    rfl
  | Test f t =>
    ext
    simp_all
    split
    simp; split_ifs <;> rfl
  | Dis t u iht ihu =>
    simp_all
    congr! with h
    simp [𝒞.bind]
    ext h'
    magic_simp [𝒞.to𝒲]
    simp
    congr! 2 with x
    magic_simp
    simp [WeightedAdd.wAdd]
    magic_simp
    simp
    congr
    split_ifs with h₁ h₂ h₃
    · simp_all [𝒲.η_bind]
      if h10 : (𝟙 : 𝒮) = 𝟘 then
        apply WeightedSemiring.if_one_is_zero_elim h10
      else
        have : (η' (𝒮:=𝒮) x).finSupp = {x} := by simp_all [η']
        have : (η' (𝒮:=𝒮) x).toFun x = 𝟙 := by simp [η']
        simp_all
    · absurd h₂
      -- TODO: fix when 𝒞 is `𝒞`
      exact 𝒞.ext_iff.mpr (congrFun (congrArg (·.toFun) h₁))
    · simp_all
    · convert_to (𝟘 : 𝒮) = 𝟘
      · simp [𝒲.bind]
      · rfl
  | Con t u iht ihu => simp_all only [sem, 𝒲.bind_of_𝒞, compute]
  | Not t ih =>
    simp_all; clear ih
    ext h h'
    split_ifs with h₁ h₂ h₃
    · simp_all [η', 𝒞.to𝒲]
    · absurd h₂
      exact 𝒞.ext_iff.mpr (congrFun (congrArg (·.toFun) h₁))
    · simp_all
    · rfl

omit [Fintype N] in
@[simp]
theorem WeightedFinsum_𝒞_apply [DecidableEq X] {ι : Type} [DecidableEq ι] (f : ι → 𝒞 𝒮 X) (S : Finset ι) (h : X) :
    (⨁ᶠ i ∈ S, f i) h = ⨁ᶠ i ∈ S, f i h := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih => simp_all

omit [Fintype N] in
@[simp]
theorem WeightedFinsum_𝒞_toFun_apply {ι : Type} [DecidableEq ι] (f : ι → 𝒞 𝒮 H[F,N]) (S : Finset ι) (h : H[F,N]) :
    (⨁ᶠ i ∈ S, f i).toFun h = ⨁ᶠ i ∈ S, f i h := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih => simp_all

variable [DecidableEq F] in
attribute [local simp] Policy.sem_n Policy.compute in
theorem Policy.compute_eq_sem_n (p : Policy[F,N,𝒮]) (n : ℕ) : p.sem_n n = fun h ↦ (p.compute n h).to𝒲 := by
  induction p with
  | Filter t => simp [sem_n, compute]; apply Predicate.compute_eq_sem_n
  | Mod f e => ext; simp; split; simp_all
  | Dup => ext; simp; split; simp_all
  | Seq p q ihp ihq => simp_all only [sem_n, 𝒲.bind_of_𝒞, compute]
  | Weight w p =>
    simp_all
    magic_simp
    simp
    congr
  | Add p q ihp ihq =>
    simp_all
    simp [WeightedAdd.wAdd]
  | Iter p ih =>
    simp_all
    congr with h h'
    simp
    congr with x
    suffices (p.iter x).sem_n n = (fun h ↦ (p.iter x).compute n h |>.to𝒲) by simp [this]
    induction x with
    | zero => ext; simp [Predicate.sem, Predicate.compute, η']
    | succ x ihx => simp_all only [iter, sem_n, 𝒲.bind_of_𝒞, compute]

end WeightedNetKAT

end
