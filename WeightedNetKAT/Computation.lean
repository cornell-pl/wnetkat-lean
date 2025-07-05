import WeightedNetKAT.Semantics
import WeightedNetKAT.FinsuppExt
import Mathlib.Data.Set.Finite.Basic

variable {X : Type} {𝒮 : Type}
  [Semiring 𝒮]
  [OmegaCompletePartialOrder 𝒮]
  [OrderBot 𝒮]
  [MulLeftMono 𝒮]
  [MulRightMono 𝒮]
  [CanonicallyOrderedAdd 𝒮]
  [IsPositiveOrderedAddMonoid 𝒮]
  [DecidableEq 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [DecidableEq N]

-- instance : DecidableEq (H[F,N] →₀ 𝒮) := fun m m' ↦
--   if h : m.support = m'.support ∧ m.support.filter (fun x ↦ m x ≠ m' x) = ∅ then
--     .isTrue (by
--       obtain ⟨h, h'⟩ := h
--       ext i
--       simp [Finset.filter_eq_empty_iff] at h'
--       if hi : i ∈ m.finSupp then exact h' ((𝒞.mem_finSupp_iff i).mp hi)
--       else grind [𝒞.mem_finSupp_iff])
--   else
--     .isFalse (by contrapose! h; simp_all)

-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
-- @[simp]
-- theorem 𝒞.wZero_to𝒲 : (0 : X →₀ 𝒮).to𝒲 = 0 := rfl
-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
-- @[simp]
-- theorem 𝒞.wZero_apply {x : X} : (0 : X →₀ 𝒮) x = 0 := rfl

-- open WeightedPreSemiring in
-- instance [DecidableEq X] : WeightedAdd (X →₀ 𝒮) where
--   wAdd a b := ⟨a.to𝒲 ⨁ b.to𝒲, a.finSupp ∪ b.finSupp, by
--     ext; simp [WeightedAdd.wAdd]
--     grind⟩

-- omit [DecidableEq 𝒮] in
-- @[simp]
-- theorem 𝒞.wAdd_apply [DecidableEq X] {m m' : X →₀ 𝒮} {x : X} : (m ⨁ m') x = m x ⨁ m' x := rfl

-- open WeightedPreSemiring in
-- instance [DecidableEq X] : WeightedMul (X →₀ 𝒮) where
--   wMul a b := ⟨a.to𝒲 ⨀ b.to𝒲, (a.finSupp ∩ b.finSupp).filter fun x ↦ a.to𝒲 x ⨀ b.to𝒲 x ≠ 0, by
--     ext; simp [WeightedMul.wMul]
--     contrapose!
--     simp
--     intro h
--     apply Decidable.not_or_of_imp at h
--     rcases h with (h | h) <;> simp_all⟩

-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp]
-- theorem 𝒞.wMul_apply [DecidableEq X] {m m' : X →₀ 𝒮} {x : X} : (m ⨀ m') x = m x ⨀ m' x := rfl

-- open WeightedPreSemiring in
-- instance [DecidableEq X] : WeightedPreSemiring (X →₀ 𝒮) where
--   wNsmul n m := if h0 : n = 0 then 0 else ⟨wNsmul n m.to𝒲, m.finSupp.filter (fun x ↦ wNsmul n (m.to𝒲 x) ≠ 0), by
--     ext x; simp_all [wNsmul, instPi]
--     constructor
--     · contrapose!
--       intro h h0'
--       clear h0
--       induction n with
--       | zero => simp only [wNsmul_wZero]
--       | succ => simp_all only [ne_eq, 𝒲.wNsmul, WeightedAdd.wAdd, 𝒞.to𝒲_apply, 𝒲.mk_apply,
--         wAdd_eq_zero_iff, and_false]
--     · contrapose!
--       intro h
--       apply Decidable.not_or_of_imp at h
--       clear h0
--       rcases h with h | h
--       · induction n with
--         | zero => simp only [𝒲.wNsmul, 𝒲.instWeightedZero_apply]
--         | succ n ih => simp_all only [ne_eq, Decidable.not_not, 𝒲.wNsmul, WeightedAdd.wAdd,
--           𝒞.to𝒲_apply, 𝒲.mk_apply, add_wZero]
--       · induction n with
--         | zero => simp only [𝒲.wNsmul, 𝒲.instWeightedZero_apply]
--         | succ n ih =>
--           simp_all only [wNsmul_succ, wAdd_eq_zero_iff, 𝒲.wNsmul, WeightedAdd.wAdd, 𝒞.to𝒲_apply,
--             𝒲.mk_apply, add_wZero]
--           apply ih
--           clear ih h
--           induction n with
--           | zero => simp [wNsmul_wZero]
--           | succ => simp_all [wNsmul_wZero, wNsmul_succ]
--     ⟩
--   wAdd_assoc _ _ _ := by ext; apply wAdd_assoc
--   wZero_add _ := by ext; apply wZero_add
--   add_wZero _ := by ext; apply add_wZero
--   wNsmul_wZero _ := by simp
--   wNsmul_succ _ _ := by
--     ext x
--     simp; split_ifs
--     · simp_all [wNsmul_wZero, wNsmul_succ]
--     · simp_all [wNsmul_succ, WeightedAdd.wAdd]
--   wAdd_comm a b := by ext; apply wAdd_comm
--   left_distrib a b c := by ext; apply WeightedPreSemiring.left_distrib
--   right_distrib a b c := by ext; apply WeightedPreSemiring.right_distrib
--   wZero_mul := by intro; ext; simp only [𝒞.wMul_apply, 𝒞.wZero_apply, wZero_mul]
--   mul_wZero := by intro; ext; simp only [𝒞.wMul_apply, 𝒞.wZero_apply, mul_wZero]
--   mul_assoc a b c := by ext; apply WeightedPreSemiring.mul_assoc

-- instance [DecidableEq X] : WeightedPartialOrder (X →₀ 𝒮) := sorry
-- instance [DecidableEq X] : WeightedMonotonePreSemiring (X →₀ 𝒮) := sorry

-- @[simp]
-- def 𝒞.mk' (f : X → 𝒮) (finSupp : Finset X) (h : ∀ x, x ∈ W.supp f ↔ x ∈ finSupp) : X →₀ 𝒮 :=
--   let h : finSupp = W.supp f := by ext; simp_all
--   ⟨⟨f, by rw [← h]; exact Finite.to_countable⟩, finSupp, h⟩

-- instance 𝒞.instwProdWeightedOne {𝒮 X : Type} [Fintype X] [WeightedSemiring 𝒮] [DecidableEq 𝒮] :
--     WeightedOne (X →₀ 𝒮) where
--   wOne :=
--     if h : ¬(1 : 𝒮) = 0 then 𝒞.mk' (fun _ ↦ 1) Fintype.elems (by simp [h, Fintype.complete])
--     else 0

-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp]
-- theorem 𝒞.wOne_apply {X : Type} [Fintype X] (x) : (1 : X →₀ 𝒮) x = 1 := by
--   simp [WeightedOne.wOne]
--   split_ifs <;> grind [𝒞.wZero_apply, 𝒞.mk_apply, 𝒲.mk_apply]

-- def 𝒞.bind {X Y : Type} [DecidableEq X] [DecidableEq Y] (m : X →₀ 𝒮) (f : X → 𝒞 𝒮 Y) :
--     𝒞 𝒮 Y :=
--   𝒞.mk' (fun y ↦ ⨁ᶠ x ∈ m.finSupp, m x ⨀ f x y)
--     (m.finSupp.biUnion (fun x ↦ (f x).finSupp.filter (fun y ↦ m x ⨀ f x y ≠ 0)))
--     (by
--       intro y
--       simp
--       congr! 2 with x
--       simp
--       contrapose!
--       simp
--       intro h₁ h₂
--       simp_all)

-- instance {X : Type} : WeightedHMul 𝒮 (X →₀ 𝒮) (X →₀ 𝒮) where
--   wHMul w m := 𝒞.mk' (fun h' ↦ w ⨀ m h')
--     (m.finSupp.filter (fun h' ↦ w ⨀ m h' ≠ 0))
--     (by
--       intro h'
--       simp_all only [W.supp_mem_iff, ne_eq, Finset.mem_filter, 𝒞.mem_finSupp_iff, iff_and_self]
--       contrapose!
--       simp_all)
-- instance {X : Type} : WeightedHMul (X →₀ 𝒮) 𝒮 (X →₀ 𝒮) where
--   wHMul m w := 𝒞.mk' (fun h' ↦ m h' ⨀ w)
--     (m.finSupp.filter (fun h' ↦ m h' ⨀ w ≠ 0))
--     (by
--       intro h'
--       simp_all only [W.supp_mem_iff, ne_eq, Finset.mem_filter, 𝒞.mem_finSupp_iff, iff_and_self]
--       contrapose!
--       simp_all)

-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.sHMul_apply {X : Type} (m : X →₀ 𝒮) (w : 𝒮) (x : X) : (w ⨀ m) x = w ⨀ m x := rfl
-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.one_sHMul {X : Type} (m : X →₀ 𝒮) : (1 : 𝒮) ⨀ m = m := by ext; simp
-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.zero_sHMul {X : Type} (m : X →₀ 𝒮) : (0 : 𝒮) ⨀ m = 0 := by ext; simp

-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.sHMul'_apply {X : Type} (m : X →₀ 𝒮) (w : 𝒮) (x : X) : (m ⨀ w) x = m x ⨀ w := rfl
-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.sHMul_one {X : Type} (m : X →₀ 𝒮) : m ⨀ (1 : 𝒮) = m := by ext; simp
-- omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
-- @[simp] theorem 𝒞.sHMul_zero {X : Type} (m : X →₀ 𝒮) : m ⨀ (0 : 𝒮) = 0 := by ext; simp

namespace WeightedNetKAT

open Finsupp (η')

def Predicate.compute (p : Predicate[F,N]) (n : ℕ) : H[F,N] → H[F,N] →₀ 𝒮 := match p with
  | wnk_pred {false} => fun _ ↦ 0
  | wnk_pred {true} => η'
  | wnk_pred {~f = ~n} => fun (π, h) ↦ if π f = n then η' (π, h) else 0
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.compute n h |>.bind (fun h ↦ η' h + ((if t.compute n h = 0 then η' h else 0).bind (u.compute n))))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ (t.compute n h).bind (u.compute n)
  | wnk_pred {¬~t} => fun h ↦ if t.compute n h = 0 then η' h else 0
def Policy.compute (p : Policy[F,N,𝒮]) (n : ℕ) : H[F,N] → H[F,N] →₀ 𝒮 := match p with
  | .Filter t => t.compute n
  | wnk_policy {~f ← ~n} => fun (π, h) ↦ η' (π[f ↦ n], h)
  | wnk_policy {dup} => fun (π, h) ↦ η' (π, π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.compute n h).bind (q.compute n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w * p.compute n h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.compute n h + q.compute n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ∑ i ∈ Finset.range n, (p ^ i).compute n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

end WeightedNetKAT

section

-- variable {X : Type} {𝒮 : Type} [WeightedPartialOrder 𝒮] [WeightedSemiring 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮]
-- variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
-- variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

def Finset.toList' {α : Type} [Encodable α] [DecidableEq α] (s : Finset α) : List α := s.val.rep

instance {F : Type} [i : Fintype F] [e : Encodable F] [Repr F] [Repr N] : Repr Pk[F,N] where
  reprPrec x _ := s!"\{{List.range i.card |>.filterMap e.decode |>.map (fun k ↦ s!"{reprStr k}↦{reprStr (x k)}") |> ",".intercalate}}"

def Finsupp.pretty [DecidableEq X] (m : X →₀ 𝒮) : Finset (X × 𝒮) := m.support.image (fun s ↦ (s, m s))
unsafe instance 𝒞.repr [DecidableEq X] [Repr X] [Repr 𝒮] : Repr (X →₀ 𝒮) where
  reprPrec m n := reprPrec m.pretty n

end

section

-- TODO: this is the proof of approx eq sem

-- variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮]
-- variable {F : Type} [Fintype F]
-- variable {N : Type} [Fintype N] [DecidableEq N]

-- omit [DecidableEq 𝒮] in
-- @[simp]
-- theorem 𝒲.bind_of_𝒞' (m : H[F,N] →₀ 𝒮) (f : H[F,N] → 𝒲 𝒮 H[F,N]) :
--     (m.to𝒲 ≫= fun h ↦ f h) = ⨁ᶠ h ∈ m.finSupp, ⟨fun h' ↦ m h ⨀ f h h', SetCoe.countable (W.supp fun h' ↦ m h ⨀ (f h) h')⟩ := by
--   simp [𝒲.bind]
--   have : Finite m.to𝒲.supp := by
--     refine Set.Finite.ofFinset m.finSupp fun x ↦ ?_
--     simp_all
--   ext h
--   simp
--   rw [WeightedSum_finite]
--   refine WeightedFinsum_bij (fun x _ ↦ x) (fun a ↦ ?_) ?_ ?_ ?_
--   · obtain ⟨a, ha⟩ := a; simp_all; exact ha
--   · simp
--   · simp
--   · simp_all [𝒞.to𝒲]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [Fintype N] in
-- theorem 𝒲.η_eq_η' (x : H[F,N]) : η (𝒮:=𝒮) x = (η' x).to𝒲 := by
--   rfl

-- @[simp]
-- theorem 𝒲.bind_of_𝒞 (m : H[F,N] →₀ 𝒮) (f : H[F,N] → H[F,N] →₀ 𝒮) :
--     (m.to𝒲 ≫= fun h ↦ (f h).to𝒲) = (m.bind f).to𝒲 := by
--   ext; simp only [bind_of_𝒞', 𝒞.to𝒲_apply, WeightedFinsum_apply_𝒲, mk_apply, 𝒞.bind, 𝒞.mk', ne_eq]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_zero_is_one_collapse (h : (0 : 𝒮) = 1) (a : 𝒮) : a = 0 := by
--   have := WeightedSemiring.mul_wOne a
--   rw [← h] at this
--   simp at this
--   exact this.symm

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_one_is_zero_collapse (h : (1 : 𝒮) = 0) (a : 𝒮) : a = 0 := by
--   have := WeightedSemiring.mul_wOne a
--   rw [h] at this
--   simp at this
--   exact this.symm

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_zero_is_one_elim (h : (0 : 𝒮) = 1) (a b : 𝒮) : a = b := by
--   simp [if_zero_is_one_collapse h]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_one_is_zero_elim (h : (1 : 𝒮) = 0) (a b : 𝒮) : a = b := by
--   simp [if_one_is_zero_collapse h]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_zero_is_one_subsingleton (h : (0 : 𝒮) = 1) : Subsingleton 𝒮 := by
--   constructor
--   simp [if_zero_is_one_collapse h]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem WeightedSemiring.if_one_is_zero_subsingleton (h : (1 : 𝒮) = 0) : Subsingleton 𝒮 := by
--   constructor
--   simp [if_one_is_zero_collapse h]

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem 𝒲.if_zero_is_one_elim (h : (0 : 𝒮) = 1) (a b : 𝒲 𝒮 X) :
--     a = b := by ext; apply WeightedSemiring.if_zero_is_one_elim h
-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
-- theorem 𝒲.if_one_is_zero_elim (h : (1 : 𝒮) = 0) (a b : 𝒲 𝒮 X) :
--     a = b := by ext; apply WeightedSemiring.if_one_is_zero_elim h

-- theorem 𝒲.η_bind (x : H[F,N]) (f : H[F,N] → 𝒲 𝒮 H[F,N]) :
--     (η x ≫= f) = ⟨fun h ↦ η x x ⨀ f x h, SetCoe.countable _⟩ := by
--   simp [𝒲.η_eq_η']
--   if (1 : 𝒮) = 0 then apply 𝒲.if_one_is_zero_elim ‹1 = 0›
--   else simp_all

-- namespace WeightedNetKAT

-- attribute [local simp] Predicate.sem Predicate.compute in
-- theorem Predicate.compute_eq_sem_n (p : Predicate[F,N]) (n : ℕ):
--     p.sem (𝒮:=𝒮) = fun h ↦ (p.compute n h) := by
--   induction p with
--   | Bool b =>
--     cases b <;> simp
--     rfl
--   | Test f t =>
--     ext
--     simp_all
--     split
--     simp; split_ifs <;> rfl
--   | Dis t u iht ihu =>
--     simp_all
--     congr! with h
--     simp [𝒞.bind]
--     ext h'
--     magic_simp [𝒞.to𝒲]
--     simp
--     congr! 2 with x
--     magic_simp
--     simp [WeightedAdd.wAdd]
--     magic_simp
--     simp
--     congr
--     split_ifs with h₁ h₂ h₃
--     · simp_all [𝒲.η_bind]
--       if h10 : (1 : 𝒮) = 0 then
--         apply WeightedSemiring.if_one_is_zero_elim h10
--       else
--         have : (η' (𝒮:=𝒮) x).finSupp = {x} := by simp_all [η']
--         have : (η' (𝒮:=𝒮) x).toFun x = 1 := by simp [η']
--         simp_all
--     · absurd h₂
--       -- TODO: fix when 𝒞 is `𝒞`
--       exact 𝒞.ext_iff.mpr (congrFun (congrArg (·.toFun) h₁))
--     · simp_all
--     · convert_to (0 : 𝒮) = 0
--       · simp [𝒲.bind]
--       · rfl
--   | Con t u iht ihu => simp_all only [sem, 𝒲.bind_of_𝒞, compute]
--   | Not t ih =>
--     simp_all; clear ih
--     ext h h'
--     split_ifs with h₁ h₂ h₃
--     · simp_all [η', 𝒞.to𝒲]
--     · absurd h₂
--       exact 𝒞.ext_iff.mpr (congrFun (congrArg (·.toFun) h₁))
--     · simp_all
--     · rfl

-- omit [Fintype N] in
-- @[simp]
-- theorem WeightedFinsum_𝒞_apply [DecidableEq X] {ι : Type} [DecidableEq ι] (f : ι → X →₀ 𝒮) (S : Finset ι) (h : X) :
--     (⨁ᶠ i ∈ S, f i) h = ⨁ᶠ i ∈ S, f i h := by
--   induction S using Finset.induction with
--   | empty => simp
--   | insert i S hi ih => simp_all

-- omit [Fintype N] in
-- @[simp]
-- theorem WeightedFinsum_𝒞_toFun_apply {ι : Type} [DecidableEq ι] (f : ι → H[F,N] →₀ 𝒮) (S : Finset ι) (h : H[F,N]) :
--     (⨁ᶠ i ∈ S, f i).toFun h = ⨁ᶠ i ∈ S, f i h := by
--   induction S using Finset.induction with
--   | empty => simp
--   | insert i S hi ih => simp_all

-- variable [DecidableEq F] in
-- attribute [local simp] Policy.sem_n Policy.compute in
-- theorem Policy.compute_eq_sem_n (p : Policy[F,N,𝒮]) (n : ℕ) : p.sem_n n = fun h ↦ (p.compute n h).to𝒲 := by
--   induction p with
--   | Filter t => simp [sem_n, compute]; apply Predicate.compute_eq_sem_n
--   | Mod f e => ext; simp; split; simp_all
--   | Dup => ext; simp; split; simp_all
--   | Seq p q ihp ihq => simp_all only [sem_n, 𝒲.bind_of_𝒞, compute]
--   | Weight w p =>
--     simp_all
--     magic_simp
--     simp
--     congr
--   | Add p q ihp ihq =>
--     simp_all
--     simp [WeightedAdd.wAdd]
--   | Iter p ih =>
--     simp_all
--     congr with h h'
--     simp
--     congr with x
--     suffices (p.iter x).sem_n n = (fun h ↦ (p.iter x).compute n h |>.to𝒲) by simp [this]
--     induction x with
--     | zero => ext; simp [Predicate.sem, Predicate.compute, η']
--     | succ x ihx => simp_all only [iter, sem_n, 𝒲.bind_of_𝒞, compute]

-- end WeightedNetKAT

end
