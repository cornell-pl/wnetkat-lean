import WeightedNetKAT.Semantics
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Order

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮]
variable {F : Type} [Fintype F] [DecidableEq F]

structure 𝒞 (𝒮 : Type) [WeightedSemiring 𝒮] (X : Type) where
  toFun : W X 𝒮
  supp : Finset X
  supp_is_supp : toFun.supp = supp

instance : FunLike (𝒞 𝒮 X) X 𝒮 where
  coe m := m.toFun
  coe_injective' := by
    intro a b h
    simp_all
    rcases a with ⟨a, asupp, ah⟩
    rcases b with ⟨b, bsupp, bh⟩
    apply Set.ext_iff.mp at ah
    apply Set.ext_iff.mp at bh
    simp_all
    subst_eqs
    simp_all

omit [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
@[simp]
theorem 𝒞.mem_supp_iff {m : 𝒞 𝒮 X} (x : X) : x ∈ m.supp ↔ m x ≠ 𝟘 := by
  have := m.supp_is_supp.symm
  apply Set.ext_iff.mp at this
  simp_all; clear this
  rfl

instance {m : 𝒞 𝒮 X} : Countable m.supp := Finite.to_countable
noncomputable instance {m : 𝒞 𝒮 X} : Encodable m.supp := Encodable.ofCountable _

omit [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
@[ext]
theorem 𝒞.ext (C₁ C₂ : 𝒞 𝒮 X)
    (h : ∀ i, C₁ i = C₂ i) : C₁ = C₂ := by
  cases C₁; cases C₂; simp_all
  simp_all [DFunLike.coe]
  constructor
  · ext x; exact h x
  · ext x
    rename_i h₂ _ _ h₁
    symm at h₁ h₂
    apply Set.ext_iff.mp at h₁
    apply Set.ext_iff.mp at h₂
    simp_all

instance : DecidableEq (𝒞 𝒮 H[F]) := fun m m' ↦
  if h : m.supp = m'.supp ∧ m.supp.filter (fun x ↦ m x ≠ m' x) = ∅ then
    .isTrue (by
      obtain ⟨h, h'⟩ := h
      ext i
      simp [Finset.filter_eq_empty_iff] at h'
      if hi : i ∈ m.supp then
        simp [𝒞.supp] at hi
        exact h' hi
      else
        simp_all
        replace : ∀ x, x ∈ m.supp ↔ x ∈ m'.supp := by simp_all
        have := this i |>.not
        simp at this
        exact this.mpr hi)
  else
    .isFalse (by contrapose! h; simp_all)

open WeightedPreSemiring in
instance : WeightedPreSemiring (𝒞 𝒮 H[F]) where
  wAdd a b := ⟨a.toFun ⨁ b.toFun, a.supp ∪ b.supp, by
    ext; simp_all [WeightedAdd.instPi, DFunLike.coe]
    constructor
    · intro h
      exact Decidable.not_or_of_imp h
    · rintro (h | h) <;> simp [h]⟩
  wMul a b := ⟨a.toFun ⨀ b.toFun, (a.supp ∩ b.supp).filter fun x ↦ a.toFun x ⨀ b.toFun x ≠ 𝟘 , by
    ext; simp_all [WeightedMul.instPi, DFunLike.coe]
    contrapose!
    simp
    intro h
    apply Decidable.not_or_of_imp at h
    rcases h with (h | h) <;> simp_all⟩
  wZero := ⟨𝟘, ∅, by ext; simp; rfl⟩
  wNsmul n m := if h0 : n = 0 then ⟨𝟘, ∅, by ext; simp; rfl⟩ else ⟨wNsmul n m.toFun, m.supp.filter (fun x ↦ wNsmul n (m x) ≠ 𝟘), by
    ext x; simp_all [instPi]
    constructor
    · contrapose!
      intro h
      apply Decidable.not_or_of_imp at h
      rcases h with (h | h)
      · simp_all
        have : (m.toFun x) = 𝟘 := h
        simp [this]
        clear h0
        induction n with
        | zero => simp [wNsmul_wZero]
        | succ n ih => simp [wNsmul_wZero, wNsmul_succ, ih]
      · exact h
    · contrapose!
      intro h _
      exact h
    ⟩
  wAdd_assoc _ _ _ := by ext; apply wAdd_assoc
  wZero_add _ := by ext; apply wZero_add
  add_wZero _ := by ext; apply add_wZero
  wNsmul_wZero _ := by simp
  wNsmul_succ _ _ := by
    ext x
    simp; split_ifs
    · simp_all [wNsmul_wZero, wNsmul_succ, DFunLike.coe]
    · simp_all [wNsmul_succ, DFunLike.coe]
  wAdd_comm a b := by ext; apply wAdd_comm
  left_distrib a b c := by ext; apply WeightedPreSemiring.left_distrib
  right_distrib a b c := by ext; apply WeightedPreSemiring.right_distrib
  wZero_mul := by simp
  mul_wZero := by simp
  mul_assoc a b c := by ext; apply WeightedPreSemiring.mul_assoc

def 𝒞.bind {X Y : Type} [DecidableEq X] [DecidableEq Y] (m : 𝒞 𝒮 X) (f : X → 𝒞 𝒮 Y) :
    𝒞 𝒮 Y :=
  ⟨fun y ↦ ⨁ᶠ x ∈ m.supp, m x ⨀ f x y, m.supp.biUnion (fun x ↦ (f x).supp.filter (fun y ↦ m x ⨀ f x y ≠ 𝟘)), by
    ext y
    simp
    congr! 2 with x
    simp
    contrapose!
    simp
    intro h₁ h₂
    simp_all⟩

def η' {X : Type} [DecidableEq X] (x : X) : 𝒞 𝒮 X := ⟨
  fun y ↦ if x = y then 𝟙 else 𝟘,
  if (𝟙 : 𝒮) = 𝟘 then ∅ else {x},
  by ext; split_ifs <;> simp_all [eq_comm]⟩

notation "η'[" 𝒮 "]" => η' (𝒮:=𝒮)

def Predicate.compute (p : Predicate[F]) (n : ℕ) : H[F] → 𝒞 𝒮 H[F] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η'
  | wnk_pred {~f = ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => if π f = n then η' (π::h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- NOTE: this is the actual semantics `⟦if t then skip else u⟧`, but we use the unfolded due to
    -- termination checking
    fun h ↦ (t.compute n h |>.bind (fun h ↦ η' h ⨁ ((if t.compute n h = 𝟘 then η' h else 𝟘).bind (u.compute n))))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦ (t.compute n h).bind (u.compute n)
  | wnk_pred {¬~t} => fun h ↦ if t.compute n h = 𝟘 then η' h else 𝟘
def Policy.compute (p : Policy[F,𝒮]) (n : ℕ) : H[F] → 𝒞 𝒮 H[F] := match p with
  | .Filter t => t.compute n
  | wnk_policy {~f ← ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η' (π[f ↦ n]::h)
  | wnk_policy {dup} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η' (π::π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.compute n h).bind (q.compute n)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ ⟨fun h' ↦ w ⨀ p.compute n h h', (p.compute n h).supp.filter (fun h' ↦ w ⨀ p.compute n h h' ≠ 𝟘), by
      ext h'
      simp_all only [W.supp_mem_iff, ne_eq, Finset.coe_filter, 𝒞.mem_supp_iff, Set.mem_setOf_eq,
        iff_and_self]
      contrapose!
      simp_all⟩
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.compute n h ⨁ q.compute n h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁ᶠ i ∈ Finset.range n, (p ^ i).compute n h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

def 𝒞.to𝒲 (m : 𝒞 𝒮 H[F]) : 𝒲 𝒮 H[F] := ⟨m, SetCoe.countable (W.supp ⇑m)⟩

omit [DecidableEq 𝒮] [DecidableEq F] in
@[simp]
theorem 𝒲.bind_of_𝒞' (m : 𝒞 𝒮 H[F]) (f : H[F] → 𝒲 𝒮 H[F]) :
    (m.to𝒲 ≫= fun h ↦ f h) = ⨁ᶠ h ∈ m.supp, ⟨fun h' ↦ m h ⨀ f h h', SetCoe.countable (W.supp fun h' ↦ m h ⨀ (f h) h')⟩ := by
  simp [𝒲.bind]
  have : Finite m.to𝒲.supp := by
    refine Set.Finite.ofFinset m.supp fun x ↦ ?_
    simp_all
    rfl
  ext h
  simp
  rw [WeightedSum_finite]
  refine WeightedFinsum_bij (fun x _ ↦ x) (fun a ↦ ?_) ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := a; simp_all; exact ha
  · simp
  · simp; intro _ h; exact h
  · simp_all [𝒞.to𝒲]
    intro a ha
    magic_simp

omit [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq F] in
theorem 𝒲.η_eq_η' (x : H[F]) : η (𝒮:=𝒮) x = (η' x).to𝒲 := by
  ext h
  simp [η', 𝒞.to𝒲]
  magic_simp

omit [DecidableEq F] in
theorem 𝒲.η_bind (x : H[F]) (f : H[F] → 𝒲 𝒮 H[F]) :
    (η x ≫= f) = ⟨fun h ↦ η x x ⨀ f x h, SetCoe.countable _⟩ := by
  simp [𝒲.η_eq_η']
  if (𝟙 : 𝒮) = 𝟘 then
    have : (η' (𝒮:=𝒮) x).supp = ∅ := by
      ext; simp [η']; split_ifs; simp
    simp_all
    ext x'
    simp [𝒞.to𝒲]
    magic_simp
    have : η' (𝒮:=𝒮) x = 𝟘 := by simp_all [η']; rfl
    simp_all
    symm
    apply WeightedPreSemiring.wZero_mul
  else
    have : (η' (𝒮:=𝒮) x).supp = {x} := by
      ext; simp [η']; simp_all
    simp_all
    ext y
    simp
    congr! 1

omit [DecidableEq F] in
@[simp]
theorem 𝒲.bind_of_𝒞 (m : 𝒞 𝒮 H[F]) (f : H[F] → 𝒞 𝒮 H[F]) :
    (m.to𝒲 ≫= fun h ↦ (f h).to𝒲) = (m.bind f).to𝒲 := by
  simp only [bind_of_𝒞']
  simp only [𝒞.to𝒲, 𝒞.bind, ne_eq]
  magic_simp
  ext
  simp only [apply_subtype, WeightedFinsum_apply']
  congr

omit [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_zero_is_one_collapse (h : (𝟘 : 𝒮) = 𝟙) (a : 𝒮) : a = 𝟘 := by
  have := WeightedSemiring.mul_wOne a
  rw [← h] at this
  simp at this
  exact this.symm

omit [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
theorem WeightedSemiring.if_one_is_zero_collapse (h : (𝟙 : 𝒮) = 𝟘) (a : 𝒮) : a = 𝟘 := by
  have := WeightedSemiring.mul_wOne a
  rw [h] at this
  simp at this
  exact this.symm

omit [DecidableEq F] in
attribute [local simp] Predicate.sem Predicate.compute in
theorem Predicate.compute_eq_sem_n (p : Predicate[F]) (n : ℕ):
    p.sem (𝒮:=𝒮) = fun h ↦ (p.compute n h).to𝒲 := by
  induction p with
  | Bool b =>
    cases b
    · simp; rfl
    · simp; rfl
  | Test f t =>
    ext
    simp_all
    split
    · simp; rfl
    · simp; split_ifs
      · simp; rfl
      · rfl
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
      if (𝟙 : 𝒮) = 𝟘 then
        simp_all
        have : (η' (𝒮:=𝒮) x).supp = ∅ := by simpa [η']
        simp_all
        apply WeightedSemiring.if_one_is_zero_collapse
        assumption
      else
        have : (η' (𝒮:=𝒮) x).supp = {x} := by simp_all [η']
        have : (η' (𝒮:=𝒮) x).toFun x = 𝟙 := by simp [η']
        simp_all
        congr
    · absurd h₂
      exact 𝒞.ext_iff.mpr (congrFun (congrArg Subtype.val h₁))
    · simp_all
      contrapose! h₁
      rfl
    · convert_to (𝟘 : 𝒮) = 𝟘
      · simp [𝒲.bind]
        magic_simp
        simp
      · rfl
  | Con t u iht ihu => simp_all only [sem, 𝒲.bind_of_𝒞, compute]
  | Not t ih =>
    simp_all; clear ih
    ext h h'
    simp
    split_ifs with h₁ h₂ h₃
    · simp_all [η', 𝒞.to𝒲]
      magic_simp
    · absurd h₂
      exact 𝒞.ext_iff.mpr (congrFun (congrArg Subtype.val h₁))
    · simp_all
      absurd h₁
      rfl
    · rfl

omit [DecidableEq F] in
@[simp]
theorem WeightedFinsum_𝒞_apply {ι : Type} [DecidableEq ι] (f : ι → 𝒞 𝒮 H[F]) (S : Finset ι) (h : H[F]) :
    (⨁ᶠ i ∈ S, f i) h = ⨁ᶠ i ∈ S, f i h := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert i S hi ih =>
    simp_all
    simp [WeightedAdd.wAdd]
    magic_simp
    congr

omit [DecidableEq F] in
@[simp]
theorem WeightedFinsum_𝒞_toFun_apply {ι : Type} [DecidableEq ι] (f : ι → 𝒞 𝒮 H[F]) (S : Finset ι) (h : H[F]) :
    (⨁ᶠ i ∈ S, f i).toFun h = ⨁ᶠ i ∈ S, f i h := by
  induction S using Finset.induction with
  | empty => simp; rfl
  | insert i S hi ih =>
    simp_all
    simp [WeightedAdd.wAdd]
    magic_simp
    congr

attribute [local simp] Policy.sem_n Policy.compute in
theorem Policy.compute_eq_sem_n (p : Policy[F,𝒮]) (n : ℕ) : p.sem_n n = fun h ↦ (p.compute n h).to𝒲 := by
  induction p with
  | Filter t => simp [sem_n, compute]; apply Predicate.compute_eq_sem_n
  | Mod f e => ext; simp; split <;> simp_all <;> rfl
  | Dup => ext; simp; split <;> simp_all <;> rfl
  | Seq p q ihp ihq => simp_all only [sem_n, 𝒲.bind_of_𝒞, compute]
  | Weight w p =>
    simp_all
    magic_simp
    simp
    congr
  | Add p q ihp ihq =>
    simp_all
    simp [WeightedAdd.wAdd]
    magic_simp
    simp_all
    congr
  | Iter p ih =>
    simp_all
    simp [𝒞.to𝒲]
    magic_simp
    congr with h h'
    simp
    congr with x
    suffices (p.iter x).sem_n n = (fun h ↦ (p.iter x).compute n h |>.to𝒲) by simp [this]; rfl
    induction x with
    | zero =>
      ext
      simp [Predicate.sem, Predicate.compute, η']
      magic_simp [𝒞.to𝒲]
    | succ x ihx =>
      simp_all only [iter, sem_n, 𝒲.bind_of_𝒞, compute]
