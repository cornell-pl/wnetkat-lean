import WeightedNetKAT.Computation
import WeightedNetKAT.Star
import Mathlib.Algebra.Order.Kleene

@[grind]
structure LexicalSemiring (α β : Type) where
  a : α
  b : β

variable {α β : Type}

class LinearIdemSemiring (α : Type) extends IdemSemiring α, LinearOrder α

namespace LexicalSemiring

variable [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] [NoZeroDivisors α]

instance : PartialOrder (LexicalSemiring α β) where
  le := fun ⟨s, r⟩ ⟨s', r'⟩ ↦ s < s' ∨ (s = s' ∧ r ≤ r')
  le_refl := by simp
  le_trans := by grind [lt_iff_le_not_ge, le_trans]
  le_antisymm := by grind [lt_iff_le_not_ge, le_antisymm]

def add : LexicalSemiring α β → LexicalSemiring α β → LexicalSemiring α β := fun ⟨s, r⟩ ⟨s', r'⟩ ↦
  if h₁ : s = s' then ⟨s, r + r'⟩ else
  if h₂ : s ⊔ s' = s ∧ s ≠ s' then ⟨s, r⟩ else
  if h₃ : s ⊔ s' = s' ∧ s' ≠ s then ⟨s', r'⟩ else
  False.elim (by simp_all; contrapose! h₁; rw [eq_comm] at h₃; apply h₃; exact h₂.le)

instance instAdd : Add (LexicalSemiring α β) := ⟨add⟩

@[grind, simp] theorem add_simp {a b : LexicalSemiring α β} : a + b = add a b := by rfl

def mul : LexicalSemiring α β → LexicalSemiring α β → LexicalSemiring α β := fun ⟨s, r⟩ ⟨s', r'⟩ ↦
    if s = s' ∧ s' = 0 then ⟨0, 0⟩ else
    if s = 0 ∧ s' ≠ 0 then ⟨0, r⟩ else
    if s' = 0 ∧ s ≠ 0 then ⟨0, r'⟩ else
    ⟨s * s', r * r'⟩

instance instMul : Mul (LexicalSemiring α β) := ⟨mul⟩

@[grind, simp] theorem mul_simp {a b : LexicalSemiring α β} : a * b = mul a b := by rfl

instance : Zero (LexicalSemiring α β) := ⟨⟨0, 0⟩⟩
instance : One (LexicalSemiring α β) := ⟨⟨1, 1⟩⟩

omit [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] in
@[simp]
theorem ite_a {l r : LexicalSemiring α β} {p : Prop} [Decidable p] :
    (if p then l else r).a = if p then l.a else r.a := by grind
omit [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] in
@[simp]
theorem ite_b {l r : LexicalSemiring α β} {p : Prop} [Decidable p] :
    (if p then l else r).b = if p then l.b else r.b := by grind
omit [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] in
@[simp]
theorem dite_a {l r : LexicalSemiring α β} {p : Prop} [Decidable p] :
    (if _ : p then l else r).a = if p then l.a else r.a := by grind
omit [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] in
@[simp]
theorem dite_b {l r : LexicalSemiring α β} {p : Prop} [Decidable p] :
    (if _ : p then l else r).b = if p then l.b else r.b := by grind

omit [LinearIdemSemiring α] [LinearIdemSemiring β] [DecidableEq α] in
theorem eq_iff {l r : LexicalSemiring α β} : l = r ↔ l.a = r.a ∧ l.b = r.b := by grind

theorem no_nonzero_divisors {s₁ s₂ : α} : s₁ * s₂ = 0 ↔ s₁ = 0 ∨ s₂ = 0 := by
  exact mul_eq_zero

instance : LinearIdemSemiring Unit where
  bot_le := fun a ↦ trivial
instance : NoZeroDivisors Unit where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    simp

example [Unique α] (hβ : (1 : β) ≠ 0) : (1 : LexicalSemiring α β) * 1 ≠ 1 := by
  simp_all [mul, eq_iff, Subsingleton.eq_zero]
  unfold b
  simp [OfNat.ofNat, One.one]
  exact (hβ ·.symm)

instance : Semiring (LexicalSemiring α β) where
  add_assoc := by
    intro ⟨as, ar⟩ ⟨bs, br⟩ ⟨cs, cr⟩
    simp only [add_simp]
    grind [add_assoc, le_antisymm, le_trans, add, sup_eq_left, sup_eq_right]

    -- intro ⟨as, ar⟩ ⟨bs, br⟩ ⟨cs, cr⟩
    -- simp [HAdd.hAdd, Add.add]
    -- simp [add]
    -- if as_bs : as = bs then
    --   if as = cs then
    --     grind [add_assoc]
    --   else
    --     grind
    -- else
    --   have bs_as : ¬bs = as := by grind
    --   simp [as_bs, bs_as]
    --   if as_cs : as = cs then
    --     subst_eqs
    --     simp [as_bs, bs_as]
    --     if as_bs' : as ≤ bs then
    --       have bs_as' : ¬bs ≤ as := by rw [le_iff_lt_or_eq] at as_bs'; simp_all
    --       simp [as_bs', bs_as']
    --       grind
    --     else
    --       grind
    --   else
    --     if bs_cs : bs = cs then
    --       subst_eqs
    --       grind
    --     else
    --       have cs_bs : ¬cs = bs := by grind
    --       have cs_as : ¬cs = as := by grind
    --       simp [bs_cs, cs_bs]
    --       if as_bs' : as ≤ bs then
    --         have bs_as' : ¬bs ≤ as := by rw [le_iff_lt_or_eq] at as_bs'; simp_all
    --         simp [as_bs', bs_as', bs_cs]
    --         if bs_cs' : bs ≤ cs then
    --           have cs_bs' : ¬cs ≤ bs := by rw [le_iff_lt_or_eq] at bs_cs'; simp_all
    --           simp [bs_cs', cs_bs', cs_bs, as_cs, cs_as]
    --           split_ifs
    --           · simp [cs_as]
    --             have := as_bs'.trans bs_cs'
    --             grind [le_antisymm]
    --           · simp
    --           · grind
    --         else
    --           simp [bs_cs']
    --           if bs_cs' : bs ≤ cs then
    --             have cs_bs' : ¬cs ≤ bs := by rw [le_iff_lt_or_eq] at bs_cs'; simp_all
    --             simp [cs_bs']
    --             grind
    --           else
    --             grind
    --       else
    --         have bs_as' : bs ≤ as := by rw [le_iff_lt_or_eq] at as_bs'; simp_all
    --         simp [bs_as', as_cs]
    --         if bs_cs' : bs ≤ cs then
    --           have cs_bs' : ¬cs ≤ bs := by rw [le_iff_lt_or_eq] at bs_cs'; simp_all
    --           grind
    --         else
    --           have cs_bs' : cs ≤ bs := by rw [le_iff_lt_or_eq] at bs_cs'; simp_all
    --           simp [cs_bs', as_bs, bs_as']
    --           intro h
    --           have : as ≤ cs := by simp_all [le_iff_lt_or_eq]
    --           simp [this, cs_as]
    --           grind [le_trans]





  zero_add := by
    intro ⟨as, ar⟩
    simp_all only [add_simp, add, zero_add, zero_le, sup_of_le_right, ne_eq, not_false_eq_true,
      and_true, and_self, ↓reduceDIte, dite_eq_ite, ite_eq_left_iff, ite_eq_right_iff, mk.injEq,
      true_and]
    grind
  add_zero := by
    intro ⟨as, ar⟩
    simp_all only [add_simp, add, add_zero, zero_le, sup_of_le_left, ne_eq, not_false_eq_true,
      and_self, ↓reduceDIte, dite_eq_ite, ite_eq_right_iff, implies_true]
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := by
    intro ⟨as, ar⟩ ⟨bs, br⟩
    simp_all only [add_simp, add, sup_eq_left, ne_eq, not_false_eq_true, and_true, sup_eq_right]
    split_ifs <;> subst_eqs <;> try grind [add_comm, le_antisymm]

  left_distrib := by
    sorry
    -- intro ⟨as, ar⟩ ⟨bs, br⟩ ⟨cs, cr⟩
    -- apply eq_iff.mpr
    -- simp_all only [add_simp, add, sup_eq_left, ne_eq, not_false_eq_true, and_true, sup_eq_right,
    --   mul_dite, mul_simp, mul, ite_and, mul_zero, ite_not, ↓reduceIte, zero_mul, ite_self, ite_a,
    --   ite_b]
    -- sorry
    -- if as = bs then
    --   subst_eqs
    --   simp +contextual
    --   if as = cs then
    --     subst_eqs
    --     simp +contextual [left_distrib]
    --     congr
    --     -- grind
    -- split_ifs

  right_distrib := sorry
  zero_mul := by
    simp [eq_iff, mul]
    split_ands <;> rfl
  mul_zero := by
    simp [eq_iff, mul]
    split_ands <;> rfl
  mul_assoc := by
    intro ⟨as, ar⟩ ⟨bs, br⟩ ⟨cs, cr⟩
    sorry
    -- simp +contextual [mul, ite_and]
  one_mul := by
    intro ⟨as, ar⟩
    simp_all [mul, ite_and, eq_comm]
    if h : (0 : α) = 1 then
      have : ∀ (x : α), x = 0 := eq_zero_of_zero_eq_one h
      simp_all
      sorry
    else
      simp_all
      grind
    -- split_ifs <;> subst_eqs <;> simp_all
  mul_one := sorry

end LexicalSemiring

namespace WeightedChain

variable [WeightedPartialOrder α] (C : WeightedChain α) (f : α → Prop) [DecidablePred f] (b : α)

def filter_fun : ℕ → α
  | 0 => if f (C 0) then C 0 else b
  | n + 1 => if f (C (n + 1)) then C (n + 1) else filter_fun n

-- TODO: hb can be loosened to be ∀ i, f (C i) → b ≼ C i
def filter (hb : b ≼ C 0) (_hb' : f b) :
    WeightedChain α :=
  ⟨C.filter_fun f b, by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ k hik ih =>
      apply WeightedPartialOrder.wle_trans ih; clear ih
      simp [filter_fun]
      split_ifs with h
      · suffices C.filter_fun f b k ≼ C k by apply WeightedPartialOrder.wle_trans this (C.prop (by simp))
        clear! i j h
        induction k with
        | zero =>
          simp [filter_fun]; split_ifs <;> simp_all
        | succ k ihk =>
          simp_all [filter_fun]
          split_ifs
          · simp
          · apply WeightedPartialOrder.wle_trans ihk (C.prop (by simp))
      · simp
  ⟩

theorem filter_filters {hb} {hb'} (i) : f (C.filter f b hb hb' i) := by
  induction i with (simp_all only [filter, filter_fun, DFunLike.coe]; grind)

end WeightedChain

instance [WeightedAdd α] [WeightedAdd β] : WeightedAdd (α × β) where
  wAdd a b := (a.1 ⨁ b.1, a.2 ⨁ b.2)
instance [WeightedMul α] [WeightedMul β] : WeightedMul (α × β) where
  wMul a b := (a.1 ⨀ b.1, a.2 ⨀ b.2)

instance Prod.instWeightedLE [WeightedLE α] [WeightedLE β] : WeightedLE (α × β) where
  wle a b := a.1 ≼ b.1 ∧ a.2 ≼ b.2

instance Lex.instWeightedLE [WeightedLE α] [WeightedLE β] : WeightedLE (Lex (α × β)) where
  wle a b := a.1 ≺ b.1 ∨ (a.1 = b.1 ∧ a.2 ≼ b.2)

-- TODO: find a more appropriate name
class WeightedAddIsSelect (α : Type) [WeightedLE α] [WeightedAdd α] where
  wAdd_eq_left_or_right : ∀ a b : α, a ⨁ b = a ∨ a ⨁ b = b

attribute [simp] WeightedAddIsSelect.wAdd_eq_left_or_right

@[simp]
theorem WeightedAddIsSelect.wAdd_self {α : Type} [WeightedLE α] [WeightedAdd α] [WeightedAddIsSelect α] {s : α} :
    s ⨁ s = s := by
  grind [wAdd_eq_left_or_right]

@[simp]
theorem WeightedAddIsSelect.not_wAdd_eq_left {α : Type} [WeightedLE α] [WeightedAdd α] [WeightedAddIsSelect α] {s₁ s₂ : α} :
    ¬s₁ ⨁ s₂ = s₁ ↔ s₁ ≠ s₂ ∧ s₁ ⨁ s₂ = s₂ := by
  have := WeightedAddIsSelect.wAdd_eq_left_or_right s₁ s₂
  grind

@[simp]
theorem WeightedAddIsSelect.not_wAdd_eq_left' {α : Type} [WeightedLE α] [WeightedAdd α] [WeightedAddIsSelect α] {s₁ s₂ s₃ : α} :
    s₁ ⨁ s₂ = s₃ → s₁ = s₃ ∨ s₂ = s₃ := by
  have := WeightedAddIsSelect.wAdd_eq_left_or_right s₁ s₂
  grind

@[simp]
theorem WeightedAddIsSelect.not_wAdd_eq_left'' {α : Type} [WeightedLE α] [WeightedAdd α] [WeightedAddIsSelect α] {s₁ s₂ s₃ : α} :
    ¬s₁ = s₃ → ¬s₂ = s₃ → ¬s₁ ⨁ s₂ = s₃ := by
  have := WeightedAddIsSelect.wAdd_eq_left_or_right s₁ s₂
  grind

@[simp]
theorem WeightedAddIsSelect.wAdd_wAdd {α : Type} [WeightedLE α] [WeightedPreSemiring α] [WeightedAddIsSelect α] {s₁ s₂ s₃ : α} :
    s₁ ⨁ s₂ ⨁ s₃ = s₃ ↔ s₁ ⨁ s₃ = s₃ ∧ s₂ ⨁ s₃ = s₃ := by
  constructor
  · intro h
    if s₁ ⨁ s₂ = s₁ then
      grind [WeightedPreSemiring.wAdd_assoc, WeightedPreSemiring.wAdd_comm]
    else
      grind [not_wAdd_eq_left, WeightedPreSemiring.wAdd_assoc, WeightedPreSemiring.wAdd_comm]
  · grind [WeightedPreSemiring.wAdd_assoc]

instance [DecidableEq α] [WeightedAdd α] [WeightedLE α] [WeightedAddIsSelect α] [WeightedAdd β] :
    WeightedAdd (Lex (α × β)) where
  wAdd := fun (s, r) (s', r') ↦
    if _ : s = s'      then (s, r ⨁ r') else
    if _ : s ⨁ s' = s  then (s, r) else
    if _ : s ⨁ s' = s' then (s', r') else
    False.elim (by rcases WeightedAddIsSelect.wAdd_eq_left_or_right s s' <;> contradiction)

instance
  [DecidableEq α] [WeightedZero α] [WeightedMul α]
  [DecidableEq β] [WeightedZero β] [WeightedMul β] :
    WeightedMul (Lex (α × β)) where
  wMul := fun (s, r) (s', r') ↦
    if s = 𝟘 ∧ s' = 𝟘 then (𝟘, 𝟘) else
    if s = 𝟘 ∧ s' ≠ 𝟘 then (𝟘, r) else
    if s ≠ 𝟘 ∧ s' = 𝟘 then (𝟘, r') else
    (s ⨀ s', r ⨀ r')

@[simp] instance [WeightedZero α] [WeightedZero β] : WeightedZero (Lex (α × β)) := ⟨(𝟘, 𝟘)⟩
@[simp] instance [WeightedOne α] [WeightedOne β] : WeightedOne (Lex (α × β)) := ⟨(𝟙, 𝟙)⟩

-- TODO: find a more appropriate name
class WeightedMulNoZeroDivisors (α : Type) [WeightedZero α] [WeightedMul α] where
  wMul_eq_zero_iff : ∀ {a b : α}, a ⨀ b = 𝟘 ↔ a = 𝟘 ∨ b = 𝟘

attribute [simp] WeightedMulNoZeroDivisors.wMul_eq_zero_iff

@[simp]
theorem WeightedMulNoZeroDivisors.zero_eq_wMul_iff {α : Type}  [WeightedZero α] [WeightedMul α] [WeightedMulNoZeroDivisors α] :
    ∀ {a b : α}, 𝟘 = a ⨀ b ↔ a = 𝟘 ∨ b = 𝟘 := by
  simp [eq_comm]

variable [DecidableEq α] [WeightedSemiring α] [WeightedOmegaCompletePartialOrder α] [WeightedOmegaContinuousPreSemiring α]
variable [WeightedAddIsSelect α] [WeightedMulNoZeroDivisors α]
variable [DecidableEq β] [WeightedSemiring β] [WeightedOmegaCompletePartialOrder β] [WeightedOmegaContinuousPreSemiring β]
variable [WeightedAddIsSelect β]

instance : WeightedSemiring (Lex (α × β)) where
  wAdd_assoc := by
    simp only [WeightedAdd.wAdd, dite_eq_ite, Lex.forall, toLex, Equiv.toFun_as_coe, Equiv.coe_refl,
      id_eq, Prod.mk.eta, Prod.forall]
    intro s₁ r₁ s₂ r₂ s₃ r₃
    if h : s₁ = s₂ ∧ s₂ = s₃ then
      grind [WeightedPreSemiring.wAdd_assoc]
    else if h : s₁ = s₂ ∧ s₂ ≠ s₃ then
      grind
    else if h : s₁ ≠ s₂ ∧ s₂ = s₃ then
      grind
    else if h : s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ then
      if s₁ ⨁ s₂ ⨁ s₃ = s₁ then
        grind
      else if s₁ ⨁ s₂ ⨁ s₃ = s₂ then
        grind
      else if s₁ ⨁ s₂ ⨁ s₃ = s₃ then
        grind [WeightedAddIsSelect.wAdd_wAdd]
      else
        grind
    else
      if s₁ ⨁ s₂ = s₁ then
        grind [WeightedPreSemiring.wAdd_comm]
      else
        grind [WeightedPreSemiring.wAdd_comm]
  wZero_add := by
    simp [toLex, WeightedAdd.wAdd]
    intro a b
    split_ifs
    · subst_eqs
      rfl
    · subst_eqs; contradiction
    · rfl
  add_wZero := by
    simp [toLex, WeightedAdd.wAdd]
    intro a b
    rfl
  wNsmul n s := if n = 0 then 𝟘 else s
  wNsmul_wZero := by simp
  wNsmul_succ := by
    simp [toLex]
    intro n a b
    split_ifs
    · sorry
    · sorry
  wAdd_comm := by
    simp only [WeightedAdd.wAdd, dite_eq_ite, Lex.forall, toLex, Equiv.toFun_as_coe, Equiv.coe_refl,
      id_eq, Prod.mk.eta, Prod.forall]
    intro s r s' r'
    grind [WeightedPreSemiring.wAdd_comm]
  left_distrib := by
    simp only [WeightedMul.wMul, WeightedAdd.wAdd, dite_eq_ite, ne_eq, Lex.forall, DFunLike.coe,
      toLex, Equiv.refl, Equiv.toFun_as_coe, id_eq, Prod.mk.eta, Prod.forall]
    intro s₁ r₁ s₂ r₂ s₃ r₃
    if s₁ = 𝟘 ∧ s₂ = 𝟘 ∧ s₃ = 𝟘 then
      grind [WeightedAddIsSelect.wAdd_self]
    else
      sorry
    -- if s₁ = 𝟘 then
    --   grind [WeightedPreSemiring.add_wZero, WeightedPreSemiring.wZero_add, WeightedAddIsSelect.wAdd_self]
    -- else
    --   if s₂ = s₃ then
    --     grind [WeightedPreSemiring.left_distrib]
    --   else
    --     if s₂ = 𝟘 then
    --       subst_eqs
    --       grind [WeightedPreSemiring.wZero_add, WeightedMulNoZeroDivisors.zero_eq_wMul_iff]
    --     else
    --       simp_all only [↓reduceIte, not_false_eq_true, false_and, true_and, and_self, and_true,
    --         and_false]
    --       if s₃ = 𝟘 then
    --         grind [WeightedPreSemiring.add_wZero, WeightedMulNoZeroDivisors.wMul_eq_zero_iff]
    --       else
    --         simp_all
    --         if s₂ = s₃ then
    --           grind
    --         else
    --           if s₂ ⨁ s₃ = s₂ then
    --             if s₁ ⨀ s₂ = s₁ ⨀ s₃ then
    --               simp_all
    --               grind
    --             else
    --               sorry
    --           else
    --             sorry
  right_distrib := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  wZero_mul := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  mul_wZero := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  mul_assoc := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  wOne_mul := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  mul_wOne := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  natCast := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  natCast_zero := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  natCast_succ := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  wNpow := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  wNpow_succ := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
  wNpow_zero := by sorry -- simp [WeightedAdd.wAdd, WeightedMul.wMul, WeightedLE.wle]
