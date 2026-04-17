module

public import WeightedNetKAT.Listed
public meta import WeightedNetKAT.Listed
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Group.Nat.Defs


@[expose] public section

namespace Nat

theorem digits_ofDigits' (b : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b) :
    b.digits (ofDigits b L) = L.rdropWhile (· = 0) := by
  rw [← digits_ofDigits b h (L.rdropWhile _)]
  · simp
    induction L using List.reverseRec with simp_all
    | append_singleton L l ih =>
      simp [ofDigits_append, List.rdropWhile_concat]
      split_ifs <;> simp_all [ofDigits_append]
  · intro l hl
    if h' : l ∈ L then
      apply w₁ _ h'
    else
      clear w₁
      contrapose! hl
      refine List.forall_mem_ne.mp ?_
      contrapose! h'
      simp_all
      clear hl h b
      induction L using List.reverseRec generalizing l with simp_all
      | append_singleton L l' ih => grind [List.rdropWhile_concat]
  · simp_all
    intro i hi hq
    induction L using List.reverseRec with try grind [List.rdropWhile_concat]

theorem nStepInduction {P : ℕ → Prop} (b : ℕ) (hb : b ≠ 0) (base : ∀ i < b, P i) (more : (y : ℕ) → (∀ j < b * y, P j) → ∀ x < b, P (x + b * y)) (a : ℕ) :
    P a := by
  induction a using Nat.strongRec with
  | ind n ih =>
    if hn : n < b then
      apply base _ hn
    else
      simp_all
      obtain ⟨x, y, hx, ⟨_⟩⟩ : ∃ x y, x < b ∧ n = (x + b * y) := by
        use n % b, n / b
        constructor
        · refine mod_lt n ?_
          omega
        · exact Eq.symm (mod_add_div n b)
      apply more _ _ _ hx
      intro j hj
      apply ih
      omega

theorem ofDigits_eq_zero_iff (b : ℕ) (L : List ℕ) (hb : b ≠ 0) :
    ofDigits b L = 0 ↔ ∀ l ∈ L, l = 0 := by
  induction L with
  | nil => simp
  | cons l L ih => simp_all [ofDigits]

end Nat

namespace List

variable {α : Type*} (p : α → Bool) (L : List α)

theorem length_rdropWhile_le : (L.rdropWhile p).length ≤ L.length := by
  simp [rdropWhile]
  grw [length_dropWhile_le]
  simp

@[simp]
theorem getElem_rdropWhile (i : ℕ) {hi : i < (L.rdropWhile p).length} :
    (L.rdropWhile p)[i] = L[i]'(by grw [← length_rdropWhile_le]; exact hi) := by
  induction L using reverseRec with
  | nil => simp
  | append_singleton L l ih =>
    simp_all  [rdropWhile_concat]
    split_ifs
    · simp_all [getElem_append]
      grind
    · simp

theorem getElem_of_rdropWhile_le (i : ℕ) (hi : (L.rdropWhile p).length ≤ i) (hi' : i < L.length) :
    p L[i] := by
  induction L using reverseRec with grind [rdropWhile_concat]

end List

namespace Vector.finBij

def invFun (n m : ℕ) (i : Fin (n ^ m)) : Vector (Fin n) m :=
  if hn : n = 0 then
    have hm : m = 0 :=  by by_contra; obtain ⟨_, hi⟩ := i; subst_eqs; simp [this] at hi
    ⟨#[], by simp [hm]⟩
  else if h' : i.val = 0 then
    Vector.ofFn fun _ ↦ ⟨0, by omega⟩
  else
    let A : Array (Fin n) := ((Nat.digits n i.val).map (fun j ↦ ⟨j % n, by
      rcases n with _ | n
      · simp_all
      refine Nat.mod_lt j ?_; have := i.isLt; contrapose this; simp at this⟩)).toArray
    ⟨A.append (Array.replicate (m - A.size) ⟨0, by omega⟩),
    by
      simp [A]; clear A
      rcases i with ⟨i, hi⟩
      simp_all only
      suffices (n.digits i).length ≤ m by omega
      rcases n with _ | _ | n
      · omega
      · grind
      rw [Nat.length_digits _ _ (by omega) h']
      exact Nat.log_lt_of_lt_pow h' hi⟩

def toFun (n m : ℕ) (v : Vector (Fin n) m) : Fin (n ^ m) :=
  ⟨Nat.ofDigits n ((v.toList.map (·.val))), by
    rcases n with _ | _ | n
    · have : m = 0 := by
        rcases m with _ | m
        · rfl
        obtain ⟨i, h⟩ := v.head
        omega
      subst_eqs
      simp_all
      rcases v with ⟨⟨l⟩, h⟩
      simp at h
      subst_eqs
      simp
    · simp
    · have := Nat.ofDigits_lt_base_pow_length (b:=n + 2) (l:=v.toList.map (·.val))
      simp at this
      exact this⟩

theorem isLeftInv (n m : ℕ) (i : Fin (n ^ m)) :
    toFun n m (invFun n m i) = i := by
  simp [toFun]
  rcases i with _ | i
  · rcases n with _ | n
    · simp_all [invFun]
    · simp_all [invFun, Vector.toList_ofFn]
  · if hn : n = 0 then
      subst_eqs
      rename_i h
      rcases m with _ | m <;> simp at h
    else
    simp_all [invFun]
    have {α : Type} [DecidableEq α] (x : α) (xs : List α) (n : ℕ) : List.rdropWhile (· = x) (xs ++ List.replicate n x) = List.rdropWhile (· = x) xs := by
      induction n with
      | zero => simp
      | succ n ih =>
        have : xs ++ List.replicate (n + 1) x = (xs ++ List.replicate n x) ++ [x] := by simp [List.replicate_add]
        rw [this]
        rw [List.rdropWhile_concat_pos _ _ _ (by simp)]
        simp [ih]
    unfold Function.comp
    simp
    suffices List.map (fun x ↦ x % n) (n.digits (i + 1)) = n.digits (i + 1) by
      simp [this]
      apply Nat.ofDigits_digits
    apply List.ext_getElem
    · simp
    · simp
      intro  j h₁ h₂
      have : (n.digits (i + 1))[j] ∈ (n.digits (i + 1)) := by simp
      rcases n with _ | _ | n
      · simp
      · simp_all
      have := Nat.digits_lt_base (by omega) this
      simp_all

theorem isRightInv (n m : ℕ) (v : Vector (Fin n) m) :
    invFun n m (toFun n m v) = v := by
  rcases v with ⟨⟨v⟩⟩
  subst_eqs
  simp_all [Array.size]
  simp [invFun, toFun]
  if n = 0 then
    subst_eqs
    simp
    rcases v with _ | ⟨⟨x, _⟩, _⟩
    · rfl
    omega
  else
  split_ifs with h
  · simp_all
    rcases n with _ | n
    · ext
      · simp
      · contradiction
    · simp_all [Nat.ofDigits_eq_zero_iff]
      ext i
      · simp_all
      · simp_all
        specialize h v[i]
        grind
  · simp_all
    rcases n with _ | _ | n
    · rcases v with _ | ⟨a, v⟩
      · simp_all
      · absurd a.isLt; omega
    · simp_all; simp_all
    by_cases h' : ¬∀ (h : ¬v = []), ¬v.getLast h = 0
    · simp_all
      obtain ⟨h₁, h₂⟩ := h'
      apply List.ext_getElem
      · simp_all
        refine Nat.add_sub_of_le ?_
        rw [Nat.digits_ofDigits']
        · grw [List.length_rdropWhile_le]
          simp
        · simp
        · simp_all; omega
      simp_all
      intro i hi₁ hi₂
      simp [List.getElem_append]
      split_ifs with h'
      · simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Fin.is_lt, implies_true,
        Nat.digits_ofDigits', List.getElem_rdropWhile, List.getElem_map]
        refine Fin.eq_of_val_eq ?_
        simp
        omega
      · simp_all
        rw [Nat.digits_ofDigits'] at h'
        · have := List.getElem_of_rdropWhile_le (· = 0) (v.map (·.val))
          simp_all
        · simp_all
        · simp_all
          omega
    rw [Nat.digits_ofDigits']
    · simp_all
      apply List.ext_getElem
      · simp
        refine Nat.add_sub_of_le ?_
        grw [List.length_rdropWhile_le]
        simp
      · simp [List.getElem_append]
        intro i h₁ h₂
        split_ifs with h'
        · refine Fin.eq_of_val_eq ?_
          simp
          omega
        · simp_all
          have := List.getElem_of_rdropWhile_le (· = 0) (v.map (·.val))
          simp at this
          grind
    · simp_all
    · simp_all
      omega

end Vector.finBij

open Vector.finBij in
@[specialize]
def Vector.finBij (n m : ℕ) : Fin (n ^ m) ≃ Vector (Fin n) m where
  toFun := invFun n m
  invFun := toFun n m
  left_inv := isLeftInv _ _
  right_inv := isRightInv _ _

namespace Listed

variable {α β : Type*} [Listed α] [Listed β]

@[specialize]
instance (n : ℕ) : Listed (Vector α n) :=
  let e₀ := Listed.equivFin (α := α)
  let e₁ := ⟨(·.map e₀.symm), (·.map e₀), by intro; simp, by intro; simp⟩
  Listed.ofEquiv ((Vector.finBij _ _).trans e₁)

@[implicit_reducible]
def pi (α β : Type*) [Listed α] [Listed β] [Inhabited β] : Listed (α → β) :=
  let e : Vector β (Listed.size α) ≃ (α → β) := {
    toFun v a := v[Listed.encodeFin a]
    invFun f := Vector.ofFn (f ∘ Listed.decodeFin)
    left_inv := by unfold Function.comp; intro; simp
    right_inv := by unfold Function.comp; intro; simp
  }
  Listed.ofEquiv e

instance [Repr α] [Repr β] : Repr (α → β) where
  reprPrec f n := reprPrec ((listOf α).map (fun a ↦ (a, f a))) n

/--
info: [[(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 1)]]
-/
#guard_msgs in
#eval letI := pi T (Fin 2); listOf (T → Fin 2)

end Listed
