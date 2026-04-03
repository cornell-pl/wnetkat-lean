import Batteries.Data.Array.Pairwise
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Vector.Basic

-- def printprint {α β : Type*} [ToString β] (msg : β) (a : α) : α :=
--   (unsafe unsafeIO (do
--     println! msg
--     let stdout ← IO.getStdout
--     stdout.flush
--     return a
--   )).toOption.getD a

-- def timeitit {α β : Type*} [Inhabited α] [ToString β] (msg : β) (a : IO α) : α :=
--   (unsafe unsafeIO (do
--     let a ← timeit (toString msg) a
--     let stderr ← IO.getStderr
--     stderr.flush
--     return a
--   )).toOption.get!

-- @[simp]
-- theorem printprint_id {α β : Type*} [ToString β] (msg : β) (a : α) : printprint msg a = a := by
--   sorry

namespace List

variable {α β : Type*}

#eval (List.ofFn (n:=5) (·.val)) ×ˢ (List.ofFn (n:=5) (·.val))

theorem getElem_product {l₁ : List α} {l₂ : List β} {i} (hi : i < (l₁ ×ˢ l₂).length) :
      (l₁ ×ˢ l₂)[i]
    = (l₁[i / l₂.length]'(by
        rw [List.length_product] at hi
        exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)).mpr hi
      ),
       l₂[i % l₂.length]'(by
        rw [List.length_product] at hi
        have : 0 < l₁.length := Nat.pos_of_lt_mul_right hi
        have : 0 < l₂.length := Nat.pos_of_lt_mul_left hi
        apply Nat.mod_lt; omega
      )) := by
  simp [SProd.sprod, product]
  induction l₁ generalizing i l₂ with
  | nil => simp at hi
  | cons x l₁ ih =>
    simp [List.length_product] at hi
    simp_all
    rw [List.getElem_append]
    simp_all
    split_ifs
    · simp_all [Nat.mod_eq_of_lt]
      have : i / l₂.length = 0 := by simp_all [Nat.div_eq_of_lt]
      grind
    · rw [ih (by simp [List.length_product]; omega)]
      simp
      constructor
      · rw [List.getElem_cons]
        split_ifs with h₂
        · simp_all
          -- rcases h₂ with (⟨_, _⟩ | _)
          -- · simp_all
          -- · simp_all
        · congr
          simp_all [Nat.mod_eq_of_lt]
          rcases l₂ with _ | ⟨x, l₂⟩
          · contradiction
          · simp
            rw [Nat.div_eq_sub_div]
            · sorry
            · simp
            · sorry

      · sorry



end List

namespace Array

variable {α β : Type*}

def product (l₁ : Array α) (l₂ : Array β) : Array (α × β) :=
  l₁.flatMap (fun (a : α) => l₂.map (Prod.mk a))

instance : SProd (Array α) (Array β) (Array (α × β)) := ⟨product⟩

theorem product_eq_toList_product (l₁ : Array α) (l₂ : Array β) :
    (l₁ ×ˢ l₂).toList = l₁.toList ×ˢ l₂.toList := by
  simp [SProd.sprod, product, List.product]
theorem mem_product_iff_mem_toList_product (l₁ : Array α) (l₂ : Array β) {x} :
    x ∈ l₁ ×ˢ l₂ ↔ x ∈ l₁.toList ×ˢ l₂.toList := by
  rw [← product_eq_toList_product]
  simp

@[simp]
theorem mem_product {l₁ : Array α} {l₂ : Array β} {x} : x ∈ l₁ ×ˢ l₂ ↔ x.1 ∈ l₁ ∧ x.2 ∈ l₂ := by
  rcases x; simp [mem_product_iff_mem_toList_product]
@[simp]
theorem mem_product' {l₁ : Array α} {l₂ : Array β} {x} : x ∈ product l₁ l₂ ↔ x.1 ∈ l₁ ∧ x.2 ∈ l₂ := mem_product
@[simp]
theorem pair_mem_product {l₁ : Array α} {l₂ : Array β} {x} {y} : (x, y) ∈ l₁ ×ˢ l₂ ↔ x ∈ l₁ ∧ y ∈ l₂ := by
  simp

def size_product {l₁ : Array α} {l₂ : Array β} : (l₁ ×ˢ l₂).size = l₁.size * l₂.size := by
  convert List.length_product (l₁:=l₁.toList) (l₂:=l₂.toList)
  simp [← product_eq_toList_product]

def Nodup (l : Array α) : Prop := l.Pairwise (· ≠ ·)

@[simp, grind]
theorem nodup_empty : Nodup (#[] : Array α) := by simp [Nodup, Pairwise]
@[simp, grind]
theorem nodup_singleton {a} : Nodup (#[a] : Array α) := by simp [Nodup, Pairwise]
@[simp, grind]
theorem nodup_pair {a b} : Nodup (#[a, b] : Array α) ↔ a ≠ b := by simp [Nodup, Pairwise]

theorem nodup_iff_toList_nodup (l : Array α) : l.toList.Nodup ↔ l.Nodup := by
  simp [Nodup, Pairwise, List.Nodup] at *

def Nodup.product {l₁ : Array α} {l₂ : Array β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) : (l₁ ×ˢ l₂).Nodup := by
  simp [Nodup, Pairwise] at *
  refine List.nodup_iff_pairwise_ne.mp ?_
  have := List.Nodup.product d₁ d₂
  convert this
  simp [SProd.sprod, List.product, Array.product]
  refine List.eq_toArray_iff.mpr ?_
  simp

theorem nodup_append {l₁ l₂ : Array α} :
    (l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ ∀ (a : α), a ∈ l₁ → ∀ (b : α), b ∈ l₂ → a ≠ b := by
  have := List.nodup_append (l₁:=l₁.toList) (l₂:=l₂.toList)
  simp [← nodup_iff_toList_nodup]
  convert this <;> (ext; simp)

theorem Nodup.map {l : Array α} {f : α → β} (hf : Function.Injective f) :
    l.Nodup → (map f l).Nodup := by
  intro h
  simp_all [← nodup_iff_toList_nodup]
  apply List.Nodup.map hf h

theorem nodup_finRange (n : ℕ) : (Array.finRange n).Nodup := by
  simp [← nodup_iff_toList_nodup]
  convert List.nodup_finRange n
  ext <;> simp

@[simp]
theorem mem_finRange {n : ℕ} (a) : a ∈ Array.finRange n :=
  mem_of_getElem (Array.getElem_finRange (by simp))

theorem nodup_map_iff_inj_on {f : α → β} {l : Array α} (d : l.Nodup) :
    (map f l).Nodup ↔ ∀ (x : α), x ∈ l → ∀ (y : α), y ∈ l → f x = f y → x = y := by
  have := List.nodup_map_iff_inj_on (f:=f) d
  simp [← nodup_iff_toList_nodup]
  convert this <;> (ext; simp)

end Array

class Listed (α : Type*) where
  array : Array α
  nodup : array.Nodup
  size : ℕ := array.size
  size_prop : array.size = size := by rfl
  complete : ∀ a, a ∈ array
  encode : α → ℕ
  encode_len : ∀ a, encode a < array.size := by grind
  encode_prop : ∀ a, array[encode a]'(encode_len a) = a := by grind

namespace Listed

@[implicit_reducible]
def ofArray {α : Type*} [DecidableEq α]
    (array : Array α) (nodup : array.Nodup) (complete : ∀ a, a ∈ array) : Listed α where
  array
  nodup
  complete
  encode a := array.findIdx (· = a)

instance : Listed Unit where
  array := #[()]
  size := 1
  nodup := by simp [Array.Nodup, Array.Pairwise]
  complete := by simp
  encode _ := 0

variable {α β : Type*}
variable [Listed α] [Listed β]

def encode_inj : Function.Injective (Listed.encode (α:=α)) := by
  intro a b h; have := encode_prop a; have := encode_prop b; grind [encode_prop]

instance : Countable α := ⟨⟨Listed.encode, Listed.encode_inj⟩⟩

@[implicit_reducible]
def lift [Listed α] {γ : Type*} (f : α ≃ γ) : Listed γ where
  array := array.map f
  size := array.size
  size_prop := by simp; rfl
  nodup := by
    simp [Array.Nodup, Array.Pairwise]
    refine List.nodup_iff_pairwise_ne.mp ?_
    apply List.Nodup.map (Equiv.injective f)
    grind [nodup, Array.nodup_iff_toList_nodup, List.Nodup.map]
  complete i := by
    have := complete (f.symm i)
    grind
  encode i := encode (f.symm i)
  encode_len := by simp [encode_len]
  encode_prop := by simp [encode_prop]

@[simp, grind] theorem mem_list (a : α) : a ∈ array := complete a

attribute [simp] Listed.nodup

def arrayOf (α : Type*) [Listed α] : Array α := Listed.array
def listOf (α : Type*) [Listed α] : List α := Listed.array.toList

@[simp, grind] theorem mem_arrayOf (a : α) : a ∈ arrayOf α := complete a
@[simp, grind] theorem mem_listOf (a : α) : a ∈ listOf α := by simp [listOf]

def decode (i : ℕ) : Option α := array[i]?

@[simp, grind]
theorem encode_decode (a : α) : decode (encode a) = some a := by
  simp [decode]
  have := encode_prop a
  nth_rw 2 [← this]
  exact Array.getElem?_eq_getElem (encode_len a)
theorem decode_eq_some (n : ℕ) (a : α) : decode n = some a ↔ encode a = n := by
  simp [decode]
  constructor
  · intro h
    have h₁ : n < (array : Array α).size := by contrapose! h; simp_all
    have h₂ : (array : Array α)[n] = a := by grind
    have h₃ := encode_prop a
    have h₄ := (Listed.nodup (α:=α))
    subst_eqs
    exact (List.Nodup.getElem_inj_iff h₄).mp h₃
  · intro h
    subst_eqs
    refine Array.getElem_eq_iff.mp (encode_prop a)

@[simp, grind]
theorem decode_get_encode (n : ℕ) (h : (decode (α:=α) n).isSome) :
    encode ((decode n).get h) = n := by
  simp [decode] at h ⊢
  have h₁ : n < (array : Array α).size := by contrapose! h; simp_all
  have h₃ := encode_prop array[n]
  have := nodup (α:=α)
  have := List.Nodup.getElem_inj_iff (nodup (α:=α)) (i:=n) (j:=encode array[n]) (hi:=h) (hj:=by simp [encode_len])
  grind

def encodeFin {α : Type*} [i : Listed α] : α → Fin i.size :=
  fun a ↦ ⟨i.encode a, by simp [encode_len, ← size_prop]⟩
def decodeFin {α : Type*} [i : Listed α] : Fin i.size → α :=
  fun a ↦ i.decode a |>.get (by obtain ⟨a, ha⟩ := a; grind [decode, size_prop])

@[simp, grind]
theorem decodeFin_encodeFin {α : Type*} [i : Listed α] (a) :
    i.encodeFin (i.decodeFin a) = a := by
  simp [encodeFin, decodeFin]

@[simp]
theorem encodeFin_decodeFin {α : Type*} [i : Listed α] (a) :
    i.decodeFin (i.encodeFin a) = a := by
  grind [encodeFin, decodeFin, encode_decode]

def equivFin {α : Type*} [Listed α] : α ≃ Fin (Listed.size α) := ⟨
  encodeFin,
  decodeFin,
  by intro; simp,
  by intro; simp⟩

def decodeFin_inj : Function.Injective (Listed.decodeFin (α:=α)) := by
  intro a b h
  have := congrArg encodeFin h
  grind

def encodeFin_bijective : Function.Bijective (encodeFin (α:=α)) := by
  constructor
  · intro a b h; simp [encodeFin] at h; exact encode_inj h
  · intro i; use decodeFin i; simp
def decodeFin_bijective : Function.Bijective (decodeFin (α:=α)) := by
  constructor
  · intro a b h; exact decodeFin_inj h
  · intro i; use encodeFin i; simp

@[implicit_reducible]
def fintype [DecidableEq α] : Fintype α := {
  elems := (listOf α).toFinset
  complete := by simp [listOf, complete]
}

-- @[simp] theorem list_toFinset [DecidableEq α] : (list (α:=α)).toFinset = @Finset.univ α fintype := rfl
@[simp] theorem array_toFinset [DecidableEq α] : (array (α:=α)).toList.toFinset = @Finset.univ α fintype := rfl

instance [DecidableEq α] [DecidableEq β] : Listed (α × β) :=
  let A := array ×ˢ array
  {
    array := A
    size := Listed.size α * Listed.size β
    size_prop := by simp [A, Array.size_product, size_prop]
    nodup := Array.Nodup.product nodup nodup
    complete := by intro ⟨a, b⟩; simp [A, complete]
    encode a := A.findIdx (· = a)
    encode_len := by simp [A]
    encode_prop a := by
      have := Array.findIdx_getElem (p:=(· = a)) (xs:=A) (w:=?_)
      simp at this; exact this
    -- encode := fun (a, b) ↦ encode a + (size α * encode b)
    -- encode_len := by
    --   intro (a, b)
    --   simp [List.instSProd, List.product, size]
    --   have := encode_len a
    --   have := encode_len b
    --   sorry
    -- encode_prop := by
    --   intro (a, b)
    --   simp
    --   sorry
  }

instance : Listed (α ⊕ β) where
  array := array.map .inl ++ array.map .inr
  size := Listed.size α + Listed.size β
  size_prop := by simp [size_prop]
  nodup := by
    refine Array.nodup_append.mpr ?_
    split_ands
    · refine Array.Nodup.map Sum.inl_injective nodup
    · refine Array.Nodup.map Sum.inr_injective nodup
    · grind
  complete := by rintro (a | b) <;> simp_all
  encode
  | .inl a => encode a
  | .inr b => size α + encode b
  encode_len := by
    rintro (a | b)
    · simp; have := encode_len a; omega
    · simp [← size_prop]; have := encode_len b; omega
  encode_prop := by
    rintro (a | b)
    · simp; have := encode_len a; simp [this]; exact encode_prop a
    · simp [← size_prop]; exact encode_prop b

@[grind]
inductive T where | a | b | c | d
deriving DecidableEq, Repr, Inhabited

instance : Listed T where
  array := #[.a, .b, .c, .d]
  nodup := by grind [Array.Nodup, Array.Pairwise]
  complete := by grind
  encode | .a => 0 | .b => 1 | .c => 2 | .d => 3

instance {n : ℕ} : Listed (Fin n) where
  array := Array.finRange n
  size := n
  size_prop := by simp
  nodup := Array.nodup_finRange n
  complete := Array.mem_finRange
  encode a := a.val
  encode_len := by simp
  encode_prop := by simp

@[simp] theorem fin_size {n} : Listed.size (α:=Fin n) = n := by simp [size]
@[simp] theorem fin_size' {n} : (@array (Fin n) instFin).size =n := by simp [array]

/--
info: [(0, Listed.T.a),
 (0, Listed.T.b),
 (0, Listed.T.c),
 (0, Listed.T.d),
 (1, Listed.T.a),
 (1, Listed.T.b),
 (1, Listed.T.c),
 (1, Listed.T.d),
 (2, Listed.T.a),
 (2, Listed.T.b),
 (2, Listed.T.c),
 (2, Listed.T.d)]
-/
#guard_msgs in
#eval listOf (Fin 3) ×ˢ listOf T

def decidableEqPi [DecidableEq α] [DecidableEq β] : DecidableEq (α → β) :=
  fun f g ↦
    if h : array.all fun a ↦ f a = g a then
      .isTrue (by
        simp_all; ext i; specialize h (encode i); convert h _
        · simp [encode_prop]
        · simp [encode_prop]
        · exact encode_len i)
    else
      .isFalse (by grind)

@[inline]
def cool_bijection.toFun (n m : ℕ)
    (i : Fin (n ^ m)) : Vector (Fin n) m :=
  .ofFn fun p ↦ ⟨(i.val / n^p.val) % n, by
    obtain ⟨i, hi⟩ := i
    obtain ⟨p, hp⟩ := p
    apply Nat.mod_lt
    rcases n with _ | n
    · rw [Nat.zero_pow] at hi <;> omega
    · omega⟩

@[inline]
def cool_bijection.invFun (n m : ℕ)
    (v : Vector (Fin n) m) : Fin (n ^ m) :=
  if h : n ^ m = 0 then
    ⟨0, by simp_all; let := v[0].isLt; omega⟩
  else
    have : NeZero (n^m) := ⟨h⟩
    v.mapIdx (fun p ⟨x, hx⟩ ↦ ⟨(n^p * x) % n^m, by apply Nat.mod_lt; omega⟩) |>.sum

def cool_bijection.toFun' (n m : ℕ)
    (i : ℕ) : Array ℕ :=
  .ofFn (n:=m) fun p ↦ (i / n^p.val) % n

def cool_bijection.invFun' (n m : ℕ)
    (v : Array ℕ) : ℕ :=
  if h : n ^ m = 0 then
    0
  else
    have : NeZero (n^m) := ⟨h⟩
    v.mapIdx (fun p x ↦ (n^p * x) % n^m) |>.sum % n ^ m

theorem Vector.toArray_sum {α : Type*} {n} [Add α] [Zero α] (v : Vector α n) :
    v.toArray.sum = v.sum := rfl
theorem Array.sum_fin_val {m} [NeZero m] (v : Array (Fin m)) :
    v.sum.val = (v.map (·.val)).sum % m := by
  rcases v with ⟨v⟩
  simp_all
  induction v with
  | nil => simp
  | cons x v ih =>
    simp_all [Fin.val_add]
@[simp]
theorem Array.mapIdx_map {α β γ : Type*} (f : ℕ → α → β) (g : β → γ) (xs : Array α) :
    (xs.mapIdx f).map g = xs.mapIdx (fun i x ↦ g (f i x)) := by
  ext <;> simp
@[simp]
theorem Array.map_mapIdx {α β γ : Type*} (f : ℕ → β → γ) (g : α → β) (xs : Array α) :
    (xs.map g).mapIdx f = xs.mapIdx (fun i x ↦ f i (g x)) := by
  ext <;> simp
@[simp]
theorem Array.ofFn_mapIdx {n} {α β : Type*} (f : Fin n → α) (g : ℕ → α → β) :
    (Array.ofFn f).mapIdx g = Array.ofFn (fun i ↦ g i (f i)) := by
  ext <;> simp
@[simp]
theorem Array.ofFn_map {n} {α β : Type*} (f : Fin n → α) (g : α → β) :
    (Array.ofFn f).map g = Array.ofFn (fun i ↦ g (f i)) := by
  ext <;> simp

theorem cool_bijection.toFun_eq_toFun' (n m : ℕ) (hn : 0 < n) (i) : cool_bijection.toFun n m i =
    ⟨cool_bijection.toFun' n m i |>.map (⟨· % n, by apply Nat.mod_lt; omega⟩), by simp [toFun']⟩ := by
  ext; simp [toFun, toFun']
theorem cool_bijection.invFun_eq_invFun' (n m : ℕ) (i) : cool_bijection.invFun n m i =
    ⟨cool_bijection.invFun' n m (i.toArray.map (·.val)), by
      simp [invFun']; split_ifs <;> simp_all
      · have := i[0].isLt; omega
      · apply Nat.mod_lt; if m = 0 then simp_all else apply Nat.pow_pos; omega
        ⟩ := by
  simp [invFun, invFun']
  split_ifs with h
  · rfl
  · if hn : n = 0 then
      subst_eqs
      simp at h
      subst_eqs
      omega
    else
      have : NeZero (n^m) := ⟨by simp_all⟩
      rw [← Vector.toArray_sum]
      simp
      ext
      simp_all
      have {n : ℕ} {i : Fin n} : i.val = i % n := by
        refine Eq.symm (Nat.mod_eq_of_lt ?_)
        simp
      rw [this]
      congr
      sorry

set_option pp.deepTerms true in
#eval List.ofFn (n:=3^4) (fun i ↦ let v := cool_bijection.toFun _ _ i; (i, v.toArray, cool_bijection.invFun _ _ v))

@[inline]
def cool_bijection (n m : ℕ) : Fin (n^m) ≃ Vector (Fin n) m where
  toFun := cool_bijection.toFun n m
  invFun := cool_bijection.invFun n m
  left_inv := by
    intro ⟨x, hx⟩
    if hn : n = 0 then
      sorry
    else
      rw [cool_bijection.toFun_eq_toFun' _ _ (by omega), cool_bijection.invFun_eq_invFun']
      simp
      simp [cool_bijection.invFun', cool_bijection.toFun', hn]
      sorry
  right_inv := by
    intro x
    if hn : n = 0 then
      sorry
    else
      rw [cool_bijection.toFun_eq_toFun' _ _ (by omega), cool_bijection.invFun_eq_invFun']
      simp
      simp [cool_bijection.invFun', cool_bijection.toFun', hn]
      ext i hi hi'
      · simp
      · simp_all; simp_all
        rcases x with ⟨⟨x⟩, hx⟩
        simp_all
        subst_eqs
        simp_all
        induction x generalizing i with
        | nil => simp at hi'
        | cons v x ih =>
          simp_all
          rcases i with _ | i
          · simp
            sorry
          · simp
            rw [← ih _ (by omega)]
            clear ih
            simp_all
            sorry


def listVector [DecidableEq α] (n : ℕ) : {inst : Listed (List.Vector α n) // inst.size = Listed.size α ^ n } :=
  match n with
  | 0 => ⟨{
      array := #[⟨[], by simp⟩],
      size := 1
      nodup := by simp [Array.Nodup, Array.Pairwise],
      complete := by rintro ⟨_, _⟩; grind [List.eq_nil_iff_length_eq_zero]
      encode _ := 0
      encode_len := by simp
      encode_prop a := by simp; ext ⟨_, _⟩; omega
  }, by simp⟩
  | n+1 =>
    let L := (listVector n).val.array ×ˢ (arrayOf α) |>.map (fun ⟨l, a⟩ ↦ l.cons a)
    let complete := by
      simp only [SProd.sprod, Array.mem_map, Array.mem_product', mem_list, mem_arrayOf, and_self,
        true_and, Prod.exists, L]
      clear L
      intro l
      rcases l with ⟨l, hl⟩
      rcases l with _ | ⟨a, l⟩
      · grind
      · use ⟨l, by simp_all⟩, a; grind [List.Vector.cons]
    ⟨{
      array := L
      size := Listed.size α ^ (n + 1)
      size_prop := by
        simp [L, Array.size_product, arrayOf, size_prop, pow_succ]
        left
        exact (listVector n).prop
      nodup := by
        simp [L]
        clear complete
        refine (Array.nodup_map_iff_inj_on ?_).mpr ?_
        · letI := (listVector n).val
          generalize h₁ : array (α:=List.Vector α n) = l₁
          generalize h₂ : (arrayOf α) = l₂
          replace h₁ : l₁.Nodup := by rw [← h₁]; exact nodup
          replace h₂ : l₂.Nodup := by rw [← h₂]; exact nodup
          show (l₁ ×ˢ l₂).Nodup
          exact Array.Nodup.product h₁ h₂
        · simp
          intro l a j b
          obtain ⟨l, hl⟩ := l
          obtain ⟨j, hj⟩ := j
          have := List.Vector.toList_cons (n:=n) (α:=α) a ⟨l, hl⟩
          clear L
          grind [List.Vector.toList_cons, List.Vector.toList_mk]
      complete := complete
      encode a := L.findIdx (· = a)
      encode_len a := by
        simp [complete]
      encode_prop a := by
        have := Array.findIdx_getElem (p:=(· = a)) (xs:=L) (w:=?_)
        simp at this; exact this
    }, by rfl⟩

instance [DecidableEq α] (n : ℕ) : Listed (List.Vector α n) := (Listed.listVector n).val

def arrayVector_aux [DecidableEq α] (all : Array α) (all_nodup : all.Nodup) (all_complete : ∀ a, a ∈ all) (all_size : all.size = size α) (n : ℕ) :
    {inst : Listed (Vector α n) // inst.size = size α ^ n} :=
  match n with
  | 0 => ⟨{
      array := #[⟨#[], by simp⟩],
      size := 1
      nodup := by simp [Array.Nodup, Array.Pairwise],
      complete := by rintro ⟨_, _⟩; grind [List.eq_nil_iff_length_eq_zero]
      encode _ := 0
      encode_len := by simp
      encode_prop a := by simp
  }, by simp⟩
  | n+1 =>
    let L := (arrayVector_aux all all_nodup all_complete all_size n).val.array ×ˢ all |>.map (fun ⟨l, a⟩ ↦ l.push a)
    let complete := by
      simp [L, List.mem_map, Prod.exists, SProd.sprod, List.pair_mem_product, Array.mem_product, mem_list, true_and]
      clear L
      intro l
      rcases l with ⟨l, hl⟩
      use ⟨l.take n, by simp_all⟩, l[n]
      simp [all_complete]
      omega
    ⟨{
      array := L
      size := Listed.size α ^ (n + 1)
      size_prop := by
        have := (arrayVector_aux all all_nodup all_complete all_size n).prop
        simp [pow_succ, L, Array.size_product, size_prop]
        congr
      nodup := by
        simp [L]
        clear complete
        refine (Array.nodup_map_iff_inj_on ?_).mpr ?_
        · letI := (arrayVector_aux all all_nodup all_complete all_size n).val
          generalize h₁ : array (α:=Vector α n) = l₁
          generalize h₂ : all = l₂
          replace h₁ : l₁.Nodup := by rw [← h₁]; exact nodup
          replace h₂ : l₂.Nodup := by rw [← h₂]; exact all_nodup
          show (l₁ ×ˢ l₂).Nodup
          exact Array.Nodup.product h₁ h₂
        · simp [all_complete]
          intro l a j b
          obtain ⟨l, hl⟩ := l
          obtain ⟨j, hj⟩ := j
          simp [Array.push_eq_push]
          clear L
          grind
      complete := complete
      encode a := L.findIdx (· = a)
      encode_len a := by
        simp [complete]
      encode_prop a := by
        have := Array.findIdx_getElem (p:=(· = a)) (xs:=L) (w:=?_)
        simp at this; exact this
    }, by simp⟩

def arrayVector [DecidableEq α] (n : ℕ) : Listed (Vector α n) :=
  arrayVector_aux array nodup mem_list size_prop n |>.val

@[simp]
theorem Array.length_product {α β : Type*} (a : Array α) (b : Array β) :
    (a ×ˢ b : Array (α × β)).size = a.size * b.size := by
  simp [SProd.sprod]
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  simp
  cases a with
  | nil => simp [Array.product]
  | cons x a => simp [Array.product, Nat.right_distrib]; omega

@[simp]
theorem arrayVector_size [DecidableEq α] (n : ℕ) : (arrayVector (α:=α) n).size = Listed.size α ^ n := by
  induction n with
  | zero => unfold size; simp only [arrayVector, Nat.pow_zero, arrayVector_aux, pow_zero]
  | succ n ih =>
    unfold size at ih ⊢
    simp_all [size, Listed.array, arrayVector, arrayVector_aux, pow_succ]
    unfold size at ih ⊢
    simp_all

#check (arrayVector (α:=Fin 5) 7).array

def arrayVector' [DecidableEq α] (n : ℕ) : Listed (Vector α n) where
  array := .ofFn (n:=size α ^ n) fun i ↦ let v := (cool_bijection (size α) n) i; v.map decodeFin
  size := size α ^ n
  size_prop := sorry
  encode v := (cool_bijection (size α) n).symm (v.map encodeFin)
  nodup := sorry
  complete := sorry
  encode_len := sorry
  encode_prop := sorry

-- TODO: make the more efficient version sound
instance [DecidableEq α] (n : ℕ) : Listed (Vector α n) := Listed.arrayVector n
-- instance [DecidableEq α] (n : ℕ) : Listed (Vector α n) := Listed.arrayVector' n

def pi_array [Inhabited β] [DecidableEq α] [DecidableEq β] : Array (α → β) :=
  -- printprint "pi_array time" <|
    arrayOf (Vector β (size α)) |>.map (fun m a ↦ m[encode a]'(by simp [← size_prop, encode_len]))

theorem mem_pi_array  [Inhabited β] [DecidableEq α] [DecidableEq β] {f : α → β} : f ∈ pi_array := by
  simp only [pi_array]
  apply Array.mem_map.mpr
  use Vector.ofFn (fun ⟨i, hi⟩ ↦ f <| (decode i).get (by simpa [decode, listOf, size_prop]))
  grind [List.Vector.getElem_def, List.Vector.toList_ofFn]

theorem pi_array_nodup  [Inhabited β] [DecidableEq α] [DecidableEq β] :
    (pi_array (α:=α) (β:=β)).Nodup := by
  simp only [pi_array]
  refine (Array.nodup_map_iff_inj_on (by simp [arrayOf])).mpr ?_
  intro x hx y hy h
  refine Vector.ext fun i hi ↦ ?_
  have : (decode (α:=α) i).isSome = true := by simpa [decode, listOf, size_prop]
  replace := congrFun h ((decode i).get this)
  simpa only [decode_get_encode]

def pi (α β : Type*) [Listed α] [Listed β] [Inhabited β] [DecidableEq α] [DecidableEq β] : Listed (α → β) :=
  let array := pi_array
  {
    array
    nodup := pi_array_nodup
    complete _ := mem_pi_array
    encode a :=
      letI := decidableEqPi (α:=α) (β:=β)
      array.findIdx (· = a)
    encode_len a := by simp [array, mem_pi_array]
    encode_prop a := by
      letI := decidableEqPi (α:=α) (β:=β)
      have := Array.findIdx_getElem (p:=(· = a)) (xs:=array) (w:=?_)
      simp at this; exact this
  }

instance [Repr α] [Repr β] : Repr (α → β) where
  reprPrec f n := reprPrec ((listOf α).map (fun a ↦ (a, f a))) n

/--
info: [[(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 0), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 0), (Listed.T.c, 1), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 0), (Listed.T.d, 1)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 0)],
 [(Listed.T.a, 1), (Listed.T.b, 1), (Listed.T.c, 1), (Listed.T.d, 1)]]
-/
#guard_msgs in
#eval! letI := pi T (Fin 2); listOf (T → Fin 2)

@[simp]
theorem encode_eq_iff {α : Type*} [Listed α] {a b : α} :
    encode a = encode b ↔ a = b := Function.Injective.eq_iff encode_inj
@[simp]
theorem encodeFin_eq_iff {α : Type*} [Listed α] {a b : α} :
    encodeFin a = encodeFin b ↔ a = b := by simp [encodeFin]
@[simp]
theorem encodeFin_eq_encode_iff {α : Type*} [Listed α] {a b : α} :
    (encodeFin a).val = encode b ↔ a = b := by simp [encodeFin]
@[simp]
theorem encode_eq_encodeFin_iff {α : Type*} [Listed α] {a b : α} :
    encode a = (encodeFin b).val ↔ a = b := by simp [encodeFin]
@[simp]
theorem encode_unit :
    encode () = 0 := rfl
@[simp]
theorem encodeFin_unit :
    encodeFin () = 0 := rfl
@[simp]
theorem size_unit :
    size Unit = 1 := by
  simp [← size_prop, array]

@[simp]
theorem sum_fin
    {α : Type*} [Listed α] [Fintype α]
    {𝒮 : Type*} [AddCommMonoid 𝒮]
    {f : Fin (size α) → 𝒮}
    :
    ∑ (i : Fin (size α)), f i = ∑ (i : α), f (encodeFin i) :=
  (Function.Bijective.sum_comp encodeFin_bijective f).symm

instance : Unique (Fin (size Unit)) where
  uniq := by intro ⟨a, ha⟩; have : size Unit = 1 := rfl; grind

@[simp, grind =]
theorem size_isEmpty {α : Type*} [Listed α] [Subsingleton α] [i : IsEmpty α] : size α = 0 := by
  rw [← size_prop]
  simp
  suffices ∀ {xs : Array α}, xs = #[] by simp_all
  intro xs
  rcases xs with ⟨xs⟩
  simp_all
  induction xs with
  | nil => rfl
  | cons x xs => apply i.elim' x
@[simp, grind =]
theorem size_subsingleton_nonempty {α : Type*} [Listed α] [ss : Subsingleton α] [i : Nonempty α] : size α = 1 := by
  rw [← size_prop]
  show (arrayOf α).size = 1
  if h : (arrayOf α).size < 2 then
    have : (arrayOf α).size ≠ 0 := by
      let a : α := Classical.choice i
      have := mem_arrayOf a
      grind
    omega
  else
    simp [Nat.lt_iff_add_one_le] at h
    let a := (arrayOf α)[0]
    let b := (arrayOf α)[1]
    simp_all [subsingleton_iff]
    have : (arrayOf α).Nodup := nodup
    simp [Array.Nodup, Array.pairwise_iff_getElem] at this
    replace : a ≠ b := by grind
    specialize ss a b
    contradiction
@[simp, grind =]
theorem size_unique {α : Type*} [Listed α] [i : Unique α] : size α = 1 := by
  apply size_subsingleton_nonempty

@[grind .]
theorem size_subsingleton {α : Type*} [Listed α] [i : Subsingleton α] : size α ≤ 1 := by
  if Nonempty α then grind else simp_all

@[simp, grind =]
theorem encodeFin_subsingleton {α : Type*} [Listed α] [Subsingleton α] (a : α) :
    encodeFin a = ⟨0, by have : Nonempty α := Nonempty.intro a; simp_all⟩ := by
  have : size α ≤ 1 := size_subsingleton; omega
@[simp, grind =]
theorem encode_subsingleton {α : Type*} [Listed α] [Subsingleton α] (a : α) :
    encode a = 0 := by
  have := encodeFin_subsingleton a
  simpa [encodeFin]

end Listed
