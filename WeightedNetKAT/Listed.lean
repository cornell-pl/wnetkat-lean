module

public import Batteries.Data.Array.Pairwise
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.DropRight
public meta import Mathlib.Data.List.Defs

@[expose] public section

namespace List

variable {α β : Type*}

def getElem_prod (l₁ : List α) (l₂ : List β) (i) (hi : i < (l₁ ×ˢ l₂).length) :
    (l₁ ×ˢ l₂)[i] = (
      l₁[i / l₂.length]'(by simp [length_product] at hi; refine (Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)).mpr hi),
      l₂[i % l₂.length]'(by simp [length_product] at hi; refine Nat.mod_lt i (Nat.pos_of_lt_mul_left hi))) := by
  induction l₁ generalizing i with
  | nil => simp at hi
  | cons a l₁ ih =>
    simp at hi
    simp_all [getElem_append, getElem_cons]
    if h : i < l₂.length then
      simp_all [Nat.mod_eq_of_lt]
    else
      simp [h]
      if l₂ = [] then
        subst_eqs
        simp_all
      else
        simp_all
        split_ands
        · congr
          refine Nat.div_eq_of_lt_le ?_ ?_
          · simp [Nat.sub_mul]
            have : i - l₂.length + l₂.length = i := by omega
            rw [this]
            exact Nat.div_mul_le_self i l₂.length
          · simp [Nat.sub_mul, Nat.add_mul]
            have : i / l₂.length * l₂.length - l₂.length + l₂.length = i / l₂.length * l₂.length := by
              refine Nat.sub_add_cancel ?_
              simp_all
              refine Nat.le_mul_of_pos_left l₂.length ?_
              simp_all
              (expose_names; exact length_pos_iff.mpr h_1)
            rw [this]
            refine Nat.lt_div_mul_self ?_ ?_
            · simp_all
              (expose_names; exact length_pos_iff.mpr h_1)
            · simp_all
        · congr! 1
          refine Eq.symm (Nat.mod_eq_sub_mod ?_)
          simp_all

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

@[simp]
def size_product {l₁ : Array α} {l₂ : Array β} : (l₁ ×ˢ l₂).size = l₁.size * l₂.size := by
  convert List.length_product (l₁:=l₁.toList) (l₂:=l₂.toList)
  simp [← product_eq_toList_product]
@[simp]
def getElem_product {l₁ : Array α} {l₂ : Array β} {i} (hi : i < (l₁ ×ˢ l₂).size) :
    (l₁ ×ˢ l₂)[i] = (
      l₁[i / l₂.size]'(by simp [size_product] at hi; refine (Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)).mpr hi),
      l₂[i % l₂.size]'(by simp [size_product] at hi; refine Nat.mod_lt i (Nat.pos_of_lt_mul_left hi))) := by
  convert List.getElem_prod (l₁:=l₁.toList) (l₂:=l₂.toList) i (by simp_all [List.length_product])
  simp [← product_eq_toList_product]

def Nodup (l : Array α) : Prop := l.Pairwise (· ≠ ·)

@[simp, grind .]
theorem nodup_empty : Nodup (#[] : Array α) := by simp [Nodup, Pairwise]
@[simp, grind .]
theorem nodup_singleton {a} : Nodup (#[a] : Array α) := by simp [Nodup, Pairwise]
@[simp, grind .]
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
  simpa only [mem_toList_iff, ne_eq]

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
  simpa only [mem_toList_iff]

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

theorem encode_lt_size (a : α) : encode a < size α := by
  convert encode_len a
  exact size_prop.symm

def encode_inj : Function.Injective (Listed.encode (α:=α)) := by
  intro a b h; have := encode_prop a; have := encode_prop b; grind [encode_prop]

instance : Countable α := ⟨⟨Listed.encode, Listed.encode_inj⟩⟩

@[implicit_reducible]
def lift [Listed α] {γ : Type*} (f : α ≃ γ) : Listed γ where
  array := (array : Array α).map f
  size := size α
  size_prop := by simp [size_prop]
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

@[simp, grind .] theorem mem_list (a : α) : a ∈ array := complete a

attribute [simp] Listed.nodup

def arrayOf (α : Type*) [Listed α] : Array α := Listed.array
def listOf (α : Type*) [Listed α] : List α := Listed.array.toList

@[simp, grind .] theorem mem_arrayOf (a : α) : a ∈ arrayOf α := complete a
@[simp, grind .] theorem mem_listOf (a : α) : a ∈ listOf α := by simp [listOf]

@[specialize, inline]
def decode (i : ℕ) : Option α := array[i]?

@[simp, grind =]
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

@[simp, grind =]
theorem decode_get_encode (n : ℕ) (h : (decode (α:=α) n).isSome) :
    encode ((decode n).get h) = n := by
  simp [decode] at h ⊢
  have h₁ : n < (array : Array α).size := by contrapose! h; simp_all
  have h₃ := encode_prop array[n]
  have := nodup (α:=α)
  have := List.Nodup.getElem_inj_iff (nodup (α:=α)) (i:=n) (j:=encode array[n]) (hi:=h) (hj:=by simp [encode_len])
  grind

@[specialize, inline]
def encodeFin {α : Type*} [i : Listed α] : α → Fin i.size :=
  fun a ↦ ⟨i.encode a, by simp [encode_len, ← size_prop]⟩
@[specialize, inline]
def decodeFin {α : Type*} [i : Listed α] : Fin i.size → α :=
  fun a ↦ i.decode a |>.get (by obtain ⟨a, ha⟩ := a; grind [decode, size_prop])

@[simp, grind =]
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

@[implicit_reducible]
def decidableEq : DecidableEq α := fun a b ↦
  if h : encode a = encode b then .isTrue (by simp_all) else .isFalse (by simp_all)

@[implicit_reducible]
def fintype : Fintype α :=
  letI : DecidableEq α := Listed.decidableEq
  {
    elems := (listOf α).toFinset
    complete := by simp [listOf, complete]
  }

@[simp] theorem array_toFinset [DecidableEq α] :
    (array (α:=α)).toList.toFinset = @Finset.univ α fintype := by
  ext; simp

instance : Listed (α × β) := {
    array := array ×ˢ array
    size := Listed.size α * Listed.size β
    size_prop := by simp [Array.size_product, size_prop]
    nodup := Array.Nodup.product nodup nodup
    complete := by intro ⟨a, b⟩; simp [complete]
    encode := fun (a, b) ↦ encode a * size β + encode b
    encode_len := by
      simp [Prod.forall, size_prop]
      intro a b
      have ha := encode_lt_size a
      have hb := encode_lt_size b
      simp_all only [gt_iff_lt]
      simp only [Nat.lt_iff_add_one_le] at *
      rw [add_assoc]
      grw [hb]
      grw [← ha]
      rw [← Nat.succ_mul]
    encode_prop := by
      simp [size_prop]
      intro a b
      have hsβ : size β ≠ 0 := Nat.ne_zero_of_lt (encode_lt_size b)
      have : (encode a * size β + encode b) / size β = encode a := by
        have : ¬size β ≤ encode b % size β := by simp; exact Nat.mod_lt_of_lt (encode_lt_size b)
        simp [Nat.add_div (Nat.zero_lt_of_ne_zero hsβ), this, hsβ, encode_lt_size b]
      have : encode b % size β = encode b := Nat.mod_eq_of_lt (encode_lt_size b)
      simp_all [encode_prop]
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

@[implicit_reducible]
def ofEquiv {α β : Type*} [i : Listed α] (e : α ≃ β) : Listed β where
  array := (arrayOf α).map e
  size := i.size
  size_prop := by simp; apply size_prop
  nodup := Array.Nodup.map e.injective Listed.nodup
  complete := by simp; exact (⟨e.symm ·, e.apply_symm_apply _⟩)
  encode := Listed.encode ∘ e.symm
  encode_len b := by simp; apply encode_len
  encode_prop b := by
    simp
    have := congrArg e (i.encode_prop (e.symm b))
    simpa

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
    {f : Fin (size α) → 𝒮} :
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
