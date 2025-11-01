import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Vector.Basic

def printprint {α β : Type} [ToString β] (msg : β) (a : α) : α :=
  (unsafe unsafeIO (do
    println! msg
    let stdout ← IO.getStdout
    stdout.flush
    return a
  )).toOption.getD a

def timeitit {α β : Type} [Inhabited α] [ToString β] (msg : β) (a : IO α) : α :=
  (unsafe unsafeIO (do
    let a ← timeit (toString msg) a
    let stderr ← IO.getStderr
    stderr.flush
    return a
  )).toOption.get!

@[simp]
theorem printprint_id {α β : Type} [ToString β] (msg : β) (a : α) : printprint msg a = a := by
  sorry

namespace Array

variable {α β : Type}

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

def Pairwise (R : α → α → Prop) (l : Array α) : Prop := l.toList.Pairwise R

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

class Listed (α : Type) where
  array : Array α
  nodup : array.Nodup
  complete : ∀ a, a ∈ array
  encode : α → ℕ
  encode_len : ∀ a, encode a < array.size := by grind
  encode_prop : ∀ a, array[encode a]'(encode_len a) = a := by grind

namespace Listed

def ofArray {α : Type} [DecidableEq α]
    (array : Array α) (nodup : array.Nodup) (complete : ∀ a, a ∈ array) : Listed α where
  array
  nodup
  complete
  encode a := array.findIdx (· = a)

instance : Listed Unit where
  array := #[()]
  nodup := by simp [Array.Nodup, Array.Pairwise]
  complete := by simp
  encode _ := 0

variable {α β : Type}
variable [Listed α] [Listed β]

@[simp, grind] theorem mem_list (a : α) : a ∈ array := complete a

attribute [simp] Listed.nodup

def arrayOf (α : Type) [Listed α] : Array α := Listed.array
def listOf (α : Type) [Listed α] : List α := Listed.array.toList

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

def size (α : Type) [i : Listed α] : ℕ := i.array.size

def encodeFin {α : Type} [i : Listed α] : α → Fin i.size :=
  fun a ↦ ⟨i.encode a, by simp [size, encode_len]⟩
def decodeFin {α : Type} [i : Listed α] : Fin i.size → α :=
  fun a ↦ i.decode a |>.get (by obtain ⟨a, ha⟩ := a; grind [decode, size])

@[simp, grind]
theorem decodeFin_encodeFin {α : Type} [i : Listed α] (a) :
    i.encodeFin (i.decodeFin a) = a := by
  simp [encodeFin, decodeFin]

@[simp]
theorem encodeFin_decodeFin {α : Type} [i : Listed α] (a) :
    i.decodeFin (i.encodeFin a) = a := by
  grind [encodeFin, decodeFin, encode_decode]

def equivFin {α : Type} [Listed α] : α ≃ Fin (Listed.size α) := ⟨
  encodeFin,
  decodeFin,
  by intro; simp,
  by intro; simp⟩

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
    · simp [size]; have := encode_len b; omega
  encode_prop := by
    rintro (a | b)
    · simp; have := encode_len a; simp [this]; exact encode_prop a
    · simp [size]; exact encode_prop b

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
  nodup := Array.nodup_finRange n
  complete := Array.mem_finRange
  encode a := a.val
  encode_len := by simp
  encode_prop := by simp

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

def listVector [DecidableEq α] (n : ℕ) : Listed (List.Vector α n) :=
  match n with
  | 0 => {
      array := #[⟨[], by simp⟩],
      nodup := by simp [Array.Nodup, Array.Pairwise],
      complete := by rintro ⟨_, _⟩; grind [List.eq_nil_iff_length_eq_zero]
      encode _ := 0
      encode_len := by simp
      encode_prop a := by simp; ext ⟨_, _⟩; omega
  }
  | n+1 =>
    let L := (listVector n).array ×ˢ (arrayOf α) |>.map (fun ⟨l, a⟩ ↦ l.cons a)
    let complete := by
      simp [L, List.mem_map, Prod.exists, SProd.sprod, List.pair_mem_product, Array.mem_product, mem_list, true_and]
      clear L
      intro l
      rcases l with ⟨l, hl⟩
      rcases l with _ | ⟨a, l⟩
      · grind
      · use ⟨l, by simp_all⟩, a; grind [List.Vector.cons]
    {
      array := L
      nodup := by
        simp [L]
        clear complete
        refine (Array.nodup_map_iff_inj_on ?_).mpr ?_
        · letI := listVector n
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
    }

instance [DecidableEq α] (n : ℕ) : Listed (List.Vector α n) := Listed.listVector n

def arrayVector [DecidableEq α] (n : ℕ) : Listed (Vector α n) :=
  match n with
  | 0 => {
      array := #[⟨#[], by simp⟩],
      nodup := by simp [Array.Nodup, Array.Pairwise],
      complete := by rintro ⟨_, _⟩; grind [List.eq_nil_iff_length_eq_zero]
      encode _ := 0
      encode_len := by simp
      encode_prop a := by simp
  }
  | n+1 =>
    let L := (arrayVector n).array ×ˢ (arrayOf α) |>.map (fun ⟨l, a⟩ ↦ l.push a)
    let complete := by
      simp [L, List.mem_map, Prod.exists, SProd.sprod, List.pair_mem_product, Array.mem_product, mem_list, true_and]
      clear L
      intro l
      rcases l with ⟨l, hl⟩
      use ⟨l.take n, by simp_all⟩, l[n]
      simp
      omega
    {
      array := L
      nodup := by
        simp [L]
        clear complete
        refine (Array.nodup_map_iff_inj_on ?_).mpr ?_
        · letI := arrayVector n
          generalize h₁ : array (α:=Vector α n) = l₁
          generalize h₂ : (arrayOf α) = l₂
          replace h₁ : l₁.Nodup := by rw [← h₁]; exact nodup
          replace h₂ : l₂.Nodup := by rw [← h₂]; exact nodup
          show (l₁ ×ˢ l₂).Nodup
          exact Array.Nodup.product h₁ h₂
        · simp
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
    }

instance [DecidableEq α] (n : ℕ) : Listed (Vector α n) := Listed.arrayVector n

def pi_array [Inhabited β] [DecidableEq α] [DecidableEq β] : Array (α → β) :=
  -- printprint "pi_array time" <|
    arrayOf (Vector β (size α)) |>.map (fun m a ↦ m[encode a]'(by simp [size, encode_len]))

theorem mem_pi_array  [Inhabited β] [DecidableEq α] [DecidableEq β] {f : α → β} : f ∈ pi_array := by
  simp only [pi_array, printprint_id]
  apply Array.mem_map.mpr
  use Vector.ofFn (fun ⟨i, hi⟩ ↦ f <| (decode i).get (by simpa [decode, listOf]))
  grind [List.Vector.getElem_def, List.Vector.toList_ofFn]

def pi (α β : Type) [Listed α] [Listed β] [Inhabited β] [DecidableEq α] [DecidableEq β] : Listed (α → β) :=
  let array := pi_array
  {
    array
    nodup := by
      simp only [pi_array, printprint_id, array]
      refine (Array.nodup_map_iff_inj_on (by simp [arrayOf])).mpr ?_
      intro x hx y hy h
      refine Vector.ext fun i hi ↦ ?_
      have : (decode (α:=α) i).isSome = true := by simpa [decode, listOf]
      replace := congrFun h ((decode i).get this)
      simpa only [decode_get_encode]
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

end Listed
