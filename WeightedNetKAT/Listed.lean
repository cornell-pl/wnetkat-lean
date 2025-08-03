import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Vector.Basic

class Listed (α : Type) where
  list : List α
  nodup : list.Nodup
  complete : ∀ a, a ∈ list

namespace Listed

variable {α : Type} {β : Type}
variable [Listed α] [Listed β]

@[simp, grind] theorem mem_list (a : α) : a ∈ list := complete a

attribute [simp] Listed.nodup

def listOf (α : Type) [Listed α] : List α := Listed.list

@[simp, grind] theorem mem_listOf (a : α) : a ∈ listOf α := complete a

def encode [DecidableEq α] (a : α) : ℕ := list.findIdx (· = a)
def decode [DecidableEq α] (i : ℕ) : Option α := list[i]?

@[simp, grind]
theorem encode_decode [DecidableEq α] (a : α) : decode (encode a) = some a := by
  simp [encode, decode]
  obtain ⟨i, hi, ⟨_⟩⟩ := List.mem_iff_getElem.mp (complete a)
  refine (List.Nodup.getElem_inj_iff ?_).mpr ?_
  · simp
  · refine (List.findIdx_eq hi).mpr ?_
    simp_all
    intro j hj h
    have := Listed.nodup (α:=α)
    have := List.nodup_iff_injective_getElem.mp this
    simp [Function.Injective] at this
    have := this (a₁:=⟨i, by omega⟩) (a₂:=⟨j, by omega⟩)
    grind
theorem decode_eq_some [DecidableEq α] (n : ℕ) (a : α) : decode n = some a ↔ encode a = n := by
  simp [encode, decode]
  constructor
  · intro h
    refine (List.findIdx_eq ?_).mpr ?_
    · grind
    · simp_all
      constructor
      · grind
      · intro j hj hq
        have := h.trans (by grind : list[j]? = some a).symm
        have hq' := hq
        rw [List.getElem_eq_getElem?_get] at hq'
        simp [← this] at hq'
        have h := hq.trans hq'.symm
        have := nodup (α:=α)
        have : j = n := by exact (List.Nodup.getElem_inj_iff this).mp h
        omega
  · intro h
    subst_eqs
    simp
    have := List.findIdx_getElem (xs:=list (α:=α)) (p:=(fun x ↦ decide (x = a))) (w:=(by simp))
    simp at this
    grind

@[simp, grind]
theorem decode_get_encode [DecidableEq α] (n : ℕ) (h : (decode (α:=α) n).isSome) :
    encode ((decode n).get h) = n := by
  simp [encode, decode] at h ⊢
  refine (List.findIdx_eq ‹_›).mpr ?_
  simp
  intro j hj
  have : j ≠ n := by omega
  apply (List.Nodup.getElem_inj_iff (by simp)).not.mpr
  omega

def size (α : Type) [i : Listed α] : ℕ := i.list.length

def encodeFin {α : Type} [DecidableEq α] [i : Listed α] : α → Fin i.size :=
  fun a ↦ ⟨i.encode a, by simp [encode, size]⟩
def decodeFin {α : Type} [DecidableEq α] [i : Listed α] : Fin i.size → α :=
  fun a ↦ i.decode a |>.get (by obtain ⟨a, ha⟩ := a; grind [decode, size])

@[simp, grind]
theorem decodeFin_encodeFin {α : Type} [DecidableEq α] [i : Listed α] (a) :
    i.encodeFin (i.decodeFin a) = a := by
  simp [encodeFin, decodeFin]

@[simp]
theorem encodeFin_decodeFin {α : Type} [DecidableEq α] [i : Listed α] (a) :
    i.decodeFin (i.encodeFin a) = a := by
  grind [encodeFin, decodeFin, encode_decode]

def equivFin {α : Type} [DecidableEq α] [Listed α] : α ≃ Fin (Listed.size α) := ⟨
  encodeFin,
  decodeFin,
  by intro; simp,
  by intro; simp⟩

def fintype [DecidableEq α] : Fintype α := {
  elems := (listOf α).toFinset
  complete := by simp [listOf, complete]
}

@[simp] theorem list_toFinset [DecidableEq α] : (list (α:=α)).toFinset = @Finset.univ α fintype := rfl

instance : Listed (α × β) where
  list := list ×ˢ list
  nodup := List.Nodup.product nodup nodup
  complete := by intro ⟨a, b⟩; simp [complete]

instance : Listed (α ⊕ β) where
  list := list.map .inl ++ list.map .inr
  nodup := by
    refine List.nodup_append.mpr ?_
    split_ands
    · refine List.Nodup.map Sum.inl_injective nodup
    · refine List.Nodup.map Sum.inr_injective nodup
    · grind
  complete := by rintro (a | b) <;> simp_all

@[grind]
inductive T where | a | b | c | d
deriving DecidableEq, Repr, Inhabited

instance : Listed T where
  list := [.a, .b, .c, .d]
  nodup := by grind
  complete := by grind

instance {n : ℕ} : Listed (Fin n) where
  list := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

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

def decidableEqPi [Inhabited β] [DecidableEq α] [DecidableEq β] : DecidableEq (α → β) :=
  fun f g ↦
    if h : (listOf α).all fun a ↦ f a = g a then
      .isTrue (by grind)
    else
      .isFalse (by grind)

def listVector [DecidableEq α] (n : ℕ) : Listed (List.Vector α n) :=
  match n with
  | 0 => ⟨[⟨[], by simp⟩], (by simp), by rintro ⟨_, _⟩; grind [List.eq_nil_iff_length_eq_zero]⟩
  | n+1 =>
    {
      list := (listVector n).list.product (listOf α) |>.map (fun ⟨l, a⟩ ↦ l.cons a)
      nodup := by
        refine (List.nodup_map_iff_inj_on ?_).mpr ?_
        · letI := listVector n
          generalize h₁ : list (α:=List.Vector α n) = l₁
          generalize h₂ : (listOf α) = l₂
          replace h₁ : l₁.Nodup := by rw [← h₁]; exact nodup
          replace h₂ : l₂.Nodup := by rw [← h₂]; exact nodup
          show (l₁ ×ˢ l₂).Nodup
          induction l₁ with
          | nil => simp [List.nil_product]
          | cons a l₁ ih =>
            simp [List.product_cons]
            refine List.nodup_append.mpr ?_
            simp_all
            constructor
            · refine (List.nodup_map_iff_inj_on h₂).mpr ?_
              simp
            · rintro b hb l' b' hb' hb'₂ ⟨_⟩ ⟨_⟩
              simp_all
        · simp
          intro l a j b
          obtain ⟨l, hl⟩ := l
          obtain ⟨j, hj⟩ := j
          have := List.Vector.toList_cons (n:=n) (α:=α) a ⟨l, hl⟩
          grind [List.Vector.toList_cons, List.Vector.toList_mk]
      complete := by
        simp only [List.mem_map, Prod.exists, List.pair_mem_product, mem_list, true_and]
        intro l
        rcases l with ⟨l, hl⟩
        rcases l with _ | ⟨a, l⟩
        · grind
        · use ⟨l, by simp_all⟩, a; grind [List.Vector.cons]
    }

instance [DecidableEq α] (n : ℕ) : Listed (List.Vector α n) := Listed.listVector n

instance [Inhabited β] [DecidableEq α] [DecidableEq β] : Listed (α → β) where
  list :=
    listOf (List.Vector β (size α)) |>.map (fun m a ↦ m[encode a]'(by simp [size, encode]))
  nodup := by
    refine (List.nodup_map_iff_inj_on (by simp [listOf])).mpr ?_
    intro x hx y hy h
    ext ⟨i, hi⟩
    have : (decode (α:=α) i).isSome = true := by simpa [decode, listOf]
    replace := congrFun h ((decode i).get this)
    simpa only [decode_get_encode]
  complete := by
    intro f
    apply List.mem_map.mpr
    use List.Vector.ofFn (fun ⟨i, hi⟩ ↦ f <| (decode i).get (by simpa [decode, listOf]))
    grind [List.Vector.getElem_def, List.Vector.toList_ofFn]

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
#eval! listOf (T → Fin 2)

end Listed
