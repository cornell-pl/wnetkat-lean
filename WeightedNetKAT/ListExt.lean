module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.DropRight
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped RightActions

namespace List

namespace Notation

notation xs "[.." n "]" => take n xs
notation xs "[" n "..]" => drop n xs
notation "..=" n => Finset.range (n + 1)
notation "‖" xs "‖" => length xs

end Notation

section

variable {α : Type*} (l : List α)

def rep : ℕ → List α
  | 0 => []
  | n+1 => l ++ rep n

@[simp] theorem repeat_zero : l.rep 0 = [] := rfl
@[simp] theorem repeat_one : l.rep 1 = l := by simp [rep]
@[simp] theorem repeat_succ {n : ℕ} : l.rep (n + 1) = l ++ l.rep n := rfl

end

@[simp]
theorem take_length_succ {α : Type*} (A : List α) : take (A.length + 1) A = A := by
  simp only [take_eq_self_iff, le_add_iff_nonneg_right, zero_le]

end List


namespace List

variable {α β : Type*}

/-! # Products -/

@[simp, grind =]
theorem product_length {as : List α} {bs : List β} :
    (as.product bs).length = as.length * bs.length := by
  simp [product, map_const']

attribute [local grind =] pair_mem_product

def products : List (List α) → List (List α)
  | [] => [[]]
  | x::xs => (x.product xs.products).map (fun ⟨a, as⟩ ↦ a :: as)

variable {xs ys : List (List α)}

@[simp, grind =]
theorem products_nil : ([] : List (List α)).products = [[]] := by rfl
@[simp, grind =]
theorem products_length : xs.products.length = (xs.map length).prod := by
  fun_induction products with grind
@[simp, grind .]
theorem mem_products_length {x} (h : x ∈ xs.products) : x.length = xs.length := by
  fun_induction products generalizing x with grind

@[grind =, simp]
theorem products_eq_nil : xs.products = [] ↔ [] ∈ xs := by
  grind [eq_nil_iff_length_eq_zero, products_length, prod_eq_zero_iff, length_eq_zero_iff]

@[grind =]
theorem mem_products {x} :
    x ∈ xs.products ↔
      x.length = xs.length ∧ ∀ i, (h : i < x.length) → (h' : i < xs.length) → x[i]'h ∈ xs[i]'h'
:= by
  fun_induction products generalizing x with
  | case1 => simp
  | case2 y ys ih =>
    constructor
    · grind
    · simp only [length_cons, mem_map, Prod.exists]; intro h; have := h.right 0; grind [cases List]

theorem singleton_product {β : Type*} {l : List β} {a} :
    ([a] : List α).product l = l.map (⟨a, ·⟩) := by rw [product]; simp
theorem product_singleton {β : Type*} {l : List β} {a : α} :
    l.product [a] = l.map (⟨·, a⟩) := by rw [product]; simp [map_eq_flatMap]

theorem products_append :
    (xs ++ ys).products = (xs.products.product ys.products).map (fun ⟨x, y⟩ ↦ x ++ y) := by
  induction xs with
  | nil =>
    simp only [nil_append, products_nil, singleton_product, map_map]; unfold Function.comp; simp
  | cons x xs ih => simp [products, ih, product, map_flatMap, flatMap_map, flatMap_assoc]; rfl

end List

namespace List

/-! # Partitions -/

variable {α : Type*}  [DecidableEq α]


def partitions (xs : List α) : Finset (List (List α)) :=
  match xs with
  | [] => {[]}
  | x::xs =>
    (partitions xs).biUnion fun ys ↦
      match ys with
      | [] => {[[x]]}
      | y::ys => {(x::y)::ys, [x]::y::ys}

@[simp]
theorem partitions_nil : partitions ([] : List α) = {[]} := by rfl

theorem mem_partitions_iff {xs : List α} {ys} :
    ys ∈ partitions xs ↔ ys.flatten = xs ∧ ∀ y ∈ ys, y ≠ [] := by
  induction xs generalizing ys with
  | nil =>
    simp
    constructor
    · rintro ⟨_⟩; simp
    · simp
      intro h h'
      rcases ys with _ | ⟨y, ys⟩
      · rfl
      · simp_all; grind
  | cons x xs ih =>
    simp_all
    simp [partitions, ih]; clear ih
    constructor
    · simp
      rintro xs ⟨_⟩ h
      split
      · simp_all
      · simp_all
        rename_i xs l zs
        rintro (⟨_, _⟩ | ⟨_, _⟩)
        · simp_all
        · simp_all
    · simp
      intro h h'
      suffices ∃ a, (a.flatten = xs ∧ ∀ y ∈ a, ¬y = []) ∧
              match a with
              | [] => ys = [[x]]
              | z :: zs => ys = (x :: z) :: zs ∨ ys = [x] :: z :: zs by grind
      if ys = [[x]] then
        simp_all
        subst_eqs
        use []
        simp
      else
        simp_all
        rcases ys with _ | ⟨y, ys⟩
        · simp at h
        · simp_all
          rcases y with _ | ⟨a, y⟩
          · simp_all
          · simp_all
            obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
            rcases y with _ | ⟨b, y⟩
            · simp_all
              use ys
              simp_all
              grind
            · simp_all
              apply Exists.intro ((b::y) :: ys)
              simp_all

@[simp]
theorem nil_mem_partitions {xs : List α} : [] ∈ partitions xs ↔ xs = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all [partitions]
    intro l hl
    split
    · simp
    · simp

theorem partitions_cons_eq_split {α 𝒮 : Type*} [NonUnitalSemiring 𝒮] [DecidableEq α] {x} {xs : List α} {f : List (List α) → 𝒮} :
    ∑ ys ∈ partitions (x :: xs), f ys =
    ∑ i ∈ ..=‖xs‖, ∑ p ∈ partitions (xs[i..]), f ((x :: xs[..i]) :: p) := by
  induction xs generalizing x f with
  | nil => simp [partitions]
  | cons y xs ih =>
    rw [partitions]
    rw [Finset.sum_biUnion]
    · simp
      rw [Finset.sum_range_succ']
      simp
      simp [ih]
      simp [← Finset.sum_add_distrib]
    · intro A hA B hB h

      simp_all [mem_partitions_iff]
      intro S hSA hSB t ht
      simp_all
      replace hSA := hSA ht
      replace hSB := hSB ht
      split at hSA <;> split at hSB
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        cases hSA
        · subst_eqs
          simp_all
        · subst_eqs
          simp_all

@[grind =]
theorem mem_products' {α : Type*} {x} {xs : List (List α)} [Inhabited α] :
    x ∈ xs.products ↔
      x.length = xs.length ∧ ∀ i < ‖xs‖, x[i]! ∈ xs[i]!
:= by
  simp_all [mem_products]

def partitions' (xs : List α) (n : ℕ) : Finset (List (ℕ × List α)) :=
  match xs with
  | [] => {[]}
  | x::xs =>
    (partitions' xs n).biUnion fun ys ↦
      match ys with
      | [] => (Finset.range (n + 1)).image fun i ↦ [(i, [x])]
      | (i, y)::ys => insert ((i, x::y)::ys) ((Finset.range (n + 1)).image fun j ↦ (j, [x])::(i, y)::ys)

@[simp]
theorem partitions'_nil {n} : partitions' ([] : List α) n = {[]} := by rfl

theorem partitions_eq_partitions' {xs : List α} {n} :
    partitions xs = (partitions' xs n).image fun l ↦ l.map Prod.snd := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [partitions, partitions']
    simp [ih]
    ext l
    simp
    constructor
    · simp
      rintro (_ | ⟨y, ys⟩) h h'
      · simp_all
        subst_eqs
        use 0, [], h
        simp
      · simp at h'
        rcases h' with ⟨_, _⟩ | ⟨_, _⟩
        · use (⟨y.1, x :: y.2⟩ :: ys)
          simp
          use y::ys
          simp [h]
        · use (⟨0, [x]⟩ :: y :: ys)
          constructor
          · use y :: ys
            simp [h]
          · simp
    · simp
      intro as bs hbs has
      rcases bs with _ | ⟨b, bs⟩
      · simp_all
        obtain ⟨i, hi, _, _⟩ := has
        simp
        rintro ⟨_⟩
        use []
        simp_all
      · simp_all
        rintro ⟨_⟩
        use b::bs
        simp [hbs]
        grind

theorem mem_partitions'_iff {xs : List α} {n : ℕ} {ys}  :
    ys ∈ partitions' xs n ↔ (ys.map Prod.snd).flatten = xs ∧ ∀ a b, (a, b) ∈ ys → a ≤ n ∧ ¬b = [] := by
  induction xs generalizing ys with
  | nil =>
    simp
    constructor
    · rintro ⟨_⟩; simp
    · simp only [and_imp]
      intro h h'
      rcases ys with _ | ⟨⟨i, y⟩, ys⟩
      · simp
      · simp_all
        specialize h' i y
        specialize h y i
        simp_all
  | cons x xs ih =>
    simp only [partitions', Finset.mem_biUnion, ih]
    constructor
    · simp
      rintro ls ⟨_⟩ h h'
      rcases ls with _ | ⟨l, ls⟩
      · simp_all only [map_nil, flatten_nil, partitions'_nil, Finset.mem_singleton,
        flatten_eq_nil_iff, mem_map, Prod.exists, exists_eq_right, forall_exists_index,
        not_mem_nil, IsEmpty.forall_iff, implies_true, Finset.mem_image, Finset.mem_range]
        obtain ⟨i, hi, ⟨_⟩⟩ := h'
        simp
        omega
      · simp_all
        rcases h' with ⟨⟨_⟩⟩ | ⟨i, hi, _, _⟩
        · simp
          grind
        · simp
          grind
    · simp
      have h₀ (xs : List α) n := partitions_eq_partitions' (xs:=xs) (n:=n)
      simp [Finset.ext_iff] at h₀
      replace h₀ xs n := (h₀ xs n (ys.map Prod.snd)).mp
      simp [mem_partitions_iff] at h₀
      intro h h'
      rcases ys with _ | ⟨⟨i, y⟩, ys⟩
      · simp_all only [map_nil, flatten_nil, nil_eq, not_mem_nil, IsEmpty.forall_iff, implies_true,
        partitions'_nil, Finset.mem_singleton, map_eq_nil_iff, and_self, exists_eq, reduceCtorEq]
      · simp_all
        rcases y with _ | ⟨a, as⟩
        · simp_all only [nil_append]
          rcases ys with _ | ⟨⟨j, y⟩, ys⟩
          · simp_all
          · simp_all
            absurd h'; clear h'
            simp
            use i, []
            simp
        · simp_all only [cons_append, cons.injEq]
          specialize h₀ (x :: xs) n rfl (by grind)
          obtain ⟨p, hp, hp'⟩ := h₀
          simp [partitions'] at hp
          obtain ⟨q, hq, hq'⟩ := hp
          rcases q with _ | ⟨⟨q₀, q₀'⟩, q⟩
          · simp_all only [map_nil, flatten_nil, nil_eq, not_mem_nil,
            IsEmpty.forall_iff, implies_true, and_true, Finset.mem_image, Finset.mem_range,
            flatten_eq_nil_iff, mem_map, Prod.exists, exists_eq_right,
            forall_exists_index, partitions'_nil, Finset.mem_singleton, append_eq_nil_iff]
            subst_eqs
            obtain ⟨j, hj, _, _⟩ := hq'
            simp_all
            use ys
            constructor
            · grind
            · rcases ys with _ | ⟨y, ys⟩
              · simp_all; omega
              · simp
                specialize h' i [x]
                simp at h'
                omega
          · simp_all only [map_cons, flatten_cons, mem_cons, Prod.mk.injEq,
            Finset.mem_insert, Finset.mem_image, Finset.mem_range]
            rcases hq' with ⟨_, _⟩ | ⟨j, hj, _, _⟩
            · simp_all
              rcases hp' with ⟨⟨_⟩, hp'⟩
              rcases h with ⟨⟨_⟩, ⟨_⟩⟩
              use ⟨i, as⟩::ys
              simp
              rintro k l (⟨⟨_⟩, ⟨_⟩⟩ | h)
              · specialize hq q₀ as
                simp at hq
                specialize h' i (x :: as)
                simp at h'
                grind
              · specialize h' k l
                simp [h] at h'
                exact h'
            · simp_all
              use ys
              simp_all
              constructor
              · grind
              · rcases ys with _ | ⟨y, ys⟩
                · simp_all
                · simp
                  specialize h' i [x]
                  simp at h'
                  omega


def partitionsFill' (xs : List α) (n : ℕ) :=
  ((partitions' xs n).image fun x ↦ x.flatMap fun ⟨i, l⟩ ↦ (replicate i [] ++ [l])).biUnion (fun q ↦ (Finset.range (n + 1)).map ⟨(q ++ replicate · []), by intro; simp⟩)

def buckets (xs : List α) (n : ℕ) : Finset (List (List α)) :=
  match n with
  | 0 => {}
  | n+1 =>
    match xs with
    | [] => {replicate (n+1) []}
    | x::xs =>
      (buckets (x::xs) n).map ⟨([] :: ·), cons_injective⟩ ∪
      (buckets xs (n+1)).image fun bs ↦
        match bs with
        | [] => [] -- NOTE: this case is unreachable
        | b::bs => (x::b)::bs

@[simp]
theorem buckets_nil {n} :
    buckets ([] : List α) n = if n = 0 then {} else {replicate n []} := by
  induction n with
  | zero => simp [buckets]
  | succ n ih => simp [buckets]
@[simp]
theorem buckets_zero (xs : List α) :
    buckets xs 0 = {} := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [buckets]
@[simp]
theorem buckets_one (xs : List α) :
    buckets xs 1 = {[xs]} := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all [buckets]
theorem mem_buckets_iff (xs : List α) (n : ℕ) {ys} :
    ys ∈ buckets xs n ↔ n ≠ 0 ∧ ys.flatten = xs ∧ ‖ys‖ = n := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
    induction xs generalizing ys n with
    | nil => simp [eq_replicate_iff]; grind
    | cons x xs ih' =>
      simp
      simp [buckets]
      simp_all
      clear ih ih'
      constructor
      · grind
      · simp
        rcases ys with _ | ⟨y, ys⟩
        · simp_all
        · simp_all
          rcases y with _ | ⟨a, y⟩
          · simp_all; grind
          · simp_all
            rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
            use y :: ys
            simp

theorem sum_le {α : Type*} (xs : List α) (f : α → ℕ) (cap : ℕ) (h : ∀ x ∈ xs, f x ≤ cap) : (xs.map f).sum ≤ cap * ‖xs‖ := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all
    grw [ih]
    grind

theorem le_sum {α : Type*} (xs : List α) (f : α → ℕ) (cap : ℕ) (h : ∀ x ∈ xs, cap ≤ f x) : ‖xs‖ * cap ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp_all
    grw [← ih]
    grind

def count' (n m : ℕ) : ℕ := (n + 1) * (m + 1)

@[gcongr]
theorem count'_le {n n' m m'} (hn : n ≤ n') (hm : m ≤ m') : count' n m ≤ count' n' m' := by
  simp [count']
  grw [hn, hm]

theorem partitionsFill'_subset_buckets (xs : List α) (n : ℕ) (h : xs ≠ []) :
    partitionsFill' xs n ⊆ (Finset.range (count' ‖xs‖ n)).biUnion (buckets xs) := by
  intro l
  simp [mem_buckets_iff, partitionsFill']
  simp [mem_partitions'_iff]
  rintro xs ⟨_⟩ h' i hi ⟨_⟩
  simp_all only [length_append, length_flatMap, length_replicate, length_cons,
    length_nil, zero_add, sum_map_add, map_const', sum_replicate, smul_eq_mul,
    mul_one, append_eq_nil_iff, flatMap_eq_nil_iff, replicate_eq_nil_iff,
    cons_ne_self, and_false, imp_false, Prod.forall, not_and, flatten_append,
    flatten_replicate_nil, append_nil]
  induction xs generalizing n i with
  | nil => simp_all
  | cons x xs ih =>
    obtain ⟨a, bs⟩ := x
    simp_all
    have : (flatMap (fun x ↦ replicate x.1 [] ++ [x.2]) xs).flatten = (map Prod.snd xs).flatten := by
      clear a h h' hi ih bs
      induction xs with simp_all
    simp [this]; clear this
    have : ((∀ (a_1 : ℕ) (b : List α), (a_1 = a → ¬b = bs) ∧ (a_1, b) ∉ xs) → ¬i = 0) := by
      rintro h ⟨_⟩
      specialize h a bs
      simp at h
    simp_all only [not_false_eq_true, implies_true, and_self, and_true, gt_iff_lt]
    have := h' a bs
    simp at this
    rcases xs with _ | ⟨⟨a', bs'⟩, xs⟩
    · simp_all
      simp [count']
      rcases n with _ | n
      · simp_all
        grind [length_pos_iff]
      · rcases bs with _ | _
        · simp_all
        · simp_all
          ring_nf
          omega
    · simp_all only [mem_cons, Prod.mk.injEq, map_cons, sum_cons, length_cons,
      Function.comp_apply, not_or, not_and, flatMap_cons, append_assoc, cons_append,
      nil_append, flatten_append, flatten_replicate_nil, flatten_cons,
      append_cancel_left_eq, not_isEmpty_of_nonempty, IsEmpty.exists_iff, true_and,
      implies_true, gt_iff_lt]
      specialize ih n bs' a'
      simp at ih
      rcases bs' with _ | _
      · simp_all
        have := h' a' []
        simp at this
      · simp_all
        specialize ih (by grind) i (by omega)
        ring_nf at ih
        replace ih := ih.left
        simp [Nat.lt_iff_add_one_le] at ih
        ring_nf
        ring_nf at ih
        have : 2 + a + a' + (map Prod.fst xs).sum + ‖xs‖ + i = a + (2 + a' + (map Prod.fst xs).sum + ‖xs‖ + i) := by omega
        rw [this]; clear this
        grw [ih]
        have : 1 ≤ ‖bs‖ := by grind [length_pos_iff]
        grw [← this]
        ring_nf
        set m := (map (length ∘ Prod.snd) xs).sum
        simp [count']
        ring_nf
        rename_i h _ _
        grw [h.left]
        ring_nf
        simp


def corep {α : Type*} (xs : List (List α)) : List (ℕ × List α) :=
  match xs with
  | [] => []
  | []::xs =>
    match corep xs with
    | [] => []
    | (n, y) :: ys => (n + 1, y) :: ys
  | x::xs => (0, x) :: (corep xs)

@[simp]
theorem corep_nil {α : Type*} : corep ([] : List (List α)) = [] := by simp [corep]

@[simp]
theorem corep_mem_ne_nil {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    ls ≠ [] := by rintro ⟨_⟩; simp [corep] at h

@[simp]
theorem corep_mem_ne_nil' {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    x.2 ≠ [] := by
  induction ls generalizing x with
  | nil => simp_all
  | cons l ls ih =>
    simp_all
    rcases l with _ | ⟨i, l⟩
    · simp_all [corep]
      split at h
      · simp_all
      · grind
    · simp_all [corep]
      grind

@[simp]
theorem corep_mem_lt {α : Type*} {ls : List (List α)} {x} (h : x ∈ corep ls) :
    x.1 < ‖ls‖ := by
  induction ls generalizing x with
  | nil => simp_all
  | cons l ls ih =>
    simp_all
    rcases l with _ | ⟨i, l⟩
    · simp_all [corep]
      split at h
      · simp_all
      · grind
    · simp_all [corep]
      grind

@[simp]
theorem corep_flatten {α : Type*} {ls : List (List α)} :
    (map Prod.snd (corep ls)).flatten = ls.flatten := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    rcases l with _ | ⟨a, l⟩
    · simp_all [corep]
      split
      · simp_all; assumption
      · simp_all
    · simp_all [corep]

@[simp]
theorem corep_replicate_nil {α : Type*} {i} :
    corep (replicate i ([] : List α)) = [] := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [corep, replicate]
    split
    · rfl
    · simp_all

@[simp]
theorem corep_append_replicate_nil {α : Type*} {ls : List (List α)} {i} :
    corep (ls ++ replicate i []) = corep ls := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    simp_all
    rcases l with _ | _
    · simp_all [corep]
    · simp_all [corep]

theorem corep_reconstruct {α : Type*} {ls : List (List α)} :
    flatMap (fun x ↦ replicate x.1 [] ++ [x.2]) (corep ls) ++ rtakeWhile (·.length = 0) ls = ls := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    rcases l with _ | ⟨a, l⟩
    · simp [corep]
      split
      · simp_all; exact ih
      · simp_all
        rename_i ys i ys' l h
        simp [replicate]
        suffices rtakeWhile (fun x ↦ decide (x = [])) ([] :: ls) = rtakeWhile (fun x ↦ decide (x = [])) ls by
          simp [this, ih]
        clear ih
        induction ls using reverseRecOn with
        | nil => simp_all
        | append_singleton ls l' ih =>
          rcases l' with _ | _
          · simp_all
            rw [← cons_append]
            rw [rtakeWhile_concat]
            simp
            apply ih
            have := corep_append_replicate_nil (ls:=ls) (i:=1)
            simp at this
            grind
          · simp_all
    · simp_all [corep]
      nth_rw 3 [← ih]; clear ih
      simp
      induction ls using reverseRecOn with
      | nil => simp
      | append_singleton ls l' ih =>
        rw [← cons_append]
        repeat rw [rtakeWhile_concat]
        simp_all

theorem exists_nil_tail {α : Type*} (xs : List (List α)) :
    ∃ ys, (∃ x, ys ++ replicate x [] = xs) ∧ ∀ (h : ¬ys = []), ¬ys.getLast h = [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨ys, ⟨n, _, _⟩, ih⟩ := ih
    rcases x with _ | ⟨a, x⟩
    · rcases ys with _ | ⟨y, ys⟩
      · simp_all
        use []
        simp
        use n + 1
        simp [replicate]
      · simp_all
        use []::y::ys
        constructor
        · use n
          simp
        · simp_all
    · use (a::x)::ys
      simp_all
      rcases ys
      · simp_all
      · simp_all

theorem buckets_subset_partitionsFill' (xs : List α) (n : ℕ) (h : xs ≠ []) :
    (Finset.range n).biUnion (buckets xs) ⊆ partitionsFill' xs (count' ‖xs‖ n) := by
  intro ls
  simp [mem_buckets_iff, partitionsFill']
  simp [mem_partitions'_iff]
  rintro h₁ h₂ ⟨_⟩
  simp_all
  obtain ⟨xs, hxs, hxs'⟩ := h
  use corep ls
  simp_all [Nat.lt_iff_add_one_le]
  constructor
  · intro i as h
    have : as ≠ [] := by have := corep_mem_ne_nil' h; grind
    simp [this]
    have := corep_mem_lt h
    simp at this
    grw [this, ← h₁]
    simp [count', mul_add, add_mul]
    omega
  · obtain ⟨ls, ⟨i, _, _⟩, h⟩ := exists_nil_tail ls
    simp_all
    use i
    simp
    have := corep_reconstruct (ls:=ls)
    constructor
    · grw [← h₁]
      simp [count']
      simp [mul_add, add_mul]
      ring_nf
      omega
    · nth_rw 2 [← this]
      simp
      apply h

theorem sum_partitions'_cons {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {x : ι} {xs : List ι} {n} {f : List (ℕ × List ι) → 𝒮'} :
      ∑ ys ∈ List.partitions' (x :: xs) n, f ys
    = if xs = [] then ∑ i ∈ ..=n, f [(i, [x])] else ∑ ys ∈ xs.partitions' n, (f ((ys.head!.1, x :: ys.head!.2) :: ys.tail) + ∑ i ∈ Finset.image (fun j ↦ (j, [x]) :: ys) (..=n), f i) := by
  split_ifs
  · subst_eqs
    simp [List.partitions']
  simp [List.partitions']
  rw [Finset.sum_biUnion]
  · have :
        ∑ ys ∈ xs.partitions' n,
          ∑
            i ∈
              match ys with
              | [] => Finset.image (fun i ↦ [(i, [x])]) (..=n)
              | (i, y) :: ys => insert ((i, x :: y) :: ys) (Finset.image (fun j ↦ (j, [x]) :: (i, y) :: ys) (..=n)),
            f i
      = ∑ ys ∈ xs.partitions' n,
          (f ((ys.head!.1, x :: ys.head!.2) :: ys.tail) + ∑ i ∈ (Finset.image (fun j ↦ (j, [x]) :: ys) (..=n)), f i) := by
      congr!
      split
      · simp_all [List.mem_partitions'_iff]
      · simp_all [List.mem_partitions'_iff]
    convert this
    simp
  · intro as has bs hbs h S h₁ h₂ Z hZ
    simp_all only [SetLike.mem_coe, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty,
      Finset.notMem_empty]
    specialize h₁ hZ
    specialize h₂ hZ
    simp_all [List.mem_partitions'_iff]
    rcases as with _ | ⟨⟨a, a'⟩, as⟩ <;> rcases bs with _ | ⟨⟨b, b'⟩, bs⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
      grind

theorem sum_partitionsFill' {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {xs : List ι} {n} {f : List (List ι) → 𝒮'} :
    ∑ ys ∈ List.partitionsFill' xs n, f ys = ∑ x ∈ xs.partitions' n, ∑ x_1 ∈ ..=n, f (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) x ++ List.replicate x_1 []) := by
  simp [List.partitionsFill']
  rw [Finset.sum_biUnion, Finset.sum_image]
  · simp
  · intro as has bs hbs h
    simp_all [List.mem_partitions'_iff]
    obtain ⟨⟨_⟩, has⟩ := has
    obtain ⟨h', hbs⟩ := hbs
    induction as generalizing bs with
    | nil => simp_all; rcases bs with _ | _ <;> simp_all; grind
    | cons a as ih =>
      obtain ⟨a, a'⟩ := a
      simp_all
      rcases bs with _ | ⟨⟨b, b'⟩, bs⟩
      · simp_all
      · simp_all
        suffices a = b by
          simp_all
          specialize @ih bs (by simp_all) (by grind)
          apply ih <;> clear ih
          · simp_all
          · grind
        rcases a' with _ | ⟨a₀, a'⟩
        · simp_all; grind
        rcases b' with _ | ⟨b₀, b'⟩
        · simp_all; grind
        simp_all
        set ts := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) as
        set ss := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) bs
        clear ih has hbs h'
        induction a generalizing b with
        | zero => simp at h; rcases b with _ | _ <;> simp_all [List.replicate]
        | succ a ih => rcases b with _ | _ <;> simp_all [List.replicate]
  · simp
    intro as has bs hbs h S h₁ h₂ Z hZ
    simp_all only [Set.mem_image, SetLike.mem_coe, ne_eq, Finset.le_eq_subset, Finset.bot_eq_empty,
      Finset.notMem_empty]
    simp_all [List.mem_partitions'_iff]
    specialize h₁ hZ
    specialize h₂ hZ
    simp_all
    obtain ⟨i, h₁, ⟨_⟩⟩ := h₁
    obtain ⟨j, h₂, h'⟩ := h₂
    obtain ⟨as, ⟨⟨_⟩, has⟩, _, ⟨_⟩⟩ := has
    obtain ⟨bs, ⟨h'', hbs⟩, _, ⟨_⟩⟩ := hbs
    clear hZ S
    contrapose! h
    simp_all
    suffices i = j by subst_eqs; simp_all only [List.append_cancel_right_eq]
    clear h''
    induction as using List.reverseRecOn with
    | nil =>
      simp at h'
      induction bs using List.reverseRecOn with
      | nil => simp at h'; omega
      | append_singleton bs b ih =>
        obtain ⟨b, b'⟩ := b
        clear ih
        simp at h'
        simp [← List.append_assoc] at h'
        simp [List.eq_replicate_iff] at h'
        obtain ⟨h₁, h₂⟩ := h'
        subst_eqs
        specialize h₂ b'
        simp at h₂
        subst_eqs
        simp at hbs
        grind
    | append_singleton as a ih =>
      obtain ⟨a, a'⟩ := a
      clear ih
      induction bs using List.reverseRecOn with
      | nil =>
        symm at h'
        simp [List.eq_replicate_iff] at h'
        obtain ⟨h₁, h₂⟩ := h'
        specialize h₂ a'
        simp at h₂
        subst_eqs
        simp at hbs
        grind
      | append_singleton bs b ih =>
        obtain ⟨b, b'⟩ := b
        clear ih
        simp at h'
        simp at has hbs
        rcases a' with _ | ⟨a₀, a'⟩
        · grind
        rcases b' with _ | ⟨b₀, b'⟩
        · grind
        simp [← List.append_assoc] at h'
        set ts := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) bs ++ List.replicate b []
        set ss := List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) as ++ List.replicate a []
        clear hbs has
        induction i generalizing j with
        | zero =>
          simp at h'; rcases j with _ | _
          · rfl
          · simp [List.replicate_add] at h'
            rw [List.append_cons, List.append_cons] at h'
            simp only [List.append_nil, ← List.append_assoc, List.append_singleton_inj, List.nil_eq,
              reduceCtorEq, and_false] at h'
        | succ i ih =>
          rcases j with _ | j
          · simp [List.replicate_add] at h'
            nth_rw 2 [List.append_cons, List.append_cons] at h'
            simp [← List.append_assoc] at h'
          · simp [List.replicate_add] at h'
            conv at h' => left; rw [List.append_cons, ← List.append_assoc, ← List.append_cons]
            conv at h' => right; rw [List.append_cons, ← List.append_assoc, ← List.append_cons]
            simp
            exact ih (by omega) j (by omega) (List.append_cancel_right h')

theorem sum_partitionsFill'_cons {𝒮' : Type*} [NonUnitalSemiring 𝒮'] {ι : Type*} [DecidableEq ι] {x : ι} {xs : List ι} {n} {f : List (List ι) → 𝒮'} (h : xs ≠ []) (hf : ∀ a b, f (a ++ b) = f a * f b) :
      ∑ ys ∈ List.partitionsFill' (x :: xs) n, f ys
    = ((∑ i ∈ xs.partitions' n,
      f (List.replicate i.head!.1 []) * f [x :: i.head!.2] *
        f (List.flatMap (fun x ↦ List.replicate x.1 [] ++ [x.2]) i.tail)) *
    ∑ i ∈ ..=n, f (List.replicate i [])) + ∑ i ∈ ..=n, ∑ ys ∈ List.partitionsFill' xs n, f (List.replicate i [] ++ [x] :: ys) := by
  simp [sum_partitionsFill']
  nth_rw 2 [Finset.sum_comm]
  simp [sum_partitions'_cons]
  simp [Finset.sum_add_distrib, h]
  congr! 1
  have hf' {a b} : f (a :: b) = f [a] * f b := by
    rw [← List.singleton_append, hf]
  simp [hf]
  conv => enter [1, 2, _, 2, _]; rw [hf']
  simp [hf]
  simp [← Finset.mul_sum]
  simp [← Finset.sum_mul, ← mul_assoc]

theorem mul_prod_mul_eq {α ι : Type*} [Semiring α] {xs : List ι} {a : α} {f : ι → α} :
    a * (xs.map (f · * a)).prod = (xs.map (a * f ·)).prod * a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [mul_assoc]

@[simp]
theorem buckets_pairwise_disjoint {α : Type*} [DecidableEq α] {xs : List α} {S : Set ℕ} :
    S.PairwiseDisjoint xs.buckets := by
  intro i hi j hj h A h₁ h₂ ls hls
  simp_all
  specialize h₁ hls
  specialize h₂ hls
  simp_all [mem_buckets_iff]

@[simp]
theorem buckets_succ_pairwise_disjoint {α : Type*} [DecidableEq α] {xs : List α} {S : Set ℕ} :
    S.PairwiseDisjoint (xs.buckets ·.succ) := by
  intro i hi j hj h A h₁ h₂ ls hls
  simp_all
  specialize h₁ hls
  specialize h₂ hls
  simp_all [mem_buckets_iff]

end List
