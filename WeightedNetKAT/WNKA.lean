import WeightedNetKAT.Language

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [DecidableEq F]
variable {N : Type} [Fintype N] [DecidableEq N]
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] -- [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

class WeightedProduct (α : Type) (β : Type) (γ : outParam Type) where
  wProd : α → β → γ

infixl:70 " ⨯ " => WeightedProduct.wProd

instance {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮] :
    WeightedProduct (𝒞 𝒮 (X × Y)) (𝒞 𝒮 (Y × Z)) (𝒞 𝒮 (X × Z)) where
  wProd m m' := 𝒞.mk'
    (fun (x, z) ↦ ⨁ᶠ p ∈ m.finSupp, let (x', y) := p; if x = x' then m ⟨x, y⟩ ⨀ m' (y, z) else 𝟘)
    (m.finSupp.biUnion (fun (x, y) ↦
      m'.finSupp
        |>.image (fun (y', z) ↦ if y = y' ∧ m ⟨x, y⟩ ⨀ m' (y, z) ≠ 𝟘 then some (x, z) else none)
        |>.filterMap (·) (fun _ _ _ ↦ Option.eq_of_mem_of_mem)))
    (by
      simp only [W.supp_mem_iff, ne_eq, WeightedFinsum_eq_zero_iff, 𝒞.mem_finSupp_iff,
        ite_eq_right_iff, Prod.forall, not_forall, Prod.mk.eta, Finset.mem_biUnion,
        Finset.mem_filterMap, Finset.mem_image, Prod.exists, exists_eq_right,
        Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq, existsAndEq, and_true,
        true_and]
      intro x z
      constructor
      · simp only [exists_prop, exists_and_left, exists_eq_left', forall_exists_index, and_imp]
        rintro _ y hxy ⟨_⟩ hxyyz
        use x, y
        simp_all only [not_false_eq_true, and_self, and_true, true_and]
        contrapose! hxyyz
        simp_all only [WeightedPreSemiring.mul_wZero]
      · grind)

def 𝒞.wProd_id {𝒮 X : Type} [Fintype X] [DecidableEq X] [WeightedSemiring 𝒮] [DecidableEq 𝒮] : 𝒞 𝒮 (X × X) :=
  if h : ¬(𝟙 : 𝒮) = 𝟘 then
    𝒞.mk'
      (fun (x, y) ↦ if x = y then 𝟙 else 𝟘)
      (Fintype.elems.map ⟨fun a ↦ (a, a), by intro; simp⟩)
      (by simp [h, Fintype.complete])
  else 𝟘

notation "⨯1" => 𝒞.wProd_id

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem 𝒞.wProd_id_apply {X : Type} [Fintype X] [DecidableEq X] [DecidableEq 𝒮] (x : X × X) :
    (⨯1 : 𝒞 𝒮 (X × X)) x = if x.1 = x.2 then 𝟙 else 𝟘 := by
  simp [𝒞.wProd_id]
  split_ifs <;> grind [𝒞.wZero_apply, 𝒞.mk_apply, 𝒲.mk_apply]

@[simp]
theorem WeightedProduct.wProd_wZero {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
    (a : 𝒞 𝒮 (X × Y)) :
    (a ⨯ (𝟘 : 𝒞 𝒮 (Y × Z))) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]
@[simp]
theorem WeightedProduct.wZero_wProd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
    (a : 𝒞 𝒮 (Y × Z)) :
    ((𝟘 : 𝒞 𝒮 (X × Y)) ⨯ a) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem 𝒞.wOne_finSupp {Y : Type} [DecidableEq Y] [Fintype Y] [DecidableEq 𝒮] :
    (⨯1 : 𝒞 𝒮 (Y × Y)).finSupp = if (𝟙 : 𝒮) = 𝟘 then ∅ else Fintype.elems.map ⟨fun a ↦ (a, a), by intro; simp⟩ := by
  ext ⟨x, y⟩
  simp [WeightedOne.wOne, 𝒞.mk', dite_not, 𝒞.mem_finSupp_iff, ne_eq]
  split_ifs with h
  · simp [WeightedSemiring.if_one_is_zero_collapse h]
  · simp [Fintype.complete, h]

@[simp]
theorem WeightedProduct.wProd_wOne {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype Y] [DecidableEq 𝒮]
    (a : 𝒞 𝒮 (X × Y)) :
    (a ⨯ (⨯1 : 𝒞 𝒮 (Y × Y))) = a := by
  ext ⟨x, y⟩; simp [WeightedProduct.wProd]
  rw [WeightedFinsum_single ⟨x, y⟩]
  · simp only [↓reduceIte, WeightedSemiring.mul_wOne]
  · grind only [WeightedPreSemiring.mul_wZero, 𝒞.mem_finSupp_iff, cases eager Prod, cases Or]
  · grind only [𝒞.mem_finSupp_iff, WeightedSemiring.mul_wOne]
@[simp]
theorem WeightedProduct.wOne_wProd {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [DecidableEq 𝒮]
    (a : 𝒞 𝒮 (X × Y)) :
    ((⨯1 : 𝒞 𝒮 (X × X)) ⨯ a) = a := by
  ext ⟨x, y⟩; simp [WeightedProduct.wProd]
  split_ifs with h
  · simp [WeightedSemiring.if_one_is_zero_collapse h]
  · rw [WeightedFinsum_single ⟨x, x⟩]
    · simp only [↓reduceIte, WeightedSemiring.wOne_mul]
    · grind only [Function.Embedding.coeFn_mk, Prod.mk.injEq, Finset.mem_map, Fintype.complete,
      ite_eq_right_iff, cases eager Prod]
    · simp only [Finset.mem_map_mk, Fintype.complete, not_true_eq_false, ↓reduceIte,
      WeightedSemiring.wOne_mul, IsEmpty.forall_iff]

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
theorem WeightedFinsum_ite {α : Type} [DecidableEq α] {S : Finset α} (g : α → Prop) [DecidablePred g] (f : α → 𝒮) :
    (⨁ᶠ x ∈ S, if g x then f x else 𝟘) = ⨁ᶠ x ∈ S.filter g, f x := by
  induction S using Finset.induction with
  | empty => simp
  | insert x S hx ih =>
    simp_all
    rw [Finset.filter_insert]
    have : x ∉ S.filter g := by simp_all
    split_ifs
    · simp_all
    · simp_all

theorem WeightedProduct.wProd_assoc {X Y Z W : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] [DecidableEq 𝒮]
    (a : 𝒞 𝒮 (X × Y))
    (b : 𝒞 𝒮 (Y × Z))
    (c : 𝒞 𝒮 (Z × W)) :
    (a ⨯ b ⨯ c) = (a ⨯ (b ⨯ c)) := by
  ext ⟨x, w⟩
  simp only [wProd, 𝒞.mk', Prod.mk.eta, ne_eq, 𝒞.mk_apply, 𝒲.mk_apply, ← WeightedFinsum_mul_right,
    WeightedFinsum_eq_zero_iff, 𝒞.mem_finSupp_iff, Prod.forall, not_forall, Classical.not_imp, ←
    WeightedFinsum_mul_left]
  rw [WeightedFinsum_ite, WeightedFinsum_comm]
  congr! with ⟨x, y⟩
  split_ifs
  · subst_eqs
    apply WeightedFinsum_bij_ne_zero (fun ⟨_, z⟩ _ _ ↦ ⟨y, z⟩)
    · grind only [WeightedPreSemiring.mul_wZero, 𝒞.mem_finSupp_iff, WeightedPreSemiring.wZero_mul,
      Prod.mk.injEq, Finset.mem_filter, Finset.mem_biUnion, cases eager Prod]
    · grind only [Prod.mk.injEq, Finset.mem_filter, cases eager Prod]
    · simp only [𝒞.mem_finSupp_iff, ne_eq, exists_prop, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_filterMap, Finset.mem_image, Prod.exists, exists_eq_right,
      Option.ite_none_right_eq_some, Option.some.injEq, exists_and_left, Prod.mk.injEq, existsAndEq,
      and_true, true_and, Prod.forall, exists_and_right, exists_eq_right']
      grind only [WeightedPreSemiring.mul_wZero, WeightedPreSemiring.wZero_mul,
        WeightedPreSemiring.mul_assoc, cases eager Prod, cases Or]
    · grind only [Finset.mem_filter, WeightedPreSemiring.mul_assoc, cases eager Prod]
  · rw [WeightedFinsum_eq_zero_iff]
    grind only [WeightedPreSemiring.wZero_mul, Finset.mem_filter, cases eager Prod]

theorem WeightedProduct.sMul_wProd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq 𝒮]
    (m : 𝒞 𝒮 (X × Y)) (m' : 𝒞 𝒮 (Y × Z)) (w : 𝒮) :
    w • (m ⨯ m') = w • m ⨯ m' := by
  ext ⟨x, z⟩
  simp
  simp [WeightedProduct.wProd]
  simp [← WeightedFinsum_mul_left]
  apply WeightedFinsum_bij_ne_zero (fun a _ _ ↦ a)
  · simp
    intro x' y hx'y h
    split_ifs at h
    · subst_eqs
      contrapose! h
      simp_all [← WeightedPreSemiring.mul_assoc]
    · simp at h
  · simp only [𝒞.mem_finSupp_iff, ne_eq, imp_self, implies_true]
  · simp
    rintro _ y h ⟨_⟩ h'
    simp_all [← WeightedPreSemiring.mul_assoc]
    contrapose! h
    simp [h]
  · simp
    intro x' y hx'y h
    split_ifs
    · subst_eqs
      simp_all [← WeightedPreSemiring.mul_assoc]
    · simp_all [← WeightedPreSemiring.mul_assoc]

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝓁` is a family of output weightings `𝓁[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝓁 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F N 𝒮 Q: Type)
    [WeightedSemiring 𝒮]
where
  /-- `ι` is the initial weightings. -/
  ι : 𝒞 𝒮 (Unit × Q)
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F,N]) → 𝒞 𝒮 (Q × Q)
  /-- `𝓁` is a family of output weightings `𝓁[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝓁 instead of λ, since λ is the function symbol in Lean. -/
  𝓁 : (α β : Pk[F,N]) → 𝒞 𝒮 (Q × Unit)
notation "WNKA[" f "," n "," s "," q "]" => WNKA (F:=f) (n:=n) (𝒮:=s) (Q:=q)

inductive StateSpace where
  | Heart
  | Club
deriving DecidableEq, Fintype

notation "♡" => StateSpace.Heart
notation "♣" => StateSpace.Club

def S : RPol[F,N,𝒮] → Type
  | wnk_rpol {drop} => I {♡}
  | wnk_rpol {skip} => I {♡}
  | wnk_rpol {@test ~_} => I {♡}
  | wnk_rpol {@mod ~_} => I {♡}
  | wnk_rpol {dup} => I {♡, ♣}
  | wnk_rpol {~_ ⨀ ~p₁} => S p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁ ; ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁*} => S p₁
where I : (Set StateSpace) → Type := (↑·)

attribute [simp] S.I

def S.decidableEq (p : RPol[F,N,𝒮]) : DecidableEq (S p) :=
  match p with
  | wnk_rpol {drop} => Subtype.instDecidableEq
  | wnk_rpol {skip} => Subtype.instDecidableEq
  | wnk_rpol {@test ~_}
  | wnk_rpol {@mod ~_} => Subtype.instDecidableEq
  | wnk_rpol {dup} => Subtype.instDecidableEq
  | wnk_rpol {~_ ⨀ ~p₁} => S.decidableEq p₁
  | wnk_rpol {~p₁ ⨁ ~p₂}
  | wnk_rpol {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_rpol {~p₁*} => S.decidableEq p₁

instance S.instDecidableEq {p : RPol[F,N,𝒮]} : DecidableEq (S p) := S.decidableEq p

def S.ι {X Y : Type} : 𝒞 𝒮 (Unit × X) → 𝒞 𝒮 (Unit × Y) → 𝒞 𝒮 (Unit × (X ⊕ Y)) :=
  fun m₁ m₂ ↦
    𝒞.mk' (fun ⟨_, x⟩ ↦
      x.elim (m₁ ⟨(), ·⟩) (m₂ ⟨(), ·⟩))
      ( let sx := m₁.finSupp.map ⟨(·.snd), by intro; grind⟩
        let sy := m₂.finSupp.map ⟨(·.snd), by intro; grind⟩
        Finset.product {()} (sx.disjSum sy))
      (by simp; grind)
notation "ι[" a "," b"]" => S.ι a b
def S.𝓁 {X Y : Type} : 𝒞 𝒮 (X × Unit) → 𝒞 𝒮 (Y × Unit) → 𝒞 𝒮 ((X ⊕ Y) × Unit) :=
  fun m₁ m₂ ↦
    𝒞.mk' (fun ⟨x, _⟩ ↦
      x.elim (m₁ ⟨·, ()⟩) (m₂ ⟨·, ()⟩))
      ( let sx := m₁.finSupp.map ⟨(·.fst), by intro; grind⟩
        let sy := m₂.finSupp.map ⟨(·.fst), by intro; grind⟩
        Finset.product (sx.disjSum sy) {()})
      (by simp; grind)
notation "𝓁[" a "," b"]" => S.𝓁 a b
attribute [grind] Prod.map Function.Injective in
def S.δ {X Y Z W : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W] :
    𝒞 𝒮 (X × Y) →
    𝒞 𝒮 (X × W) →
    𝒞 𝒮 (Z × Y) →
    𝒞 𝒮 (Z × W) →
    𝒞 𝒮 ((X ⊕ Z) × (Y ⊕ W)) :=
  fun mxy mxw mzy mzw ↦
    𝒞.mk' (fun ⟨xz, yw⟩ ↦
      xz.elim (fun x ↦ yw.elim (mxy ⟨x, ·⟩) (mxw ⟨x, ·⟩))
              (fun z ↦ yw.elim (mzy ⟨z, ·⟩) (mzw ⟨z, ·⟩)))
      (
        let sxy := mxy.finSupp.map ⟨Prod.map .inl .inl, by grind⟩
        let sxw := mxw.finSupp.map ⟨Prod.map .inl .inr, by grind⟩
        let szy := mzy.finSupp.map ⟨Prod.map .inr .inl, by grind⟩
        let szw := mzw.finSupp.map ⟨Prod.map .inr .inr, by grind⟩
        sxy ∪ sxw ∪ szy ∪ szw
      )
      (by
        simp only [_root_.W.supp_mem_iff, ne_eq, Finset.union_assoc, Finset.mem_union,
          Finset.mem_map, 𝒞.mem_finSupp_iff, Function.Embedding.coeFn_mk, Prod.exists,
          Prod.map_apply, Prod.forall, Prod.mk.injEq, Sum.forall, Sum.elim_inl, Sum.inl.injEq,
          exists_eq_right_right, reduceCtorEq, and_false, exists_false, or_false, false_or,
          Sum.elim_inr, Sum.inr.injEq, exists_eq_right, implies_true, and_self])
notation "δ[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.δ a b c d

instance S.fintype (p : RPol[F,N,𝒮]) : Fintype (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_rpol {dup} => ⟨{⟨♡, by simp⟩, ⟨♣, by simp⟩}, by rintro ⟨_, (h | h | h)⟩ <;> simp_all⟩
  | wnk_rpol {~_ ⨀ ~p₁} => S.fintype p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.fintype p₁; letI := S.fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁*} => S.fintype p₁
instance S.instFintype {p : RPol[F,N,𝒮]} : Fintype (S p) := S.fintype p
instance S.Finite {p : RPol[F,N,𝒮]} : Finite (S p) := Finite.of_fintype (S p)

variable [DecidableEq 𝒮]

def ι (p : RPol[F,N,𝒮]) : 𝒞 𝒮 (Unit × S p) := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    η' ⟨(), ♡, rfl⟩
  | wnk_rpol {dup} => η' ⟨(), ♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~p₂} => ι[ι p₁, 𝟘]
  | wnk_rpol {~p₁*} => ι p₁

def 𝓁 [DecidableEq 𝒮] (p : RPol[F,N,𝒮]) (α β : Pk[F,N]) : 𝒞 𝒮 (S p × Unit) :=
  match p with
  | wnk_rpol {drop} => 𝟘
  | wnk_rpol {skip} => if α = β then 𝟙 else 𝟘
  | wnk_rpol {@test ~γ} => if α = β ∧ β = γ then 𝟙 else 𝟘
  | wnk_rpol {@mod ~π} => if β = π then 𝟙 else 𝟘
  | wnk_rpol {dup} =>
    if α = β then
      𝒞.mk' (fun ⟨s, ()⟩ ↦ if s.val = ♣ then 𝟙 else 𝟘) (if ¬(𝟙 : 𝒮) = 𝟘 then {⟨⟨♣, by simp⟩, ()⟩} else ∅) (by
        simp only [S, S.I, W.supp_mem_iff, ne_eq, ite_eq_right_iff, Classical.not_imp, ite_not,
          Prod.forall, Subtype.forall, Set.mem_insert_iff, Set.mem_singleton_iff]
        grind only [Finset.mem_singleton, Set.mem_singleton_iff, Prod.mk.injEq, Finset.notMem_empty,
          Set.mem_insert_iff, Subtype.mk.injEq, cases eager PUnit, cases Or])
    else 𝟘
  | wnk_rpol {~_ ⨀ ~p₁} => 𝓁 p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} => 𝓁[𝓁 p₁ α β, 𝓁 p₂ α β]
  | wnk_rpol {~p₁ ; ~p₂} => 𝓁[⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ 𝓁 p₂ γ β), 𝓁 p₂ α β]
  | wnk_rpol {~p₁*} => ⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₁ ⨯ 𝓁 p₁ γ β)

def δ (p : RPol[F,N,𝒮]) (α β : Pk[F,N]) : 𝒞 𝒮 (S p × S p) := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} =>
    𝟘
  | wnk_rpol {dup} => 𝒞.liftPi fun s ↦ if s.val = ♡ ∧ α = β then η' ⟨♣, by simp [S]⟩ else 𝟘
  | wnk_rpol {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_rpol {~p₁ ⨁ ~p₂} =>
      δ[[δ p₁ α β,    𝟘],
        [𝟘,           δ p₂ α β]]
  | wnk_rpol {~p₁ ; ~p₂} =>
      δ[[δ p₁ α β,    ⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ δ p₂ γ β)],
        [𝟘,           δ p₂ α β]]
  | wnk_rpol {~p₁*} => δ p₁ α β ⨁ (⨁ᶠ γ, 𝓁 p₁ α γ ⨯ ι p₁)

example {a : Prop} : ¬¬a ↔ a := by exact not_not

def RPol.wnka (p : RPol[F,N,𝒮]) : WNKA[F,N,𝒮,S p] where
  ι := ι p
  δ := δ p
  𝓁 := 𝓁 p

@[simp] theorem RPol.wnka_ι (p : RPol[F,N,𝒮]) : p.wnka.ι = ι p := rfl
@[simp] theorem RPol.wnka_δ (p : RPol[F,N,𝒮]) : p.wnka.δ = δ p := rfl
@[simp] theorem RPol.wnka_𝓁 (p : RPol[F,N,𝒮]) : p.wnka.𝓁 = 𝓁 p := rfl

def big_wprod {X : Type} [Fintype X] [DecidableEq X] (l : List (𝒞 𝒮 (X × X))) : 𝒞 𝒮 (X × X) :=
  l.foldl (· ⨯ ·) 𝟙

def WNKA.compute' {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    𝒞 𝒮 (Q × Q) :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 𝟙 is okay by idempotency
  | [] | [_] => ⨯1
  | α::α'::s => 𝒜.δ α α' ⨯ 𝒜.compute' (α' :: s)

def WNKA.compute'_right {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) {α α'} :
    𝒜.compute' (s ++ [α, α']) = (𝒜.compute' (s ++ [α]) ⨯ 𝒜.δ α α') := by
  induction s with
  | nil => simp [compute']
  | cons α₀ s ih =>
    simp
    rcases s with _ | ⟨α₁, s⟩
    · simp [compute']
    · simp [compute']
      simp at ih
      rw [ih]
      simp [WeightedProduct.wProd_assoc]

def WNKA.compute {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) :
    𝒞 𝒮 (Q × Unit) :=
  match s with
  -- NOTE: these are unreachable in practice, but setting them to 𝟙 is okay by idempotency
  | [] | [_] => 𝟙
  | [α, α'] => 𝒜.𝓁 α α'
  | α::α'::s => 𝒜.δ α α' ⨯ 𝒜.compute (α' :: s)

-- def WNKA.compute_cons_append {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α α' : Pk[F,N]) :
--     𝒜.compute (α :: A ++ [α']) =  (𝒜.compute' A ⨯ 𝒜.𝓁 α' α'') := by
--   induction A generalizing α with
--   | nil => simp [compute, compute']
--   | cons α₀ A ih =>
--     simp [compute, compute']
--     simp at ih
--     rw [ih α₀]
--     rcases A with _ | ⟨α₁, A⟩
--     · simp_all [compute, compute']
--     · simp [compute, compute']
--       simp at ih
--       rw [ih]
--       simp [WeightedProduct.wProd_assoc]

def WNKA.compute_pair {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α' α'' : Pk[F,N]) :
    𝒜.compute (A ++ [α', α'']) = (𝒜.compute' (A ++ [α']) ⨯ 𝒜.𝓁 α' α'') := by
  induction A with
  | nil => simp [compute, compute']
  | cons α₀ A ih =>
    simp [compute, compute']
    rcases A with _ | ⟨α₁, A⟩
    · simp_all [compute, compute']
    · simp [compute, compute']
      simp at ih
      rw [ih]
      simp [WeightedProduct.wProd_assoc]

def WNKA.compute_pair' {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) (A : List Pk[F,N]) (α₀ α' α'' : Pk[F,N]) :
    𝒜.compute (α₀ :: (A ++ [α', α''])) = (𝒜.compute' (α₀ :: (A ++ [α'])) ⨯ 𝒜.𝓁 α' α'') := by
  rw [← List.cons_append]
  rw [WNKA.compute_pair]
  rfl

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem WNKA.compute_eq_of {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) (h𝓁 : 𝒜.𝓁 = 𝒜'.𝓁) :
    𝒜.compute s = 𝒜'.compute s := by
  induction s with
  | nil => simp [compute]
  | cons x s ih =>
    induction s with
    | nil => simp [compute]
    | cons y s ih =>
      unfold compute
      split <;> try rfl
      · simp [h𝓁]
      · simp [hδ, ih]
        simp_all

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem WNKA.compute'_eq_of {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 𝒜' : WNKA[F,N,𝒮,Q]) (s : List Pk[F,N]) (hδ : 𝒜.δ = 𝒜'.δ) :
    𝒜.compute' s = 𝒜'.compute' s := by
  induction s with
  | nil => simp [compute']
  | cons x s ih =>
    induction s with
    | nil => simp [compute']
    | cons y s ih =>
      unfold compute'
      simp [ih, hδ]

def WNKA.sem {Q : Type} [Fintype Q] [DecidableEq Q] (𝒜 : WNKA[F,N,𝒮,Q]) : 𝒲 𝒮 GS[F,N] :=
  𝒲.mk (𝒜.ι ⨯ 𝒜.compute ·.pks <| ((), ())) (SetCoe.countable _)

def asdasd_supp {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (xy : X × Y) (m : 𝒞 𝒮 (Y × Z)) :=
  (η' (𝒮:=𝒮) xy ⨯ m).finSupp

@[simp]
theorem asdasd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (xy : X × Y) (m : 𝒞 𝒮 (Y × Z)) :
      (η' (𝒮:=𝒮) xy ⨯ m)
    = (𝒞.mk' (fun y ↦ if y.1 = xy.1 then m (xy.2, y.2) else 𝟘) (asdasd_supp xy m) (by
        obtain ⟨x, y⟩:= xy
        intro ⟨x', z⟩
        simp [WeightedProduct.wProd, η', asdasd_supp]
        split_ifs with h
        · simp [WeightedSemiring.if_one_is_zero_collapse h]
        · simp; grind) : 𝒞 𝒮 (X × Z)) := by
  obtain ⟨x, y⟩ := xy
  simp [WeightedProduct.wProd, η', asdasd_supp]
  split_ifs
  · simp [WeightedSemiring.if_one_is_zero_collapse ‹𝟙 = 𝟘›]
  · simp +contextual

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.induction (P : GS[F,N] → Prop)
    (h₀ : ∀ α α₀, P gs[α; α₀])
    (h₁ : ∀ α α₀ α₁, P gs[α; α₀; dup; α₁])
    (hn : ∀ α α₀ α₁ A αₙ, P (GS.mk α (α₀ :: α₁ :: A) αₙ))
    (x : GS[F,N]) :
    P x := by
  obtain ⟨α, A, αn⟩ := x
  match A with
  | [] => exact h₀ α αn
  | [α'] => exact h₁ α α' αn
  | α' :: α'' :: A => exact hn α α' α'' A αn

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.induction' (P : GS[F,N] → Prop)
    (h₀ : ∀ α α₀, P gs[α; α₀])
    (hn : ∀ α α₀ A αₙ, P (GS.mk α (A ++ [α₀]) αₙ))
    (x : GS[F,N]) :
    P x := by
  obtain ⟨α, A, αₙ⟩ := x
  match A with
  | [] => exact h₀ α αₙ
  | α' :: A =>
    simp [mk] at hn
    obtain ⟨A', α₀, h⟩ : ∃ A' α₀, α' :: A = A' ++ [α₀] := by
      use (α'::A).dropLast, (α'::A).getLast (by simp)
      if hA : A = [] then
        subst_eqs
        simp
      else
        simp [hA, List.dropLast_cons_of_ne_nil, List.getLast_cons, List.dropLast_concat_getLast]
    grind

@[simp]
theorem WeightedFinsum_map {α ι γ : Type} [DecidableEq γ] [DecidableEq ι] [WeightedPreSemiring α] (I : Finset ι) (g : ι ↪ γ) (f : γ → α) :
    (⨁ᶠ i ∈ I.map g, f i) = ⨁ᶠ i ∈ I, f (g i) := by
  simp [WeightedFinsum_eq_finset_sum]

@[simp]
theorem WeightedFinsum_disjSum {α ι γ : Type} [DecidableEq γ] [DecidableEq ι] [WeightedPreSemiring α] (I : Finset ι) (J : Finset γ) (f : ι ⊕ γ → α) :
    (⨁ᶠ i ∈ I.disjSum J, f i) = (⨁ᶠ i ∈ I, f (.inl i)) ⨁ ⨁ᶠ j ∈ J, f (.inr j) := by
  simp [WeightedFinsum_eq_finset_sum]
  rfl

theorem ι_wProd_𝓁 {A B : Type} [DecidableEq A] [DecidableEq B] {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)} {Z : 𝒞 𝒮 (A × Unit)} {W : 𝒞 𝒮 (B × Unit)} :
    (ι[X, Y] ⨯ 𝓁[Z, W]) = (X ⨯ Z) ⨁ (Y ⨯ W) := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd, S.ι, S.𝓁]
theorem ι_wProd_δ {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)}
    {Z : 𝒞 𝒮 (A × C)} {W : 𝒞 𝒮 (A × D)}
    {U : 𝒞 𝒮 (B × C)} {V : 𝒞 𝒮 (B × D)}
    :
    (ι[X, Y] ⨯ δ[[Z, W], [U, V]]) = ι[X ⨯ Z, X ⨯ W] ⨁ ι[Y ⨯ U, Y ⨯ V] := by
  ext ⟨_, a⟩
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd, S.ι, S.𝓁, S.δ]
  rcases a with c | d
  · simp
  · simp
theorem ι_wProd_δ' {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)}
    {Z : 𝒞 𝒮 (A × C)} {W : 𝒞 𝒮 (A × D)}
    {U : 𝒞 𝒮 (B × C)} {V : 𝒞 𝒮 (B × D)}
    :
    (ι[X, Y] ⨯ δ[[Z, W], [U, V]]) = ι[X ⨯ Z ⨁ Y ⨯ U, X ⨯ W ⨁ Y ⨯ V] := by
  ext ⟨_, a⟩
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd, S.ι, S.𝓁, S.δ]
  rcases a with c | d
  · simp
  · simp
theorem δ_wProd_δ {A B C D E F : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq E] [DecidableEq F]
    {A₁₁ : 𝒞 𝒮 (A × C)} {A₁₂ : 𝒞 𝒮 (A × D)}
    {A₂₁ : 𝒞 𝒮 (B × C)} {A₂₂ : 𝒞 𝒮 (B × D)}
    {B₁₁ : 𝒞 𝒮 (C × E)} {B₁₂ : 𝒞 𝒮 (C × F)}
    {B₂₁ : 𝒞 𝒮 (D × E)} {B₂₂ : 𝒞 𝒮 (D × F)}
    :
      (δ[[A₁₁, A₁₂], [A₂₁, A₂₂]] ⨯ δ[[B₁₁, B₁₂], [B₂₁, B₂₂]])
    = δ[[A₁₁ ⨯ B₁₁ ⨁ A₁₂ ⨯ B₂₁, A₁₁ ⨯ B₁₂ ⨁ A₁₂ ⨯ B₂₂],
        [A₂₁ ⨯ B₁₁ ⨁ A₂₂ ⨯ B₂₁, A₂₁ ⨯ B₁₂ ⨁ A₂₂ ⨯ B₂₂]] := by
  ext ⟨ab, ef⟩
  rcases ab with a | b
  · rcases ef with e | f
    · simp only [WeightedProduct.wProd, 𝒞.mk', S.δ, Finset.union_assoc, 𝒞.mk_apply, 𝒲.mk_apply,
      Prod.mk.eta, ne_eq, Sum.elim_inl, 𝒞.wAdd_apply]
      rw [WeightedFinsum_union, WeightedFinsum_union, WeightedFinsum_union]
      · simp
      all_goals
        intro h h' h'' ⟨ab, cd⟩ h'''
        have := h' h'''
        simp_all only [Finset.le_eq_subset, Finset.mem_map, 𝒞.mem_finSupp_iff, ne_eq,
          Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply, Prod.mk.injEq,
          Finset.bot_eq_empty, Finset.notMem_empty]
        obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
        have := h'' h'''
        simp_all
    · simp only [WeightedProduct.wProd, 𝒞.mk', S.δ, Finset.union_assoc, 𝒞.mk_apply, 𝒲.mk_apply,
      Prod.mk.eta, ne_eq, Sum.elim_inl, 𝒞.wAdd_apply]
      rw [WeightedFinsum_union, WeightedFinsum_union, WeightedFinsum_union]
      · simp
      all_goals
        intro h h' h'' ⟨ab, cd⟩ h'''
        have := h' h'''
        simp_all only [Finset.le_eq_subset, Finset.mem_map, 𝒞.mem_finSupp_iff, ne_eq,
          Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply, Prod.mk.injEq,
          Finset.bot_eq_empty, Finset.notMem_empty]
        obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
        have := h'' h'''
        simp_all
  · rcases ef with e | f
    · simp only [WeightedProduct.wProd, 𝒞.mk', S.δ, Finset.union_assoc, 𝒞.mk_apply, 𝒲.mk_apply,
      Prod.mk.eta, ne_eq, Sum.elim_inl, 𝒞.wAdd_apply]
      rw [WeightedFinsum_union, WeightedFinsum_union, WeightedFinsum_union]
      · simp
      all_goals
        intro h h' h'' ⟨ab, cd⟩ h'''
        have := h' h'''
        simp_all only [Finset.le_eq_subset, Finset.mem_map, 𝒞.mem_finSupp_iff, ne_eq,
          Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply, Prod.mk.injEq,
          Finset.bot_eq_empty, Finset.notMem_empty]
        obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
        have := h'' h'''
        simp_all
    · simp only [WeightedProduct.wProd, 𝒞.mk', S.δ, Finset.union_assoc, 𝒞.mk_apply, 𝒲.mk_apply,
      Prod.mk.eta, ne_eq, Sum.elim_inl, 𝒞.wAdd_apply]
      rw [WeightedFinsum_union, WeightedFinsum_union, WeightedFinsum_union]
      · simp
      all_goals
        intro h h' h'' ⟨ab, cd⟩ h'''
        have := h' h'''
        simp_all only [Finset.le_eq_subset, Finset.mem_map, 𝒞.mem_finSupp_iff, ne_eq,
          Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply, Prod.mk.injEq,
          Finset.bot_eq_empty, Finset.notMem_empty]
        obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
        have := h'' h'''
        simp_all

theorem δ_wProd_𝓁 {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {X : 𝒞 𝒮 (C × Unit)} {Y : 𝒞 𝒮 (D × Unit)}
    {Z : 𝒞 𝒮 (A × C)} {W : 𝒞 𝒮 (A × D)}
    {U : 𝒞 𝒮 (B × C)} {V : 𝒞 𝒮 (B × D)}
    :
    (δ[[Z, W], [U, V]] ⨯ 𝓁[X, Y]) = 𝓁[Z ⨯ X ⨁ W ⨯ Y, U ⨯ X ⨁ V ⨯ Y] := by
  ext ⟨a, _⟩
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd, S.ι, S.𝓁, S.δ]
  rw [WeightedFinsum_union, WeightedFinsum_union, WeightedFinsum_union]
  · rcases a with c | d <;> simp
  · intro h h' h'' ⟨ab, cd⟩ h'''
    simp_all
    have := h' h'''
    simp_all
    obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
    have := h'' h'''
    simp_all
  · intro h h' h'' ⟨ab, cd⟩ h'''
    simp_all
    have := h' h'''
    simp_all
    obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
    have := h'' h'''
    simp_all
  · intro h h' h'' ⟨ab, cd⟩ h'''
    simp_all
    have := h' h'''
    simp_all
    obtain ⟨a, b, h₀, ⟨_⟩, ⟨_⟩⟩ := this
    have := h'' h'''
    simp_all

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] in
@[simp]
theorem S.δ_identity {A B : Type} [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B] :
    (δ[[⨯1,𝟘],[𝟘,⨯1]] : 𝒞 𝒮 ((A ⊕ B) × (A ⊕ B))) = ⨯1 := by
  ext ⟨ab₁, ab₂⟩
  simp
  split_ifs
  · subst_eqs
    rcases ab₁ with a | b <;> simp [S.δ]
  · rcases ab₁ with a₁ | b₁ <;> rcases ab₂ with a₂ | b₂ <;> simp [S.δ]
    · grind
    · grind

theorem wProd_left_distrib {A B C : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {AB : 𝒞 𝒮 (A × B)} {BC : 𝒞 𝒮 (B × C)} {BC' : 𝒞 𝒮 (B × C)} :
    AB ⨯ (BC ⨁ BC') = (AB ⨯ BC) ⨁ (AB ⨯ BC') := by
  ext ⟨a, c⟩
  simp
  simp [WeightedProduct.wProd]
  simp [← WeightedFinsum_add]
  congr with ⟨a', b⟩
  simp
  split_ifs
  · subst_eqs; simp [WeightedPreSemiring.left_distrib]
  · simp
theorem ite_wAdd {α : Type} [WeightedPreSemiring α] {p : Prop} [Decidable p] {a b : α} :
    (if p then a ⨁ b else 𝟘) = (if p then a else 𝟘) ⨁ if p then b else 𝟘 := by
  split_ifs
  · rfl
  · simp
theorem wProd_right_distrib {A B C : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {AB : 𝒞 𝒮 (A × B)} {AB' : 𝒞 𝒮 (A × B)} {BC : 𝒞 𝒮 (B × C)} :
    (AB ⨁ AB') ⨯ BC = (AB ⨯ BC) ⨁ (AB' ⨯ BC) := by
  ext ⟨a, c⟩
  simp only [WeightedProduct.wProd, 𝒞.mk', 𝒞.wAdd_apply, WeightedPreSemiring.right_distrib,
    ite_wAdd, WeightedFinsum_add, Prod.mk.eta, ne_eq, wAdd_eq_zero_iff, not_and, 𝒞.mk_apply,
    𝒲.mk_apply]
  congr! 1
  all_goals
    apply WeightedFinsum_bij_ne_zero (fun a _ _ ↦ a)
    · simp only [𝒞.mem_finSupp_iff, 𝒞.wAdd_apply, ne_eq, wAdd_eq_zero_iff, not_and,
      ite_eq_right_iff, Classical.not_imp, and_imp, Prod.forall]
      rintro _ b h ⟨_⟩ h'
      contrapose! h'
      simp [h']
    · grind only [cases eager Prod]
    · simp only [𝒞.mem_finSupp_iff, ne_eq, ite_eq_right_iff, Classical.not_imp, exists_prop,
      𝒞.wAdd_apply, wAdd_eq_zero_iff, not_and, exists_and_left, exists_eq_right_right, and_imp,
      Prod.forall]
      rintro _ b h ⟨_⟩ h'
      grind
    · grind only [cases eager Prod]

theorem wProd_WeightedFinsum {ι A B C : Type} [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (AB : 𝒞 𝒮 (A × B)) (fBC : ι → 𝒞 𝒮 (B × C)) (S : Finset ι) :
    (AB ⨯ ⨁ᶠ i ∈ S, fBC i) = ⨁ᶠ i ∈ S, AB ⨯ fBC i := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih => simp_all [wProd_left_distrib]

theorem WeightedFinsum_wProd {ι A B C : Type} [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (BC : 𝒞 𝒮 (B × C)) (fAB : ι → 𝒞 𝒮 (A × B)) (S : Finset ι) :
    ((⨁ᶠ i ∈ S, fAB i) ⨯ BC) = ⨁ᶠ i ∈ S, (fAB i ⨯ BC) := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S hi ih => simp_all [wProd_right_distrib]


def GS.ofPks (l : List Pk[F,N]) (h : 2 ≤ l.length) : GS[F,N] :=
  GS.mk (l.head (List.ne_nil_of_length_pos (by omega))) (l.drop 1).dropLast (l.getLast (List.ne_nil_of_length_pos (by omega)))

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
@[simp] theorem GS.ofPks_pks (l : List Pk[F,N]) (h : 2 ≤ l.length) : (GS.ofPks l h).pks = l := by
  simp [ofPks, pks, GS.mk]
  apply List.ext_getElem
  · simp; omega
  · simp
    intro i h₁ h₂
    rcases i with _ | i
    · simp; apply List.head_eq_getElem
    · simp [List.getElem_append]
      split_ifs
      · rfl
      · grind

omit [Fintype F] [DecidableEq F] [Fintype N] [DecidableEq N] in
theorem GS.eq_iff_pks_eq (g₁ g₂ : GS[F,N]) : g₁ = g₂ ↔ g₁.pks = g₂.pks := by
  simp only [pks, List.cons_append, List.cons.injEq]
  obtain ⟨g₁₀, g₁, g₁₁⟩ := g₁
  obtain ⟨g₂₀, g₂, g₂₁⟩ := g₂
  constructor
  · grind
  · intro h
    obtain ⟨h₀, h₁⟩ := h
    have := congrArg List.length h₁
    grind only [List.length_cons, List.length_nil, List.append_inj, List.length_append, →
      List.eq_nil_of_append_eq_nil]

@[simp]
theorem RPol.wnka_sem_pair (p : RPol[F,N,𝒮]) (α γ : Pk[F,N]) :
    p.wnka.sem (α, [], γ) = (ι p ⨯ 𝓁 p α γ) ((), ()) := rfl

theorem RPol.wnka_sem_eq_of (p : RPol[F,N,𝒮]) (f)
    (h₂ : ∀ (A : List Pk[F,N]) (α α' : Pk[F,N]), (ι p ⨯ p.wnka.compute' (A ++ [α]) ⨯ 𝓁 p α α') ((), ()) = f (GS.ofPks (A ++ [α, α']) (by simp))) :
    p.wnka.sem = f := by
  ext g
  obtain ⟨g₀, g, g₁⟩ := g
  if g = [] then
    subst_eqs
    simp [wnka, WNKA.sem, GS.pks, WNKA.compute]
    have := h₂ [] g₀ g₁
    simp [WNKA.compute'] at this
    assumption
  else
    obtain ⟨A, α, α', h⟩ : ∃ A α α', GS.mk g₀ g g₁ = GS.ofPks (A ++ [α, α']) (by simp) := by
      conv =>
        arg 1; ext; arg 1; ext; arg 1; ext
        rw [GS.eq_iff_pks_eq]
      simp [GS.mk]
      simp [GS.pks]
      set A := g₀ :: (g ++ [g₁])
      use A.take (A.length - 2),
          A[A.length - 2]'(by simp [A]; omega),
          A[A.length - 1]'(by simp [A])
      apply List.ext_getElem
      · simp; grind
      · intro i h₀ h₁
        simp [List.getElem_append, List.getElem_cons]
        intro h₂
        split_ifs
        · congr; omega
        · congr; grind
        · omega
    simp [GS.mk] at h
    rw [h]
    simp [wnka, WNKA.sem, WNKA.compute_pair]
    simp [← WeightedProduct.wProd_assoc]
    exact h₂ A α α'

variable [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

theorem RPol.wnka_sem_drop :
    (RPol.wnka wnk_rpol {drop}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {drop} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    simp only [WNKA.sem, wnka, ι, 𝓁, GS.pks, List.cons_append, asdasd, 𝒞.mk', ↓reduceIte,
      𝒞.mk_apply, 𝒲.mk_apply, GS.mk, List.nil_append, WNKA.compute, 𝒞.wZero_apply]
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, List.nil_append,
      WNKA.compute, WeightedProduct.wZero_wProd, WeightedProduct.wProd_wZero, 𝒞.wZero_apply]
  next α A αn =>
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, δ, GS.pks]
theorem RPol.wnka_sem_skip :
    (RPol.wnka wnk_rpol {skip}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {skip} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝓁, ι, GS.pks]
    split_ifs with h₁ h₂ h₃ <;> subst_eqs
    · simp [𝒞.wOne_apply]
    · simp at h₂
    · obtain ⟨_, _, _⟩ := h₃
      contradiction
    · rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, ι, δ, GS.pks, List.cons_append, asdasd, 𝒞.mk', ↓reduceIte,
      𝒞.mk_apply, 𝒲.mk_apply, GS.mk, List.nil_append, WNKA.compute, WeightedProduct.wZero_wProd,
      𝒞.wZero_apply, right_eq_ite_iff, imp_false, not_exists]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, WeightedProduct.wZero_wProd,
      WeightedProduct.wProd_wZero, 𝒞.wZero_apply, right_eq_ite_iff, forall_exists_index]
    grind
theorem RPol.wnka_sem_test {t} :
    (RPol.wnka wnk_rpol {@test ~t}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {@test ~t} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝓁, ι, GS.pks]
    split_ifs
    · simp only [𝒞.wOne_apply]
    · grind only
    · grind only
    · rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, List.nil_append,
      WNKA.compute, WeightedProduct.wZero_wProd, WeightedProduct.wProd_wZero, 𝒞.wZero_apply,
      right_eq_ite_iff]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, WeightedProduct.wZero_wProd,
      WeightedProduct.wProd_wZero, 𝒞.wZero_apply, right_eq_ite_iff]
    grind
theorem RPol.wnka_sem_mod {π} :
    (RPol.wnka wnk_rpol {@mod ~π}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {@mod ~π} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝓁, ι, GS.pks]
    split_ifs with h₁ h₂ h₃ <;> simp_all
    grind
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, List.nil_append,
      WNKA.compute, WeightedProduct.wZero_wProd, WeightedProduct.wProd_wZero, 𝒞.wZero_apply,
      right_eq_ite_iff, forall_exists_index]
    grind
  next α A αn =>
    simp only [WNKA.sem, wnka, δ, GS.pks, List.cons_append, GS.mk, 𝒲.mk_apply, WNKA.compute,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self, WeightedProduct.wZero_wProd,
      WeightedProduct.wProd_wZero, 𝒞.wZero_apply, right_eq_ite_iff, forall_exists_index]
    grind
theorem RPol.wnka_sem_dup (h : ((𝟙 : 𝒮) ≠ 𝟘)) (h' : ((𝟘 : 𝒮) ≠ 𝟙)) :
    (RPol.wnka wnk_rpol {dup}).sem = G (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {dup} := by
  ext x
  simp [G]
  induction x using GS.induction
  next α α₀ =>
    -- TODO: simp?
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, 𝓁, ι, GS.pks]
    split_ifs
    · subst_eqs
      simp; grind
    · simp_all; grind
    · grind
    · rfl
  next α α₀ α₁ =>
    simp only [WNKA.sem, wnka, ι, δ, 𝒞.liftPi, 𝒞.mk', 𝓁, h, not_false_eq_true, ↓reduceIte, GS.pks,
      List.cons_append, asdasd, 𝒞.mk_apply, 𝒲.mk_apply, GS.mk, List.nil_append, WNKA.compute]
    split_ifs
    · grind
    · subst_eqs
      simp [WeightedProduct.wProd]
      split_ifs <;> subst_eqs
      · simp_all
        let a : S (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {dup} := ⟨♡, by simp⟩
        let b : S (F:=F) (N:=N) (𝒮:=𝒮) wnk_rpol {dup} := ⟨♣, by simp⟩
        rw [WeightedFinsum_single ⟨a, b⟩]
        · simp [a, b, η']
        · simp +contextual [Fintype.complete, a, b]
          intros
          subst_eqs
          simp_all [η']
        · simp [Fintype.complete, a, b]
      · simp_all
      · simp_all
        grind only
      · simp_all
    · grind
    · simp
  next α A αn =>
    simp only [WNKA.sem, wnka, ι, δ, 𝒞.liftPi, 𝒞.mk', 𝓁, h, not_false_eq_true, ↓reduceIte, GS.pks,
      List.cons_append, asdasd, 𝒞.mk_apply, 𝒲.mk_apply, GS.mk, WNKA.compute, List.append_eq_nil_iff,
      List.cons_ne_self, and_false, imp_self]
    split_ifs
    · grind
    · split
      · rename_i hα
        obtain ⟨α, _, _⟩ := hα
      · simp only [S, S.I, WeightedProduct.wProd, 𝒞.mk', 𝒞.mk_apply, 𝒲.mk_apply, Prod.mk.eta,
        ne_eq, true_and, WeightedFinsum_eq_zero_iff, Finset.mem_biUnion, Fintype.complete,
        Finset.mem_map, 𝒞.mem_finSupp_iff, Function.Embedding.coeFn_mk, Subtype.exists,
        Set.mem_insert_iff, Set.mem_singleton_iff, ite_eq_right_iff, forall_exists_index, and_imp,
        Prod.forall, Prod.mk.injEq, Subtype.forall, Subtype.mk.injEq]
        intro a ha b hb c hc d hd h'' _ _ _
        subst_eqs
        split_ifs with h₀ h₁ h₂ <;> subst_eqs
        · obtain ⟨_, _⟩ := h₁
          subst_eqs
          simp [η']
        · simp only [𝒞.wZero_apply, WeightedPreSemiring.wZero_mul, ite_self, WeightedFinsum_zero,
          WeightedPreSemiring.mul_wZero]
        · simp only [𝒞.wZero_apply, WeightedPreSemiring.wZero_mul]
        · simp only [𝒞.wZero_apply, WeightedPreSemiring.wZero_mul, ite_self, WeightedFinsum_zero,
          WeightedPreSemiring.mul_wZero]
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
theorem RPol.wnka_sem_add {p₁ p₂ : RPol[F,N,𝒮]} :
    wnk_rpol {~p₁ ⨁ ~p₂}.wnka.sem = p₁.wnka.sem ⨁ p₂.wnka.sem := by
  ext S
  induction S using GS.induction'
  next α α₀ =>
    simp [G]
    simp [wnka, WNKA.sem, GS.mk, WNKA.compute, ι, GS.pks, 𝓁, G]
    rw [ι_wProd_𝓁]
    simp
  next α α₀ α₁ A α₂ =>
    simp [G]
    simp [WNKA.sem, GS.mk, WNKA.compute, GS.pks, ι, 𝓁, G, δ]
    simp [WNKA.compute_pair', 𝓁, δ]
    generalize ι p₁ = ι₁
    generalize ι p₂ = ι₂
    generalize 𝓁 p₁ α₁ α₂ = 𝓁₁
    generalize 𝓁 p₂ α₁ α₂ = 𝓁₂
    generalize (α₀ :: (A ++ [α₁])) = A
    simp [← WeightedProduct.wProd_assoc]
    induction A generalizing ι₁ ι₂ with
    | nil =>
      simp [WNKA.compute']
      rw [ι_wProd_𝓁]
      simp
    | cons α A ih =>
      rcases A with _ | ⟨α', A⟩
      · simp [WNKA.compute']
        rw [ι_wProd_𝓁]
        rfl
      · simp [WNKA.compute']
        simp [← WeightedProduct.wProd_assoc, δ]
        simp [ι_wProd_δ']
        rw [ih]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
theorem RPol.wnka_sem_weight {w} {p : RPol[F,N,𝒮]} :
    wnk_rpol {~w ⨀ ~p}.wnka.sem = (w • p.wnka.sem) := by
  ext x
  induction x using GS.induction
  next α α₀ =>
    simp [WNKA.sem, wnka, ι, instSMul𝒞, 𝒞.mk', ne_eq, 𝓁, GS.pks, List.cons_append, GS.mk,
      List.nil_append, WNKA.compute, instSMul𝒲, 𝒲.sMul_apply, ←  WeightedProduct.sMul_wProd]
  next α α₀ α₁ =>
    simp [WNKA.sem, WNKA.compute, wnka, δ, GS.mk, 𝒲.mk_apply, ι, 𝓁, GS.pks,
      ← WeightedProduct.wProd_assoc, ← WeightedProduct.sMul_wProd]
  next α A αn =>
    simp [GS.mk, wnka, WNKA.sem, ι, WNKA.compute, GS.pks, ← WeightedProduct.wProd_assoc,
      ← WeightedProduct.sMul_wProd, δ, ι, 𝓁]
    congr! 3
    apply WNKA.compute_eq_of <;> rfl

def GS.splitAtJoined (g : GS[F,N]) (n : ℕ) (γ : Pk[F,N]) : GS[F,N] × GS[F,N] :=
  let (g₀, g, gₙ)  := g
  let (l, r) := g.splitAt n
  ((g₀, l, γ), (γ, r, gₙ))

example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 0 γ = (gs[α;γ], gs[γ;α₁;dup;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 1 γ = (gs[α;α₁;dup; γ], gs[γ;α₂;dup;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 2 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl
example {α α₁ α₂ α₃ γ : Pk[F,N]} :
    gs[α;α₁;dup;α₂;dup;α₃].splitAtJoined 3 γ = (gs[α;α₁;dup;α₂;dup;γ], gs[γ;α₃]) := rfl

-- a;b;dup;c
--  ^     ^
-- a;γ ◇ γ;b;dup;c
-- a;b;dup;γ ◇ γ;c

omit [WeightedPartialOrder 𝒮] [WeightedMonotonePreSemiring 𝒮] [DecidableEq 𝒮] in
theorem G.concat_apply [Encodable F] [Encodable N] {p₁ p₂ : RPol[F,N,𝒮]} {xₙ : GS F N} :
      ((G p₁ ♢ G p₂) : 𝒲 𝒮 _) xₙ
    = ⨁ᶠ i ∈ Finset.range (xₙ.2.1.length + 1), ⨁ᶠ (γ : Pk[F,N]), (G p₁) (xₙ.splitAtJoined i γ).1 ⨀ (G p₂) (xₙ.splitAtJoined i γ).2 := by
  obtain ⟨α, A, αₙ⟩ := xₙ
  rw [← WeightedSum_finset]
  simp only [WeightedConcat.concat, 𝒲.mk_apply]
  simp [← WeightedSum_finset]
  have := WeightedSum_prod (f:=fun ((x, x_1) : ({ x // x ∈ Finset.range (A.length + 1) } × { x // x ∈ (Finset.univ : Finset Pk[F,N]) })) ↦
    (G p₁) (GS.splitAtJoined (α, A, αₙ) x.val ↑x_1).1 ⨀ (G p₂) (GS.splitAtJoined (α, A, αₙ) x.val ↑x_1).2
    )
  simp at this
  rw [← this]; clear this
  apply WeightedSum_eq_WeightedSum_of_ne_one_bij (fun ⟨⟨⟨i, hi⟩, ⟨γ, hγ⟩⟩, hi'⟩ ↦ by
    simp [GS.splitAtJoined] at hi'
    exact ⟨(α, A.take i, γ), by
      simp
      contrapose! hi'
      simp [hi', GS.splitAtJoined]⟩)
  · intro ⟨⟨⟨i, hi⟩, ⟨γ, hγ⟩⟩, hi'⟩
    simp_all
    rintro j hj α' hα' h
    apply Prod.eq_iff_fst_eq_snd_eq.mp at h
    simp at h
    obtain ⟨h, h'⟩ := h
    simp at hi hi'
    grind
  · intro ⟨g₀, hg₀⟩
    simp at hg₀ ⊢
    intro g₁ hg₁ h h'
    split at h
    split at h
    · subst_eqs
      simp only [List.length_append]
      rename_i A₀ γ A₁
      simp [GS.splitAtJoined]
      use A₀.length
      simp +arith only [List.take_left', List.drop_left', true_and]
      use γ
    · contradiction
  · simp [GS.splitAtJoined]
    intro i hi
    intro γ hγ
    rw [WeightedSum_eq_single ⟨(γ, List.drop i A, αₙ), by simp; contrapose! hγ; simp [hγ]⟩]
    · simp
    · simp
      intro g hg hg' h
      split at h
      rename_i α' x β' γ' y ξ h'
      split_ifs at h
      subst_eqs
      simp at h
      rw [Prod.eq_iff_fst_eq_snd_eq] at h
      obtain ⟨h₀, h₁⟩ := h
      simp at h₁
      obtain ⟨h₁, ⟨_⟩⟩ := h₁
      suffices y = List.drop i A by subst_eqs; simp_all
      rw [← h₁]
      rw [List.drop_append_eq_append_drop]
      simp
      have : (i - min i A.length) = 0 := by omega
      simp [this]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
attribute [-simp] WeightedFinsum_range_succ WeightedFinsum_range_add in
theorem RPol.seq_wnka_compute'' {p₁ p₂ : RPol[F,N,𝒮]} [Inhabited Pk[F,N]] {A} :
        wnk_rpol {~p₁; ~p₂}.wnka.compute' A =
    δ[[p₁.wnka.compute' A,
        (⨁ᶠ γ, ⨁ᶠ i ∈ Finset.range (A.length - 1), p₁.wnka.compute' (A.take (i + 1)) ⨯ 𝓁 p₁ A[i]! γ ⨯ ι p₂ ⨯ p₂.wnka.compute' (γ :: A.drop (i + 1)))],
      [𝟘, p₂.wnka.compute' A]] := by
  induction A using List.reverseRecOn with
  | nil => simp [WNKA.compute']
  | append_singleton A α₀ ih =>
    clear ih
    induction A using List.reverseRecOn generalizing α₀ with
    | nil => simp [WNKA.compute']
    | append_singleton A α₁ ih =>
      simp [WNKA.compute'_right]
      rw [ih]; clear ih
      simp [δ]
      rw [δ_wProd_δ]
      simp only [WeightedProduct.wProd_wZero, WeightedPreSemiring.wAdd_comm,
        WeightedPreSemiring.wZero_add, wProd_WeightedFinsum, ← WeightedProduct.wProd_assoc,
        WeightedFinsum_wProd, ← WeightedFinsum_add, WeightedProduct.wZero_wProd,
        WeightedPreSemiring.add_wZero, WeightedFinsum_zero, WeightedFinsum_range_add,
        Finset.range_one, WeightedFinsum_singleton, add_zero, List.take_append, List.take_succ_cons,
        List.take_zero, List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, lt_add_iff_pos_right, Nat.zero_lt_succ, getElem?_pos, le_refl,
        List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, Option.getD_some,
        List.drop_append, List.drop_succ_cons, List.drop_zero, WNKA.compute', wnka_δ,
        WeightedProduct.wProd_wOne]
      congr! 4 with γ
      apply WeightedFinsum_congr _ fun i hi ↦ ?_
      simp only [Finset.mem_range] at hi
      simp only [List.take_append_eq_append_take, (by omega : i + 1 - A.length = 0), List.take_zero,
        List.append_nil, List.getElem?_append, hi, ↓reduceIte, getElem?_pos, Option.getD_some,
        List.drop_append_eq_append_drop, List.drop_zero]
      nth_rw 2 [← List.cons_append]
      simp only [WNKA.compute'_right, wnka_δ]
      simp only [List.cons_append, ← WeightedProduct.wProd_assoc]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem 𝒞.unit_pair_wProd {m₁ m₂ : 𝒞 𝒮 (Unit × Unit)} : m₁ ((), ()) ⨀ m₂ ((), ()) = (m₁ ⨯ m₂) ((), ()) := by
  simp [WeightedProduct.wProd]
  rw [WeightedFinsum_single ⟨(), ()⟩] <;> simp +contextual

attribute [-simp] WeightedFinsum_range_succ WeightedFinsum_range_add in
theorem RPol.wnka_sem_seq [Encodable F] [Encodable N] {p₁ p₂ : RPol[F,N,𝒮]}
    (ih₁ : p₁.wnka.sem = G p₁) (ih₂ : p₂.wnka.sem = G p₂) :
    wnk_rpol {~p₁ ; ~p₂}.wnka.sem = G wnk_rpol {~p₁; ~p₂} := by
  apply wnka_sem_eq_of
  intro A α α'
  letI : Inhabited Pk[F,N] := ⟨α⟩
  simp only [ι, seq_wnka_compute'', List.length_append, List.length_cons, List.length_nil, zero_add,
    add_tsub_cancel_right, List.getElem!_eq_getElem?_getD, 𝓁, G, GS.ofPks, GS.mk, List.drop_one,
    ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_append_of_ne_nil, List.cons_ne_self,
    List.getLast_cons, List.getLast_singleton, G.concat_apply, List.length_dropLast, List.length_tail,
    Nat.reduceAdd, Nat.add_one_sub_one, GS.splitAtJoined, List.splitAt_eq]
  simp only [← ih₁, ← ih₂]
  rw [ι_wProd_δ', ι_wProd_𝓁]
  nth_rw 2 [WeightedFinsum_comm]
  simp only [WeightedProduct.wProd_wZero, WeightedPreSemiring.add_wZero, wProd_WeightedFinsum,
    WeightedProduct.wZero_wProd, WeightedFinsum_wProd, ← WeightedFinsum_add, WeightedFinsum_𝒞_apply,
    𝒞.wAdd_apply, ← List.tail_dropLast, ne_eq, reduceCtorEq, not_false_eq_true,
    List.dropLast_append_of_ne_nil, List.dropLast_cons₂, List.dropLast_singleton, List.drop_tail,
    WeightedFinsum_range_add, Finset.range_one, WeightedFinsum_singleton, add_zero,
    List.drop_append, List.drop_succ_cons, List.drop_nil, wnka_sem_pair]
  congr with γ
  nth_rw 2 [WeightedPreSemiring.wAdd_comm]
  rcases A with _ | ⟨α₀, A⟩
  · simp [WNKA.compute', ← WeightedProduct.wProd_assoc]
  · simp only [List.cons_append, ← WeightedProduct.wProd_assoc, List.length_cons,
    List.take_succ_cons, List.drop_succ_cons, WNKA.sem, wnka_ι, GS.pks, List.head_cons,
    List.tail_cons, 𝒲.mk_apply, 𝒞.unit_pair_wProd]
    congr! 1
    · nth_rw 3 [WeightedProduct.wProd_assoc]
      congr! 4
      simp [List.take_append_eq_append_take, WNKA.compute_pair']
      congr
      exact (List.take_self_eq_iff A).mpr (by omega)
    · apply WeightedFinsum_congr _ fun i hi ↦ ?_
      simp at hi
      congr! 1
      have h₀ : i - A.length = 0 := by omega
      rcases i with _ | i
      · simp only [List.take_append_eq_append_take, List.take_zero, h₀, List.append_nil,
        WNKA.compute', WeightedProduct.wProd_wOne, List.length_cons, List.length_append,
        List.length_nil, zero_add, lt_add_iff_pos_left, add_pos_iff, Nat.zero_lt_succ, or_true,
        getElem?_pos, List.getElem_cons_zero, Option.getD_some, WeightedProduct.wProd_assoc,
        List.drop_zero, List.nil_append, WNKA.compute, wnka_𝓁, List.append_assoc, List.cons_append,
        WNKA.compute_pair']
      · simp only [List.take_append_eq_append_take, h₀, List.take_zero, List.append_nil,
          List.getElem?_cons_succ, List.getElem?_append, List.getElem?_cons, List.length_nil,
          Nat.not_lt_zero, not_false_eq_true, getElem?_neg, WeightedProduct.wProd_assoc,
          List.drop_append_eq_append_drop, List.drop_zero, List.append_assoc, List.cons_append,
          List.nil_append, WNKA.compute_pair', wnka_𝓁, this]
        congr! 1
        rw [← WeightedProduct.wProd_assoc]
        congr! 1
        generalize hL : A.take (i + 1) = L
        set R := A.drop (i + 1)
        have h₀ : A = L ++ R := by simp [← hL, R]
        have h₁ : i < L.length := by simp [← hL]; omega
        induction L using List.reverseRecOn with
        | nil => simp at h₁
        | append_singleton L α₁ ih =>
          simp only [List.append_assoc, List.singleton_append, WNKA.compute_pair', wnka_𝓁]
          grind

attribute [-simp] WeightedFinsum_range_succ WeightedFinsum_range_add in
theorem RPol.wnka_sem [Encodable F] [Encodable N] (p : RPol[F,N,𝒮]) : (RPol.wnka p).sem = G p := by
  if h : (𝟘 : 𝒮) = 𝟙 then ext; simp only [WeightedSemiring.if_zero_is_one_collapse h] else
  have h' : ¬𝟙 = (𝟘 : 𝒮) := by grind
  induction p with
  | Drop => exact wnka_sem_drop
  | Skip => exact wnka_sem_skip
  | Test t => exact wnka_sem_test
  | Mod π => exact wnka_sem_mod
  | Dup => exact wnka_sem_dup h' h
  | Add p₁ p₂ ih₁ ih₂ => rw [G, ← ih₁, ← ih₂]; exact wnka_sem_add
  | Weight w p ih => rw [G, ← ih]; exact wnka_sem_weight
  | Seq p₁ p₂ ih₁ ih₂ => exact wnka_sem_seq ih₁ ih₂
  | Iter p₁ ih => sorry

end WeightedNetKAT
