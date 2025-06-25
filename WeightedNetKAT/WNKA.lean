import WeightedNetKAT.Language

namespace WeightedNetKAT

variable {F : Type} [DecidableEq Pk[F]] [Encodable Pk[F]]
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs.
- `𝓁` is a family of output weightings `𝓁[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that we
  use 𝓁 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F 𝒮 Q: Type)
    [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
where
  /-- `ι` is the initial weightings. -/
  ι : 𝒞 𝒮 (Unit × Q)
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒞 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F]) → 𝒞 𝒮 (Q × Q)
  /-- `𝓁` is a family of output weightings `𝓁[α,β] : 𝒞 𝒮 Q` indexed by packet pairs. Note that
    we use 𝓁 instead of λ, since λ is the function symbol in Lean. -/
  𝓁 : (α β : Pk[F]) → 𝒞 𝒮 (Q × Unit)

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

inductive StateSpace where
  | Heart
  | Club
deriving DecidableEq

notation "♡" => StateSpace.Heart
notation "♣" => StateSpace.Club

def S : RPol[F,𝒮] → Type
  | wnk_rpol {drop} => I {♡}
  | wnk_rpol {skip} => I {♡}
  | wnk_rpol {@test ~_} => I {♡}
  | wnk_rpol {@mod ~_} => I {♡}
  | wnk_rpol {dup} => I {♡, ♣}
  | wnk_rpol {¬ ~_} => I {♡}
  | wnk_rpol {~_ ⨀ ~p₁} => S p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁ ; ~p₂} => S p₁ ⊕ S p₂
  | wnk_rpol {~p₁*} => S p₁
where I : (Set StateSpace) → Type := (↑·)

def S.decidableEq (p : RPol[F,𝒮]) : DecidableEq (S p) :=
  match p with
  | wnk_rpol {drop} => Subtype.instDecidableEq
  | wnk_rpol {skip} => Subtype.instDecidableEq
  | wnk_rpol {@test ~_}
  | wnk_rpol {@mod ~_} => Subtype.instDecidableEq
  | wnk_rpol {dup} => Subtype.instDecidableEq
  | wnk_rpol {¬~_} => Subtype.instDecidableEq
  | wnk_rpol {~_ ⨀ ~p₁} => S.decidableEq p₁
  | wnk_rpol {~p₁ ⨁ ~p₂}
  | wnk_rpol {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_rpol {~p₁*} => S.decidableEq p₁

instance S.instDecidableEq {p : RPol[F,𝒮]} : DecidableEq (S p) := S.decidableEq p

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

omit [DecidableEq Pk] [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
instance S.Fintype (p : RPol[F,𝒮]) : Fintype (S p) :=
  match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} | wnk_rpol {¬~_} =>
    ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_rpol {dup} => ⟨{⟨♡, by simp⟩, ⟨♣, by simp⟩}, by rintro ⟨_, (h | h | h)⟩ <;> simp_all⟩
  | wnk_rpol {~_ ⨀ ~p₁} => S.Fintype p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => letI := S.Fintype p₁; letI := S.Fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁ ; ~p₂} => letI := S.Fintype p₁; letI := S.Fintype p₂; instFintypeSum _ _
  | wnk_rpol {~p₁*} => S.Fintype p₁
instance S.instFintype {p : RPol[F,𝒮]} : _root_.Fintype (S p) := S.Fintype p
omit [DecidableEq Pk] [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
instance S.Finite {p : RPol[F,𝒮]} : Finite (S p) := Finite.of_fintype (S p)

variable [DecidableEq 𝒮]

def ι (p : RPol[F,𝒮]) : 𝒞 𝒮 (Unit × S p) := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {¬~_} | wnk_rpol {@mod ~_} =>
    η' ⟨(), ♡, rfl⟩
  | wnk_rpol {dup} => η' ⟨(), ♡, by simp⟩
  | wnk_rpol {~w ⨀ ~p₁} => w • ι p₁
  | wnk_rpol {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_rpol {~p₁ ; ~p₂} => ι[ι p₁, 𝟘]
  | wnk_rpol {~p₁*} => ι p₁

variable [Fintype Pk[F]]

def 𝓁 [DecidableEq 𝒮] (p : RPol[F,𝒮]) (α β : Pk[F]) : 𝒞 𝒮 (S p × Unit) :=
  match p with
  | wnk_rpol {drop} => 𝟘
  | wnk_rpol {skip} => if α = β then 𝟙 else 𝟘
  | wnk_rpol {@test ~γ} => if α = β ∧ β = γ then 𝟙 else 𝟘
  | wnk_rpol {¬~γ} => if α = β ∧ β ≠ γ then 𝟙 else 𝟘
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

def δ (p : RPol[F,𝒮]) (α β : Pk[F]) : 𝒞 𝒮 (S p × S p) := match p with
  | wnk_rpol {drop} | wnk_rpol {skip} | wnk_rpol {@test ~_} | wnk_rpol {@mod ~_} | wnk_rpol {¬ ~_} =>
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

def RPol.wnka (p : RPol[F,𝒮]) : WNKA F 𝒮 (S p) where
  ι := ι p
  δ := δ p
  𝓁 := 𝓁 p

def List.pairs {α : Type} (l : List α) : List (α × α) := l.zip l.tail

def GS.pks (s : GS F) : List Pk[F] := s.1 :: s.2.1 ++ [s.2.2]

def GS.compute {Q : Type} [DecidableEq Q] (𝒜 : WNKA F 𝒮 Q) (s : GS F) : 𝒮 :=
  match _ : s with
  | ⟨α, [], α₀⟩ => (𝒜.ι ⨯ 𝒜.𝓁 α α₀) ((), ())
  | ⟨α, [α₀], α₁⟩ => (𝒜.ι ⨯ 𝒜.δ α α₀ ⨯ 𝒜.𝓁 α₀ α₁) ((), ())
  | ⟨α, α₀::α₁::A, αn⟩ => (𝒜.ι ⨯ (List.pairs (α₀ :: α₁ :: A) |>.foldl (fun acc (α', β') ↦ acc ⨯ 𝒜.δ α' β') (𝒜.δ α α₀)) ⨯ 𝒜.𝓁 ((α₁ :: A).getLast (by simp)) αn) ((), ())
  -- g ((List.pairs (s.1 :: s.2.1)).foldl f init) ((s.1 :: s.2.1).getLast (by simp), s.2.2)

def WNKA.sem {Q : Type} [DecidableEq Q] (𝒜 : WNKA F 𝒮 Q) : 𝒲 𝒮 (GS F) := 𝒲.mk
  (fun x ↦ x.compute 𝒜)
  sorry

@[simp]
theorem asdasd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] {x : X × Y} (m : 𝒞 𝒮 (Y × Z)) :
    (η' (𝒮:=𝒮) x ⨯ m) = (𝒞.mk' (fun y ↦ if y.1 = x.1 then m (x.2, y.2) else 𝟘) sorry sorry : 𝒞 𝒮 (X × Z)) := by
  if h : ((𝟙 : 𝒮) ≠ 𝟘) then
    ext y
    simp [WeightedProduct.wProd]
    magic_simp
    simp
    rw [WeightedFinsum_single x]
    · simp_all [η']
    · simp_all [η']
    · simp_all
  else
    ext ⟨x, z⟩
    simp at h
    simp [WeightedSemiring.if_one_is_zero_collapse h]

@[simp]
theorem WeightedProduct.wProd_wZero {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : 𝒞 𝒮 (X × Y)) :
    (a ⨯ (𝟘 : 𝒞 𝒮 (Y × Z))) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]
@[simp]
theorem WeightedProduct.wZero_wProd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : 𝒞 𝒮 (Y × Z)) :
    ((𝟘 : 𝒞 𝒮 (X × Y)) ⨯ a) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
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

theorem WeightedProduct.wProd_assoc {X Y Z W : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
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

theorem WeightedProduct.wProd_apply {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : 𝒞 𝒮 (X × Y))
    (b : 𝒞 𝒮 (Y × Z))
    (x : X × Z) :
    (a ⨯ b) x = sorry := by
  simp [wProd]
  simp [WeightedFinsum_ite]
  sorry
theorem WeightedProduct.wProd_apply' {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (f : (X × Y) → 𝒮)
    (b : 𝒞 𝒮 (Y × Z))
    (x : X × Z) :
    WeightedProduct.wProd (α:=𝒞 𝒮 (X × Y)) (β:=𝒞 𝒮 (Y × Z)) ⟨⟨f, sorry⟩, sorry, sorry⟩ b x = sorry := by
  simp [wProd]
  sorry
omit [DecidableEq Pk] [Encodable Pk] [Fintype Pk] in
theorem GS.induction (P : GS F → Prop)
    (h₀ : ∀ α α₀, P gs[α; α₀])
    (h₁ : ∀ α α₀ α₁, P gs[α; α₀; dup; α₁])
    (hn : ∀ α α₀ α₁ A αₙ, P (GS.mk α (α₀ :: α₁ :: A) αₙ))
    (x : GS F) :
    P x := by
  obtain ⟨α, A, αn⟩ := x
  match A with
  | [] => exact h₀ α αn
  | [α'] => exact h₁ α α' αn
  | α' :: α'' :: A => exact hn α α' α'' A αn

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem WeightedZero.instPi_apply {X 𝒮 : Type} [WeightedZero 𝒮] (x : X) : (𝟘 : X → 𝒮) x = 𝟘 := rfl
omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] [DecidableEq 𝒮] in
@[simp] theorem WeightedZero.instCountablePi_apply {X : Type} (x : X) : (𝟘 : 𝒞 𝒮 X) x = 𝟘 := rfl

@[simp]
theorem asdasdas {X : Type} {n : ℕ} : (fun (_ : 𝒞 𝒮 X) ↦ (WeightedZero.wZero (α:=𝒞 𝒮 X)))^[n + 1] = 𝟘 := by
  induction n with
  | zero => simp_all; rfl
  | succ => simp_all; rfl

theorem ι_wProd_𝓁 {A B : Type} [DecidableEq A] [DecidableEq B] {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)} {Z : 𝒞 𝒮 (A × Unit)} {W : 𝒞 𝒮 (B × Unit)} :
    (ι[X, Y] ⨯ 𝓁[Z, W]) = (X ⨯ Z) ⨁ (Y ⨯ W) := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd]
  sorry
theorem ι_wProd_δ {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)}
    {Z : 𝒞 𝒮 (A × C)} {W : 𝒞 𝒮 (A × D)}
    {U : 𝒞 𝒮 (B × C)} {V : 𝒞 𝒮 (B × D)}
    :
    (ι[X, Y] ⨯ δ[[Z, W], [U, V]]) = ι[X ⨯ Z, X ⨯ W] ⨁ ι[Y ⨯ U, Y ⨯ V] := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd]
  sorry
theorem ι_wProd_δ' {A B C D : Type}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {X : 𝒞 𝒮 (Unit × A)} {Y : 𝒞 𝒮 (Unit × B)}
    {Z : 𝒞 𝒮 (A × C)} {W : 𝒞 𝒮 (A × D)}
    {U : 𝒞 𝒮 (B × C)} {V : 𝒞 𝒮 (B × D)}
    :
    (ι[X, Y] ⨯ δ[[Z, W], [U, V]]) = ι[X ⨯ Z ⨁ Y ⨯ U, X ⨯ W ⨁ Y ⨯ V] := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd]
  sorry

open scoped Classical in
theorem RPol.wnka_sem [Fintype F] [DecidableEq F] (p : RPol[F,𝒮]) : (RPol.wnka p).sem = G p := by
  if h : (𝟘 : 𝒮) = 𝟙 then sorry else
  have h' : ¬𝟙 = (𝟘 : 𝒮) := by grind
  induction p with
  | Drop =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      simp only [WNKA.sem, GS.compute, wnka, ι, 𝓁, WeightedProduct.wProd_wZero, 𝒞.wZero_apply,
        asdasd, 𝒞.mk', ↓reduceIte, GS.mk, 𝒲.mk_apply]
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply]
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Skip =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      -- TODO: simp?
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      split_ifs with h₁ h₂ h₃ <;> simp_all
      grind
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply, right_eq_ite_iff]
      grind
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Test t =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      -- TODO: simp?
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      split_ifs
      · simp
      · grind only
      · grind only
      · rfl
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply, right_eq_ite_iff]
      grind
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Neg t =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      -- TODO: simp?
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      split_ifs with h₁ h₂ h₃
      · simp
      · simp_all only [not_exists, not_and, Decidable.not_not, 𝒞.wOne_apply, not_true_eq_false,
        and_false]
      · grind [𝒞.wZero_apply]
      · rfl
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply, right_eq_ite_iff]
      grind
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Mod π =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      -- TODO: simp?
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      split_ifs with h₁ h₂ h₃ <;> simp_all
      grind
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply, right_eq_ite_iff]
      grind
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Dup =>
    ext x
    simp [G]
    induction x using GS.induction
    next α α₀ =>
      -- TODO: simp?
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      sorry
    next α α₀ α₁ =>
      simp [WNKA.sem, GS.compute, wnka, WeightedProduct.wProd_wZero,
        WeightedProduct.wZero_wProd, 𝒞.wZero_apply, GS.mk, 𝒲.mk_apply, right_eq_ite_iff]
      simp [δ]
      simp [ι]
      sorry
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, δ]
      sorry
  | Add p₁ p₂ ih₁ ih₂ =>
    ext S
    induction S using GS.induction
    next α α₀ =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs]
      simp [G]
      simp [ι]
      simp [𝓁]
      rw [← ih₁, ← ih₂]; clear ih₁ ih₂
      simp [wnka, WNKA.sem]
      simp [GS.compute]
      rw [ι_wProd_𝓁]; rfl
    next α α₀ α₁ =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs]
      simp [G]
      simp [ι]
      simp [𝓁]
      simp [δ]
      rw [← ih₁, ← ih₂]; clear ih₁ ih₂
      simp [wnka, WNKA.sem]
      simp [GS.compute]
      rw [ι_wProd_δ']
      simp
      rw [ι_wProd_𝓁]
      rfl
    next α α₀ α₁ α₂ A =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs]
      simp [G]
      simp [ι]
      simp [𝓁]
      simp [δ]
      rw [← ih₁, ← ih₂]; clear ih₁ ih₂
      simp [wnka, WNKA.sem]
      sorry
  | Weight w p ih =>
    ext x
    simp [G]
    rw [← ih]
    induction x using GS.induction
    next α α₀ =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁, ι]
      sorry
    next α α₀ α₁ =>
      simp only [WNKA.sem, GS.compute, wnka, δ, GS.mk, 𝒲.mk_apply, ι, 𝓁]
      sorry
    next α A αn =>
      simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, ι, 𝓁]
      sorry
  | _ => sorry

end WeightedNetKAT
