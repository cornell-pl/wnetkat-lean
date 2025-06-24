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

def S : Policy[F,𝒮] → Type
  | wnk_policy {drop} => I {♡}
  | wnk_policy {skip} => I {♡}
  | wnk_policy {@filter ~_} => I {♡}
  | wnk_policy {~_ ← ~_} => I {♡}
  | wnk_policy {dup} => I {♡, ♣}
  | wnk_policy {~_ ⨀ ~p₁} => S p₁
  | wnk_policy {~p₁ ⨁ ~p₂} => S p₁ ⊕ S p₂
  | wnk_policy {~p₁ ; ~p₂} => S p₁ ⊕ S p₂
  | wnk_policy {~p₁*} => S p₁
where I : (Set StateSpace) → Type := (↑·)

def S.decidableEq (p : Policy[F,𝒮]) : DecidableEq (S p) :=
  match p with
  | wnk_policy {drop} => Subtype.instDecidableEq
  | wnk_policy {skip} => Subtype.instDecidableEq
  | wnk_policy {@filter ¬~_}
  | wnk_policy {@filter ~(.Con _ _)}
  | wnk_policy {@filter ~(.Dis _ _)}
  | wnk_policy {@filter ~(.Test _ _)} => Subtype.instDecidableEq
  | wnk_policy {~_ ← ~_} => Subtype.instDecidableEq
  | wnk_policy {dup} => Subtype.instDecidableEq
  | wnk_policy {~_ ⨀ ~p₁} => S.decidableEq p₁
  | wnk_policy {~p₁ ⨁ ~p₂}
  | wnk_policy {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_policy {~p₁*} => S.decidableEq p₁

instance S.instDecidableEq {p : Policy[F,𝒮]} : DecidableEq (S p) := S.decidableEq p

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
        let sxy := mxy.finSupp.map ⟨fun (l, r) ↦ (Sum.inl l, Sum.inl r), by intro; grind⟩
        let sxw := mxw.finSupp.map ⟨fun (l, r) ↦ (Sum.inl l, Sum.inr r), by intro; grind⟩
        let szy := mzy.finSupp.map ⟨fun (l, r) ↦ (Sum.inr l, Sum.inl r), by intro; grind⟩
        let szw := mzw.finSupp.map ⟨fun (l, r) ↦ (Sum.inr l, Sum.inr r), by intro; grind⟩
        sxy ∪ sxw ∪ szy ∪ szw
      )
      (by
        simp only [_root_.W.supp_mem_iff, ne_eq, Finset.union_assoc, Finset.mem_union,
          Finset.mem_map, 𝒞.mem_finSupp_iff, Function.Embedding.coeFn_mk, Prod.exists, Prod.forall,
          Prod.mk.injEq, Sum.forall, Sum.elim_inl, Sum.inl.injEq, exists_eq_right_right,
          reduceCtorEq, and_false, exists_false, or_false, false_or, Sum.elim_inr, Sum.inr.injEq,
          exists_eq_right, implies_true, and_self])
notation "δ[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.δ a b c d

omit [DecidableEq Pk] [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
instance S.Fintype (p : Policy[F,𝒮]) : Fintype (S p) :=
  match p with
  | wnk_policy {drop} => ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_policy {skip} => ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_policy {@filter ¬~_}
  | wnk_policy {@filter ~(.Con _ _)}
  | wnk_policy {@filter ~(.Dis _ _)}
  | wnk_policy {@filter ~(.Test _ _)} => ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_policy {~_ ← ~_} => ⟨{⟨♡, by simp⟩}, by intro ⟨_, _⟩; simp; congr⟩
  | wnk_policy {dup} => ⟨{⟨♡, by simp⟩, ⟨♣, by simp⟩}, by rintro ⟨_, (h | h | h)⟩ <;> simp_all⟩
  | wnk_policy {~_ ⨀ ~p₁} => S.Fintype p₁
  | wnk_policy {~p₁ ⨁ ~p₂} =>
    have := S.Fintype p₁
    have := S.Fintype p₂
    instFintypeSum (S p₁) (S p₂)
  | wnk_policy {~p₁ ; ~p₂} =>
    have := S.Fintype p₁
    have := S.Fintype p₂
    instFintypeSum (S p₁) (S p₂)
  | wnk_policy {~p₁*} => S.Fintype p₁
instance S.instFintype {p : Policy[F,𝒮]} : _root_.Fintype (S p) := S.Fintype p
omit [DecidableEq Pk] [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
instance S.Finite {p : Policy[F,𝒮]} : Finite (S p) := Finite.of_fintype (S p)

variable [DecidableEq 𝒮]

def ι (p : Policy[F,𝒮]) : 𝒞 𝒮 (Unit × S p) := match p with
  | wnk_policy {drop} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {skip} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ¬~_} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Con _ _)} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Dis _ _)} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Test _ _)} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {~_ ← ~_} => η' ⟨(), ♡, rfl⟩
  | wnk_policy {dup} => η' ⟨(), ♡, by simp [S]⟩
  | wnk_policy {~w ⨀ ~p₁} => w • ι p₁
  | wnk_policy {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_policy {~p₁ ; ~p₂} => ι[ι p₁, 𝟘]
  | wnk_policy {~p₁*} => ι p₁

variable [Fintype Pk[F]]

def 𝓁 [DecidableEq 𝒮] (p : Policy[F,𝒮]) (α β : Pk[F]) : 𝒞 𝒮 (S p × Unit) :=
  match p with
  | wnk_policy {drop} => 𝟘
  | wnk_policy {skip} =>
    𝒞.mk'
      (fun ⟨⟨♡, _⟩, ()⟩ ↦ if α = β then 𝟙 else 𝟘)
      (if α = β ∧ (𝟙 : 𝒮) ≠ 𝟘 then Fintype.elems else ∅)
      (by simp +contextual [S, S.I]; rintro a ⟨_⟩ _; split_ifs <;> simp [Fintype.complete, *])
  | wnk_policy {@filter ~t} => 𝒞.mk' (fun _ ↦ if α = β ∧ t.test α then 𝟙 else 𝟘) sorry sorry
  | wnk_policy {~_ ← ~_} => sorry -- TODO
  | wnk_policy {dup} => 𝒞.mk' (fun ⟨s, ()⟩ ↦ if s.val = ♣ then if α = β then 𝟙 else 𝟘 else 𝟘) sorry sorry
  | wnk_policy {~_ ⨀ ~p₁} => 𝓁 p₁ α β
  | wnk_policy {~p₁ ⨁ ~p₂} => 𝓁[𝓁 p₁ α β, 𝓁 p₂ α β]
  | wnk_policy {~p₁ ; ~p₂} => 𝓁[⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ 𝓁 p₂ γ β), 𝓁 p₂ α β]
  | wnk_policy {~p₁*} => ⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₁ ⨯ 𝓁 p₁ γ β)

def δ (p : Policy[F,𝒮]) (α β : Pk[F]) : 𝒞 𝒮 (S p × S p) := match p with
  | wnk_policy {drop} => 𝟘
  | wnk_policy {skip} => 𝟘
  | wnk_policy {@filter ~_} => 𝟘
  | wnk_policy {~_ ← ~_} => 𝟘
  | wnk_policy {dup} => 𝒞.liftPi fun s ↦ if s.val = ♡ ∧ α = β then η' ⟨♣, by simp [S]⟩ else 𝟘
  | wnk_policy {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_policy {~p₁ ⨁ ~p₂} =>
      δ[[δ p₁ α β,    𝟘],
        [𝟘,           δ p₂ α β]]
  | wnk_policy {~p₁ ; ~p₂} =>
      δ[[δ p₁ α β,    ⨁ᶠ γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ δ p₂ γ β)],
        [𝟘,           δ p₂ α β]]
  | wnk_policy {~p₁*} => δ p₁ α β ⨁ (⨁ᶠ γ, 𝓁 p₁ α γ ⨯ ι p₁)

example {a : Prop} : ¬¬a ↔ a := by exact not_not

def Policy.wnka (p : Policy[F,𝒮]) : WNKA F 𝒮 (S p) where
  ι := ι p
  δ := δ p
  𝓁 := 𝓁 p

def List.pairs {α : Type} (l : List α) : List (α × α) := l.zip l.tail

#eval List.pairs (List.range 10)

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

theorem WeightedProduct.wProd_assoc {X Y Z W : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (a : 𝒞 𝒮 (X × Y))
    (b : 𝒞 𝒮 (Y × Z))
    (c : 𝒞 𝒮 (Z × W)) :
    (a ⨯ b ⨯ c) = (a ⨯ (b ⨯ c)) := by
  ext ⟨x, w⟩
  simp [WeightedProduct.wProd]
  simp [← WeightedFinsum_mul_left]
  sorry

theorem WeightedProduct.wProd_apply {X Y Z : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : 𝒞 𝒮 (X × Y))
    (b : 𝒞 𝒮 (Y × Z))
    (x : X × Z) :
    (a ⨯ b) x = sorry := by
  simp [wProd]
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

-- example {A A' B B' C C' D D' : Type} {X : 𝒞 𝒮 (A × B)} {Y : 𝒞 𝒮 (B × C)} {Z : 𝒞 𝒮 (A × D)} {W : 𝒞 𝒮 (D × C)} : True := by
--   let a := S[X,Y]
--   let b := S[Z,W]
--   -- let a := S[X,Y].equiv (e:=Equiv.prodSumDistrib _ _ _)
--   -- let b := S[Z,W].equiv (e:=Equiv.sumProdDistrib _ _ _)
--   -- have := a ⨯ b
--   let c := X ⨯ Y
--   let d := Z ⨯ W
--   have : (S[X,Y] ⨯ S[Z,W]) = (X ⨯ Y) ⨁ (Z ⨯ W) := sorry
--   sorry

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
theorem Policy.wnka_sem [Fintype F] [DecidableEq F] (p : Policy[F,𝒮]) : (Policy.wnka p).sem = G p := by
  if h : (𝟘 : 𝒮) = 𝟙 then sorry else
  have h' : ¬𝟙 = (𝟘 : 𝒮) := by grind
  induction p with
  | Filter t =>
    cases t with
    | Bool b =>
      cases b
      · ext x
        simp [G]
        induction x using GS.induction
        next α α₀ =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁]
        next α α₀ α₁ =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, 𝓁]
        next α A αn =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, 𝓁]
      · ext x
        simp [G]
        induction x using GS.induction
        next α α₀ =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, ι, 𝓁]
          sorry
        next α α₀ α₁ =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, ι, 𝓁, δ, h]
          sorry
        next α A αn =>
          simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, ι, 𝓁, δ]
          rw [List.foldl_const]
          simp
          cases A
          · simp_all; sorry--; grind
          · simp [List.length_cons, -Function.iterate_succ, Function.comp_apply, ne_eq,
            reduceCtorEq, not_false_eq_true, List.getLast_cons]
            sorry
            -- grind
    | _ => sorry
  | Dup =>
    sorry
    -- ext S
    -- induction S using GS.induction
    -- next α α₀ =>
    --   simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, ι]
    --   simp [𝓁]
    --   simp_all [G, GS.mk]
    --   grind
    -- next α α₀ α₁ =>
    --   simp [wnka, WNKA.sem, GS.mk, GS.compute, List.pairs, WeightedProduct.wProd_assoc]
    --   simp [δ, 𝒞.liftPi]
    --   simp [𝓁]
    --   simp [ι]
    --   simp [δ]
    -- -- simp [wnka, WNKA.sem]
    -- -- simp only [DFunLike.coe]
    -- -- simp
    -- -- apply S.cases₀₁ₙ
    -- -- · rintro α α₀ ⟨_⟩
    -- --   simp [GS.mk, GS.compute, List.pairs]
    -- --   simp [ι]
    -- --   magic_simp
    -- --   simp
    -- --   simp [𝓁]
    -- --   magic_simp
    -- --   simp [G]
    -- --   simp_all [GS.mk]
    -- --   grind
    -- -- · rintro α α₀ α₁ ⟨_⟩
    -- --   simp [GS.mk, GS.compute, List.pairs]
    -- --   simp [ι]
    -- --   magic_simp
    -- --   simp
    -- --   simp [𝓁]
    -- --   magic_simp
    -- --   simp [WeightedProduct.wProd]
    -- --   magic_simp
    -- --   simp
    -- --   rw [WeightedSum_finite]
    -- --   sorry

    -- -- simp only [WNKA.sem, wnka, 𝒞.apply_subtype, G]
    -- -- simp only [DFunLike.coe]
    -- -- simp only [𝒞.apply_subtype]
    -- -- split_ifs with h
    -- -- · obtain ⟨α, hα⟩ := h
    -- --   subst_eqs
    -- --   simp [GS.mk, GS.compute, List.pairs]
    -- --   simp [ι, δ]
    -- --   simp [𝓁]
    -- --   magic_simp
    -- --   simp
    -- --   simp
    -- -- · simp_all
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
  | _ => sorry

end WeightedNetKAT
