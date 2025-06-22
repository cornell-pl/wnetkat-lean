import WeightedNetKAT.Language

namespace WeightedNetKAT

variable {F : Type} [DecidableEq Pk[F]] [Encodable Pk[F]]
variable {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]

/-- Weighted NetKAT Automaton.

- `Q` is a set of states.
- `ι` is the initial weightings.
- `δ` is a family of transition functions `δ[α,β] : Q → 𝒲 𝒮 Q` indexed by packet pairs.
- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒲 𝒮 Q` indexed by packet pairs. Note that we
  use 𝒪 instead of λ, since λ is the function symbol in Lean.
-/
structure WNKA (F 𝒮 Q: Type)
    [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮]
where
  /-- `ι` is the initial weightings. -/
  ι : 𝒲 𝒮 (Unit × Q)
  /-- `δ` is a family of transition functions `δ[α,β] : Q → 𝒲 𝒮 Q` indexed by packet pairs. -/
  δ : (α β : Pk[F]) → 𝒲 𝒮 (Q × Q)
  /-- `𝒪` is a family of output weightings `𝒪[α,β] : 𝒲 𝒮 Q` indexed by packet pairs. Note that
    we use 𝒪 instead of λ, since λ is the function symbol in Lean. -/
  𝒪 : (α β : Pk[F]) → 𝒲 𝒮 (Q × Unit)

class WeightedProduct (α : Type) (β : Type) (γ : outParam Type) where
  wProd : α → β → γ

infixl:70 " ⨯ " => WeightedProduct.wProd

-- open scoped Classical in
-- TODO: make this computable once we parameterize the support of 𝒲 to be countable or finite
noncomputable instance {X Y Z : Type} [DecidableEq X] : WeightedProduct (𝒲 𝒮 (X × Y)) (𝒲 𝒮 (Y × Z)) (𝒲 𝒮 (X × Z)) where
  wProd m m' := ⟨
    fun (x, z) ↦ ⨁' p : m.supp, let (x', y) := p.val; if x = x' then m ⟨x, y⟩ ⨀ m' (y, z) else 𝟘,
    sorry
  ⟩

-- notation "♡" => Idk.Heart
-- notation "♣" => Idk.Club

-- def S : Policy[F,𝒮] → Set Idk
--   | wnk_policy {drop} => {♡}
--   | wnk_policy {skip} => {♡}
--   | wnk_policy {@filter ~_} => {♡}
--   | wnk_policy {~_ ← ~_} => {♡}
--   | wnk_policy {dup} => {♡,♣}
--   | wnk_policy {~_ ⨀ ~p₁} => S p₁
--   | wnk_policy {~p₁ ⨁ ~p₂} => S p₁ ∪ S p₂
--   | wnk_policy {~p₁ ; ~p₂} => S p₁ ∪ S p₂
--   | wnk_policy {~p₁*} => S p₁

inductive StateSpace where
  | Heart
  | Club
  | Prod (α β : StateSpace)
  | Sum (α β : StateSpace)
deriving DecidableEq

notation "♡" => StateSpace.Heart
notation "♣" => StateSpace.Club
-- notation "♡♣" => StateSpace.HeartAndClub

@[simp] instance : Mul StateSpace := ⟨.Prod⟩
@[simp] instance : Add StateSpace := ⟨.Sum⟩

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
  | wnk_policy {~p₁ ⨁ ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_policy {~p₁ ; ~p₂} =>
    have := S.decidableEq p₁
    have := S.decidableEq p₂
    instDecidableEqSum
  | wnk_policy {~p₁*} => S.decidableEq p₁

instance S.instDecidableEq {p : Policy[F,𝒮]} : DecidableEq (S p) := S.decidableEq p

instance {X : Type} : SMul 𝒮 (𝒲 𝒮 X) := sorry

def S.ι {X Y : Type} : 𝒲 𝒮 (Unit × X) → 𝒲 𝒮 (Unit × Y) → 𝒲 𝒮 (Unit × (X ⊕ Y)) :=
  fun m₁ m₂ ↦ ⟨fun ⟨_, x⟩ ↦ match x with | .inl x => m₁ ((), x) | .inr y => m₂ ((), y), by sorry⟩
notation "ι[" a "," b"]" => S.ι a b
def S.𝓁 {X Y : Type} : 𝒲 𝒮 (X × Unit) → 𝒲 𝒮 (Y × Unit) → 𝒲 𝒮 ((X ⊕ Y) × Unit) :=
  fun m₁ m₂ ↦ ⟨fun ⟨x, _⟩ ↦ match x with | .inl x => m₁ (x, ()) | .inr y => m₂ (y, ()), by sorry⟩
notation "𝓁[" a "," b"]" => S.𝓁 a b
def S.δ {X Y Z W : Type} :
    𝒲 𝒮 (X × Y) →
    𝒲 𝒮 (X × W) →
    𝒲 𝒮 (Z × Y) →
    𝒲 𝒮 (Z × W) →
    𝒲 𝒮 ((X ⊕ Z) × (Y ⊕ W)) :=
  fun mxy mxw mzy mzw ↦ ⟨fun ⟨xz, yw⟩ ↦
    match xz, yw with
    | .inl x, .inl y => mxy (x, y)
    | .inl x, .inr w => mxw (x, w)
    | .inr z, .inl y => mzy (z, y)
    | .inr z, .inr w => mzw (z, w), by sorry⟩
notation "δ[" "[" a "," b "]" "," "[" c "," d "]" "]" => S.δ a b c d

omit [DecidableEq Pk] [WeightedSemiring 𝒮] [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
instance S.Finite {p : Policy[F,𝒮]} : Finite (S p) := by
  induction p with try simp_all [S, S.I] <;> try exact inferInstance
  | Filter t =>
    cases t <;> try simp_all [S, S.I, Finite.of_subsingleton]
    rename_i b; cases b <;> simp_all [S, S.I, Finite.of_subsingleton]

def ι (p : Policy[F,𝒮]) : 𝒲 𝒮 (Unit × S p) := match p with
  | wnk_policy {drop} => η ⟨(), ♡, rfl⟩
  | wnk_policy {skip} => η ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ¬~_} => η ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Con _ _)} => η ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Dis _ _)} => η ⟨(), ♡, rfl⟩
  | wnk_policy {@filter ~(.Test _ _)} => η ⟨(), ♡, rfl⟩
  | wnk_policy {~_ ← ~_} => η ⟨(), ♡, rfl⟩
  | wnk_policy {dup} => η ⟨(), ♡, by simp [S]⟩
  | wnk_policy {~w ⨀ ~p₁} => w • ι p₁
  | wnk_policy {~p₁ ⨁ ~p₂} => ι[ι p₁, ι p₂]
  | wnk_policy {~p₁ ; ~p₂} => ι[ι p₁, 𝟘]
  | wnk_policy {~p₁*} => ι p₁

noncomputable def 𝓁 (p : Policy[F,𝒮]) (α β : Pk[F]) : 𝒲 𝒮 (S p × Unit) :=
  match p with
  | wnk_policy {drop} => 𝟘
  | wnk_policy {skip} => ⟨fun ⟨⟨♡, _⟩, ()⟩ ↦ if α = β then 𝟙 else 𝟘, SetCoe.countable _⟩
  | wnk_policy {@filter ~t} => ⟨fun _ ↦ if α = β ∧ t.test α then 𝟙 else 𝟘, SetCoe.countable _⟩
  | wnk_policy {~_ ← ~_} => sorry -- TODO
  | wnk_policy {dup} => ⟨fun ⟨s, ()⟩ ↦ if s.val = ♣ then if α = β then 𝟙 else 𝟘 else 𝟘, SetCoe.countable _⟩
  | wnk_policy {~_ ⨀ ~p₁} => 𝓁 p₁ α β
  | wnk_policy {~p₁ ⨁ ~p₂} => 𝓁[𝓁 p₁ α β, 𝓁 p₂ α β]
  | wnk_policy {~p₁ ; ~p₂} => 𝓁[⨁' γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ 𝓁 p₂ γ β), 𝓁 p₂ α β]
  | wnk_policy {~p₁*} => ⨁' γ, (𝓁 p₁ α γ ⨯ ι p₁ ⨯ 𝓁 p₁ γ β)

noncomputable def δ (p : Policy[F,𝒮]) (α β : Pk[F]) : 𝒲 𝒮 (S p × S p) := match p with
  | wnk_policy {drop} => 𝟘
  | wnk_policy {skip} => 𝟘
  | wnk_policy {@filter ~_} => 𝟘
  | wnk_policy {~_ ← ~_} => 𝟘
  | wnk_policy {dup} => 𝒲.liftPi fun s ↦ if s.val = ♡ ∧ α = β then η ⟨♣, by simp [S]⟩ else 𝟘
  | wnk_policy {~_ ⨀ ~p₁} => δ p₁ α β
  | wnk_policy {~p₁ ⨁ ~p₂} =>
      δ[[δ p₁ α β,    𝟘],
        [𝟘,           δ p₂ α β]]
  | wnk_policy {~p₁ ; ~p₂} =>
      δ[[δ p₁ α β,    ⨁' γ, (𝓁 p₁ α γ ⨯ ι p₂ ⨯ δ p₂ γ β)],
        [𝟘,           δ p₂ α β]]
  | wnk_policy {~p₁*} => δ p₁ α β ⨁ (⨁' γ, 𝓁 p₁ α γ ⨯ ι p₁)

example {a : Prop} : ¬¬a ↔ a := by exact not_not

noncomputable def Policy.wnka (p : Policy[F,𝒮]) : WNKA F 𝒮 (S p) where
  ι := ι p
  δ := δ p
  𝒪 := 𝓁 p

def List.pairs {α : Type} (l : List α) : List (α × α) := l.zip l.tail

#eval List.pairs (List.range 10)

def GS.pks (s : GS F) : List Pk[F] := s.1 :: s.2.1 ++ [s.2.2]

noncomputable def GS.compute {Q : Type} [DecidableEq Q] (𝒜 : WNKA F 𝒮 Q) (s : GS F) : 𝒮 :=
  match _ : s with
  | ⟨α, [], α₀⟩ => (𝒜.ι ⨯ 𝒜.𝒪 α α₀) ((), ())
  | ⟨α, [α₀], α₁⟩ => (𝒜.ι ⨯ 𝒜.δ α α₀ ⨯ 𝒜.𝒪 α₀ α₁) ((), ())
  | ⟨α, α₀::α₁::A, αn⟩ => (𝒜.ι ⨯ (List.pairs (α₀ :: α₁ :: A) |>.foldl (fun acc (α', β') ↦ acc ⨯ 𝒜.δ α' β') (𝒜.δ α α₀)) ⨯ 𝒜.𝒪 ((α₁ :: A).getLast (by simp)) αn) ((), ())
  -- g ((List.pairs (s.1 :: s.2.1)).foldl f init) ((s.1 :: s.2.1).getLast (by simp), s.2.2)

noncomputable def WNKA.sem {Q : Type} [DecidableEq Q] (𝒜 : WNKA F 𝒮 Q) : 𝒲 𝒮 (GS F) := ⟨fun x ↦
  x.compute 𝒜,
  -- let z := x.foldl 𝒜.ι (fun m (α, β) ↦ m ⨯ 𝒜.δ α β) (fun m (α, β) ↦ m ⨯ 𝒜.𝒪 α β)
  -- z ((), ()),
  sorry⟩

@[simp]
theorem asdasd {X Y Z : Type} [DecidableEq X] [DecidableEq Y] {x : X × Y} (m : 𝒲 𝒮 (Y × Z)) :
    (η (𝒮:=𝒮) x ⨯ m) = (⟨fun y ↦ if y.1 = x.1 then m (x.2, y.2) else 𝟘, sorry⟩ : 𝒲 𝒮 (X × Z)) := by
  if h : ((𝟙 : 𝒮) ≠ 𝟘) then
    ext y
    simp [WeightedProduct.wProd]
    magic_simp
    simp
    have : (η (𝒮:=𝒮) x).supp = {x} := by
      ext
      simp_all [η, 𝒲.supp, eq_comm]
    have : Finite ↑(η (𝒮:=𝒮) x).supp := by simp_all [Finite.of_subsingleton]
    rw [WeightedSum_finite]
    rw [WeightedFinsum_single ⟨x, by simp_all⟩]
    · simp_all [η]
    · simp_all
    · simp_all
  else
    ext
    simp_all
    sorry

@[simp]
theorem WeightedProduct.wProd_wZero {X Y Z : Type} [DecidableEq X] [DecidableEq Y]
    (a : 𝒲 𝒮 (X × Y)) :
    (a ⨯ (𝟘 : 𝒲 𝒮 (Y × Z))) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]
@[simp]
theorem WeightedProduct.wZero_wProd {X Y Z : Type} [DecidableEq X] [DecidableEq Y]
    (a : 𝒲 𝒮 (Y × Z)) :
    ((𝟘 : 𝒲 𝒮 (X × Y)) ⨯ a) = 𝟘 := by
  ext ⟨x, Z⟩; simp [WeightedProduct.wProd]

theorem WeightedProduct.wProd_assoc {X Y Z W : Type} [DecidableEq X] [DecidableEq Y]
    (a : 𝒲 𝒮 (X × Y))
    (b : 𝒲 𝒮 (Y × Z))
    (c : 𝒲 𝒮 (Z × W)) :
    (a ⨯ b ⨯ c) = (a ⨯ (b ⨯ c)) := by
  ext ⟨x, w⟩
  simp [WeightedProduct.wProd]
  simp [← WeightedSum_mul_left]
  sorry

theorem WeightedProduct.wProd_apply {X Y Z : Type} [DecidableEq X] [DecidableEq Y]
    (a : 𝒲 𝒮 (X × Y))
    (b : 𝒲 𝒮 (Y × Z))
    (x : X × Z) :
    (a ⨯ b) x = sorry := by
  simp [wProd]
  sorry
theorem WeightedProduct.wProd_apply' {X Y Z : Type} [DecidableEq X] [DecidableEq Y]
    (f : (X × Y) → 𝒮)
    (b : 𝒲 𝒮 (Y × Z))
    (x : X × Z) :
    WeightedProduct.wProd (α:=𝒲 𝒮 (X × Y)) (β:=𝒲 𝒮 (Y × Z)) ⟨f, sorry⟩ b x = sorry := by
  simp [wProd]
  sorry
omit [DecidableEq Pk] [Encodable Pk] in
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

attribute [- simp] WeightedZero.instCountablePi

omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp] theorem WeightedZero.instPi_apply {X 𝒮 : Type} [WeightedZero 𝒮] (x : X) : (𝟘 : X → 𝒮) x = 𝟘 := rfl
@[simp] theorem WeightedZero.instCountablePi_apply {X : Type} (x : X) : (𝟘 : 𝒲 𝒮 X) x = 𝟘 := rfl

@[simp]
theorem asdasdas {X : Type} {n : ℕ} : (fun (_ : 𝒲 𝒮 X) ↦ (WeightedZero.wZero (α:=𝒲 𝒮 X)))^[n + 1] = 𝟘 := by
  induction n with
  | zero => simp_all; rfl
  | succ => simp_all; rfl

-- example {A A' B B' C C' D D' : Type} {X : 𝒲 𝒮 (A × B)} {Y : 𝒲 𝒮 (B × C)} {Z : 𝒲 𝒮 (A × D)} {W : 𝒲 𝒮 (D × C)} : True := by
--   let a := S[X,Y]
--   let b := S[Z,W]
--   -- let a := S[X,Y].equiv (e:=Equiv.prodSumDistrib _ _ _)
--   -- let b := S[Z,W].equiv (e:=Equiv.sumProdDistrib _ _ _)
--   -- have := a ⨯ b
--   let c := X ⨯ Y
--   let d := Z ⨯ W
--   have : (S[X,Y] ⨯ S[Z,W]) = (X ⨯ Y) ⨁ (Z ⨯ W) := sorry
--   sorry

theorem ι_wProd_𝓁 {A B : Type} {X : 𝒲 𝒮 (Unit × A)} {Y : 𝒲 𝒮 (Unit × B)} {Z : 𝒲 𝒮 (A × Unit)} {W : 𝒲 𝒮 (B × Unit)} :
    (ι[X, Y] ⨯ 𝓁[Z, W]) = (X ⨯ Z) ⨁ (Y ⨯ W) := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd]
  sorry
theorem ι_wProd_δ {A B C D : Type}
    {X : 𝒲 𝒮 (Unit × A)} {Y : 𝒲 𝒮 (Unit × B)}
    {Z : 𝒲 𝒮 (A × C)} {W : 𝒲 𝒮 (A × D)}
    {U : 𝒲 𝒮 (B × C)} {V : 𝒲 𝒮 (B × D)}
    :
    (ι[X, Y] ⨯ δ[[Z, W], [U, V]]) = ι[X ⨯ Z, X ⨯ W] ⨁ ι[Y ⨯ U, Y ⨯ V] := by
  ext a
  simp [WeightedAdd.wAdd]
  simp [WeightedProduct.wProd]
  sorry
theorem ι_wProd_δ' {A B C D : Type}
    {X : 𝒲 𝒮 (Unit × A)} {Y : 𝒲 𝒮 (Unit × B)}
    {Z : 𝒲 𝒮 (A × C)} {W : 𝒲 𝒮 (A × D)}
    {U : 𝒲 𝒮 (B × C)} {V : 𝒲 𝒮 (B × D)}
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
    --   simp [δ, 𝒲.liftPi]
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

    -- -- simp only [WNKA.sem, wnka, 𝒲.apply_subtype, G]
    -- -- simp only [DFunLike.coe]
    -- -- simp only [𝒲.apply_subtype]
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
      simp [WeightedAdd.wAdd]
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
      simp [WeightedAdd.wAdd]
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
      simp [WeightedAdd.wAdd]
      sorry
  | _ => sorry

end WeightedNetKAT
