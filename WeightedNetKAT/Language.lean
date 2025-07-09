import Mathlib.Data.Finsupp.Defs
import WeightedNetKAT.RPol
import WeightedNetKAT.Semantics
import WeightedNetKAT.Reduction

section

variable {F : Type}
variable {N : Type} [DecidableEq N]
variable {𝒮 : Type}
variable [Semiring 𝒮]

-- def 𝒲.map {X Y : Type} (m : X →c 𝒮) (f : Y → X) (hf : f.Injective) : 𝒲 𝒮 Y :=
--   ⟨(m <| f ·), by
--     simp only [Set.countable_coe_iff]
--     convert Set.Countable.preimage_of_injOn m.countable (fun ⦃x₁⦄ a ⦃x₂⦄ a ↦ by apply hf)⟩

-- def 𝒲.liftPi {Q : Type} [Countable Q] (f : Q → 𝒲 𝒮 Q) : 𝒲 𝒮 (Q × Q) :=
--   ⟨fun (x, y) ↦ f x y, SetCoe.countable _⟩
def Finsupp.liftPi {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P] (f : Q → P →₀ 𝒮) : (Q × P) →₀ 𝒮 :=
  ⟨(i.elems.biUnion (fun q ↦ (f q).support.map ⟨(q, ·), (Prod.mk_right_injective q)⟩)),
    (fun (x, y) ↦ f x y),
    (by simp [Fintype.complete])⟩

-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
-- @[simp]
-- theorem 𝒲.liftPi_apply {Q : Type} [Countable Q]
--     (f : Q → 𝒲 𝒮 Q) (q : Q) (p : Q) : 𝒲.liftPi f ⟨q, p⟩ = f q p := rfl
-- omit [WeightedOmegaCompletePartialOrder 𝒮] [WeightedOmegaContinuousPreSemiring 𝒮] in
@[simp]
theorem 𝒞.liftPi_apply {Q P : Type} [i : Fintype Q] [DecidableEq Q] [DecidableEq P]
    (f : Q → P →₀ 𝒮) (q : Q) (p : P) : Finsupp.liftPi f ⟨q, p⟩ = f q p := rfl

-- def 𝒲.equiv {X Y : Type} (m : X →c 𝒮) {e : Y ≃ X} : 𝒲 𝒮 Y := m.map _ e.injective

end

namespace WeightedNetKAT

/-- `At` is the set of complete tests. -/
def At (F : Type) (N : Type) : Type := Pk[F,N]

/-- `Π` is the set of all complete assignments. -/
def Pi (F : Type) (N : Type) : Type := Pk[F,N]
@[inherit_doc] notation "Π" => WeightedNetKAT.Pi

/--
The language of guarded strings.

Isomorphically defined as `At ⬝ (Π ⬝ dup)* ⬝ Π`.
-/
def GS (F : Type) (N : Type) := Pk[F,N] × List Pk[F,N] × Pk[F,N]
notation "GS[" f "," n "]" => GS (F:=f) (N:=n)

instance {F N : Type} [Fintype F] [DecidableEq F] [DecidableEq N] : DecidableEq GS[F,N] := instDecidableEqProd
instance {F N : Type} [Fintype F] [Fintype N] : Countable GS[F,N] := instCountableProd
instance {F N : Type} [Fintype F] [Fintype N] [Encodable F] [Encodable N] : Encodable GS[F,N] := Encodable.Prod.encodable

variable {F : Type} [Fintype F] [DecidableEq F] [Encodable F]
variable {N : Type} [Fintype N] [DecidableEq N] [Encodable N]

def GS.mk (α : Pk[F,N]) (x : List Pk[F,N]) (β : Pk[F,N]) : GS[F,N] := ⟨α, x, β⟩

class WeightedConcat (α : Type) (β : outParam Type := Option α) where
  /-- Weighted concatination -/
  concat : α → α → β

@[inherit_doc]
infixl:50 " ♢ " => WeightedConcat.concat

instance : WeightedConcat GS[F,N] where
  concat | ⟨α, x, β⟩, ⟨γ, y, ξ⟩ => if β = γ then some ⟨α, x ++ y, ξ⟩ else none

variable {𝒮 : Type} [Semiring 𝒮]
variable [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]

noncomputable instance : WeightedConcat (GS[F,N] →c 𝒮) (GS[F,N] →c 𝒮) where
  concat m m' := ⟨
    fun g ↦ ω∑ (x : m.support) (y : m'.support), if (x.val ♢ y.val) = some g then m x * m' y else 0,
    SetCoe.countable _,
  ⟩

#check (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0)) ♢ (GS.mk (fun _ ↦ 0) [] (fun _ ↦ 0))

notation "gs[" α ";" β "]" => GS.mk α [] β
notation "gs[" α ";" x ";" "dup" ";" β "]" => GS.mk α [x] β
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" β "]" => GS.mk α [x, y] β
notation "gs[" α ";" x ";" "dup" ";" y ";" "dup" ";" z ";" "dup" ";" β "]" => GS.mk α [x, y, z] β

#check gs[1;2]
#check gs[1;2;dup;3]
#check gs[1;2;dup;3]

open scoped Classical in
noncomputable def G.ofPk (f : Pk[F,N] → GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if ∃ α, f α = · then 1 else 0), SetCoe.countable _⟩
def G.ofConst [DecidableEq GS[F,N]] (f : GS[F,N]) : GS[F,N] →c 𝒮 :=
  ⟨(if f = · then 1 else 0), SetCoe.countable _⟩

open scoped Classical in
omit [Encodable F] [Encodable N] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofPk_apply (f : Pk[F,N] → GS[F,N]) (x : GS[F,N]) :
    G.ofPk f x = if ∃ α, f α = x then (1 : 𝒮) else 0 := rfl
omit [Encodable F] [Encodable N] in
omit [DecidableEq N] [DecidableEq F] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮] in
@[simp]
theorem G.ofConst_apply [DecidableEq GS[F,N]] (f : GS[F,N]) (x : GS[F,N]) :
    G.ofConst f x = if f = x then (1 : 𝒮) else 0 := rfl

variable [MulLeftMono 𝒮] [MulRightMono 𝒮]

open scoped Classical in
noncomputable def G (p : RPol[F,N,𝒮]) : GS[F,N] →c 𝒮 := match p with
  | wnk_rpol { drop } => 0
  -- [x = α; α | α ∈ Pk]
  | wnk_rpol { skip } => G.ofPk fun α ↦ gs[α; α]
  -- [x = α; α]
  | wnk_rpol { @test ~α } => G.ofConst gs[α; α]
  -- [x = α; π | α ∈ Pk]
  | wnk_rpol { @mod ~π } => G.ofPk fun α ↦ gs[α; π]
  -- [x = α; α; dup; α | α ∈ Pk]
  | wnk_rpol { dup } => G.ofPk fun α ↦ gs[α; α; dup; α]
  | wnk_rpol { ~p₁ ⨁ ~p₂ } => G p₁ + G p₂
  | wnk_rpol { ~p₁ ; ~p₂ } => G p₁ ♢ G p₂
  | wnk_rpol { ~w ⨀ ~p₁ } => w * G p₁
  | wnk_rpol { ~p₁* } => ω∑ n : ℕ, G (p₁ ^ n)
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

omit [Encodable F] [Encodable N] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
-- TODO: this proof is incredibly slow
set_option maxHeartbeats 500000 in
attribute [-simp] Function.iterate_succ in
theorem G.iter_succ (p₁ : RPol[F,N,𝒮]) (n : ℕ) :
    G (p₁.iter (n + 1)) = (G p₁ ♢ ·)^[n] (G p₁) := by
  induction n with
  | zero =>
    ext gs
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    if hgs : ¬(G p₁) gs = 0 then
      simp only [RPol.iter, G, ofPk, GS.mk, Function.iterate_zero, id_eq]
      simp only [WeightedConcat.concat, Countsupp.coe_mk, mul_ite, mul_one, mul_zero]
      rw [ωSum_eq_single ⟨gs, by grind [Countsupp.mem_support_iff]⟩]
      · rw [ωSum_eq_single ⟨⟨gs.2.2, [], gs.2.2⟩, by simp only [Countsupp.mem_support_iff,
        Countsupp.coe_mk, exists_apply_eq_apply, ↓reduceIte, ne_eq, h10, not_false_eq_true]⟩]
        · split
          simp only [Option.ite_none_right_eq_some, Option.some.injEq, exists_apply_eq_apply,
            ↓reduceIte]
          grind
        · grind only [= List.append_assoc, Countsupp.coe_mk, Countsupp.mem_support_iff,
          ite_eq_right_iff, =_ List.append_assoc, Subtype.mk.injEq, → List.eq_nil_of_append_eq_nil,
          cases eager Subtype]
      · grind only [Countsupp.coe_mk, List.append_nil, Countsupp.mem_support_iff, ite_eq_right_iff,
          Subtype.mk.injEq, → List.eq_nil_of_append_eq_nil, ωSum_zero, cases eager Subtype, cases
          Or]
    else
      simp at hgs
      simp only [RPol.iter, G, WeightedConcat.concat, ofPk, GS.mk, Countsupp.coe_mk, mul_ite,
        mul_one, mul_zero, Function.iterate_zero, id_eq, hgs, ωSum_eq_zero_iff, ite_eq_right_iff,
        forall_exists_index, Subtype.forall, Countsupp.mem_support_iff, ne_eq, not_forall,
        forall_apply_eq_imp_iff]
      grind
  | succ n ih =>
    simp only [RPol.iter, G, Function.iterate_succ', Function.comp_apply]
    grind only [G, RPol.iter]

omit [Encodable F] [Encodable N] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
attribute [-simp] Function.iterate_succ in
theorem G.iter (p₁ : RPol[F,N,𝒮]) (n : ℕ) :
    G (p₁.iter n) = (G p₁ ♢ ·)^[n] (G wnk_rpol {skip}) := by
  induction n with
  | zero =>
    ext gs
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    if hgs : ¬(G p₁) gs = 0 then
      simp only [RPol.iter, G, ofPk, GS.mk, Function.iterate_zero, id_eq]
    else
      simp at hgs
      simp only [RPol.iter, G, ofPk, GS.mk, Countsupp.coe_mk, WeightedConcat.concat,
        Function.iterate_zero, id_eq]
  | succ n ih =>
    simp only [RPol.iter, G, Function.iterate_succ', Function.comp_apply]
    grind only [G, RPol.iter]

def GS.pks (s : GS[F,N]) : List Pk[F,N] := s.1 :: s.2.1 ++ [s.2.2]
def GS.H (s : GS[F,N]) : H[F,N] := (s.2.2, s.2.1.reverse)
def GS.H' (s : GS[F,N]) : H[F,N] := (s.2.2, s.2.1)

def GS.toRPol (g : GS[F,N]) : RPol[F,N,𝒮] :=
  wnk_rpol {@test ~g.1}.Seq <| g.2.1.foldr (fun x y ↦ wnk_rpol { @mod ~x; dup; ~y }) wnk_rpol { @mod ~g.2.2 }

example (a b c d : Pk[F,N]) :
    gs[a;b;dup;c;dup;d].toRPol (𝒮:=𝒮) = wnk_rpol { @test ~a; @mod ~b; dup; @mod ~c; dup; @mod ~d } := by
  rfl

noncomputable def GS.sem (g : GS[F,N]) : H[F,N] → H[F,N] →c 𝒮 :=
  g.toRPol.sem
omit [DecidableEq F] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem GS.sem_eq (g : GS[F,N]) (h) :
    g.sem (𝒮:=𝒮) h = if g.1 = h.1 then η (g.H.1, g.H.2 ++ h.2) else 0 := by
  if h10 : (1 : 𝒮) = 0 then ext; simp [eq_zero_of_zero_eq_one h10.symm] else
  rcases h with ⟨π, h⟩
  simp_all [GS.sem]
  split_ifs with h₀
  · simp [GS.toRPol, RPol.sem, h₀]
    ext ⟨π', h'⟩
    simp
    rw [ωSum_eq_single ⟨⟨π, h⟩, by simp [h10]⟩ (by simp_all)]
    simp
    obtain ⟨g₀, g, g₁⟩ := g
    simp_all
    subst_eqs
    simp [H]
    induction g generalizing π h with
    | nil =>
      simp_all [RPol.sem, η]
    | cons x g ih =>
      simp_all [RPol.sem]
      rw [ωSum_eq_single ⟨⟨x, h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
      rw [ωSum_eq_single ⟨⟨x, x::h⟩, by simp [h10]⟩ (by simp_all)]
      simp_all
  · simp [GS.toRPol, RPol.sem, h₀, ne_comm.mp h₀]

@[simp]
noncomputable def RPol.sem_G_theorem (p : RPol[F,N,𝒮]) : Prop :=
  p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h

omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
omit [Encodable F] [Encodable N] in
theorem RPol.sem_G.Drop : wnk_rpol {drop}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext h; simp [sem, G]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Skip : wnk_rpol {skip}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;π], (by simp [G, h10])⟩]
  · simp [GS.mk, GS.H, η]
  · simp [G, GS.mk, GS.H, h10]
    rintro α _ _ ⟨_⟩
    have : α ≠ π := by rintro ⟨_⟩; grind
    simp_all
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Test {π₀} : wnk_rpol {@test ~π₀}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
    ext ⟨π, h⟩
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    simp [GS.sem_eq, sem, G]
    if h₀ : π = π₀ then
      subst_eqs
      rw [ωSum_eq_single ⟨gs[π₀;π₀], (by simp [G, h10])⟩]
      · simp [GS.mk, GS.H, η]
      · simp [G, GS.mk, GS.H]
    else
      symm
      have : π₀ ≠ π := fun a ↦ h₀ (Eq.symm a)
      simp [h₀, G, GS.mk, GS.H, h10, this]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Mod {γ} : wnk_rpol {@mod ~γ}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩
  if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
  simp [GS.sem_eq, sem, G]
  rw [ωSum_eq_single ⟨gs[π;γ], (by simp [G, h10])⟩]
  · simp [GS.mk, GS.H, η]
  · simp [G, GS.mk, GS.H, h10]
    rintro α _ _ ⟨_⟩
    have : α ≠ π := by grind
    simp [this]
omit [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem RPol.sem_G.Dup : wnk_rpol {dup}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  ext ⟨π, h⟩ ⟨π', h'⟩
  simp
  simp [GS.sem_eq]
  simp [sem, G, GS.H]
  split_ifs with h₀
  · cases h₀
    symm
    if h10 : (1 : 𝒮) = 0 then simp [eq_zero_of_zero_eq_one h10.symm] else
    rw [ωSum_eq_single ⟨gs[π;π;dup;π], (by simp [G, h10])⟩]
    · simp_all [GS.mk, η]
    · simp_all [G, GS.mk]
      intro g hg
      split_ifs
      · grind
      · simp
  · symm
    simp [G]
    rintro g h10 h' ⟨⟨α, ⟨_⟩⟩, h10⟩
    simp [GS.mk]
    split_ifs
    · subst_eqs
      simp [η, h10]
      grind
    · rfl
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Seq {p₁ p₂} (ih₁ : p₁.sem_G_theorem) (ih₂ : p₂.sem_G_theorem) :
    wnk_rpol {~p₁ ; ~p₂}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp only [sem_G_theorem] at *
  simp [sem, G]
  rw [ih₁, ih₂]; clear ih₁ ih₂
  simp
  simp [Countsupp.bind, WeightedConcat.concat]
  ext h₀ h₁
  simp [← ωSum_mul_right, ← ωSum_mul_left]
  conv => left; arg 1; ext; rw [ωSum_comm]
  simp [← ωSum_prod' (α:=𝒮)]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, h⟩ ↦
    ⟨⟨(b.2.2, b.2.1.reverse ++ h₀.2), by
      simp_all [G]
      simp_all [G]
      simp_all [GS.sem_eq, GS.H]
      obtain ⟨b₀, b₁, b₂⟩ := b
      obtain ⟨c₀, c₁, c₂⟩ := c
      simp_all
      obtain ⟨⟨⟨_⟩, ⟨_⟩⟩, h⟩ := h
      simp [WeightedConcat.concat] at ha
      use (b₀, b₁, b₂)
      split_ifs at h <;> simp_all⟩,
      ⟨b, hb⟩, ⟨c, hc⟩⟩)
  · simp
    intro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, h⟩
    simp_all only [Prod.mk.injEq, Subtype.mk.injEq, Subtype.forall, Function.mem_support, ne_eq,
      ite_eq_right_iff, Classical.not_imp, and_imp, Prod.forall, and_true,
      Countsupp.mem_support_iff]
    simp_all only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp]
    grind
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    simp_all only [Function.mem_support, ne_eq, Subtype.coe_eta, Prod.mk.eta, Set.mem_range,
      Prod.mk.injEq, Subtype.mk.injEq, Subtype.exists, ite_eq_right_iff, Classical.not_imp,
      exists_and_left, exists_prop, Prod.exists, exists_eq_right_right, Countsupp.mem_support_iff]
    simp_all only [Countsupp.mem_support_iff, Countsupp.ωSum_apply, Countsupp.hMul_apply_left,
      ne_eq, ωSum_eq_zero_iff, Subtype.forall, not_forall, Classical.not_imp]
    simp_all only [exists_prop]
    obtain ⟨a, ha, ha'⟩ := ha
    intro h
    simp_all [GS.sem_eq, GS.H]
    split_ifs at * <;> try simp_all [Countsupp.coe_zero,  ite_eq_right_iff, ite_self, mul_ite, mul_one, mul_zero, zero_mul, η_apply]
    obtain ⟨a₀, a₁, a₂⟩ := a
    obtain ⟨b₀, b₁, b₂⟩ := b
    obtain ⟨c₀, c₁, c₂⟩ := c
    subst_eqs
    simp_all
    obtain ⟨⟨_⟩, h, h'⟩ := h
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    simp at h
    obtain ⟨⟨_⟩, ⟨_⟩⟩ := h
    simp_all [G, WeightedConcat.concat]
    apply Exists.intro
    use hb
    apply Exists.intro
    use hc
    simp_all
  · simp [G]
    simp_all [GS.sem_eq, GS.H]
    intro a ha b hb c hc h h'
    split at h
    simp at h
    obtain ⟨⟨_⟩, _⟩ := h
    simp_all
    split_ifs at *
    · simp_all only [η_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff, Classical.not_imp,
      ↓reduceIte]
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
    · simp_all
      grind
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
    · simp_all
      grind
    · simp_all only [Countsupp.coe_zero, Pi.zero_apply, mul_zero, not_true_eq_false]
omit [Encodable F] [Encodable N] in
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Add {p₁ p₂} (ih₁ : p₁.sem_G_theorem) (ih₂ : p₂.sem_G_theorem) : wnk_rpol {~p₁ ⨁ ~p₂}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp [sem]
  rw [ih₁, ih₂]; clear ih₁ ih₂
  ext h h'
  simp [G, right_distrib, ωSum_add]
  congr! 1
  · symm
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨x, h₀⟩, h₁⟩ ↦ ⟨x, by simp at h₀; simp [G, h₀]⟩)
    · intro ⟨⟨_, _⟩, _⟩; simp
    · intro ⟨_, h₀⟩
      simp at h₀
      simp_all [G]
      contrapose! h₀
      simp_all [G]
      rcases h₀
      simp_all
    · simp
  · symm
    apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨x, h₀⟩, h₁⟩ ↦ ⟨x, by simp at h₀; simp [G, h₀]⟩)
    · intro ⟨⟨_, _⟩, _⟩; simp
    · intro ⟨_, h₀⟩
      simp at h₀
      simp_all [G]
      contrapose! h₀
      simp_all [G]
      rcases h₀
      simp_all
    · simp
omit [Encodable F] [Encodable N] in
variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Weight {w} {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~w ⨀ ~p₁}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  simp only [sem_G_theorem] at ih
  simp [sem, ih, G]; clear ih
  ext h h'
  simp [← ωSum_mul_left]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, by simp_all; contrapose! ha'; simp_all⟩)
  · intro ⟨_, _⟩ ⟨_, _⟩
    simp_all
    exact fun a ↦ SetCoe.ext a
  · intro ⟨s, h₀⟩; simp [GS.H]
    obtain ⟨π, h⟩ := h
    simp_all [G]
    contrapose! h₀
    simp_all [← mul_assoc, G]
    obtain ⟨_, _⟩ := h₀
    simp_all
  · simp [G]
    intro g h₀ h₁
    simp_all [← mul_assoc, G]

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

omit [Encodable F] [MulLeftMono 𝒮] [MulRightMono 𝒮] in
theorem G.concat_apply {L R : GS F N →c 𝒮} {xₙ : GS F N} :
      ((L ♢ R) : _ →c 𝒮) xₙ
    = ∑ i ∈ Finset.range (xₙ.2.1.length + 1), ∑ (γ : Pk[F,N]), L (xₙ.splitAtJoined i γ).1 * R (xₙ.splitAtJoined i γ).2 := by
  obtain ⟨α, A, αₙ⟩ := xₙ
  simp
  simp [WeightedConcat.concat]
  rw [← Finset.sum_product']
  rw [← ωSum_finset]
  apply ωSum_eq_ωSum_of_ne_one_bij (fun ⟨⟨⟨i, γ⟩, hi⟩, hi'⟩ ↦ by
    exact ⟨(α, A.take i, γ), by simp; contrapose! hi'; simp [hi', GS.splitAtJoined]⟩)
  · intro ⟨⟨⟨i, γ⟩, hi⟩, b⟩
    simp_all
    simp_all
    simp_all
    rintro i' γ' hi' h h'
    rw [Prod.eq_iff_fst_eq_snd_eq] at h'
    simp at h'
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
    intro i γ hi hγ
    rw [ωSum_eq_single ⟨(γ, List.drop i A, αₙ), by simp; contrapose! hγ; simp [hγ]⟩]
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
      rw [List.drop_append]
      simp
      have : (i - min i A.length) = 0 := by omega
      simp [this]

variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G.Iter {p₁} (ih : p₁.sem_G_theorem) : wnk_rpol {~p₁*}.sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
  funext h₀
  simp [sem]
  if h10 : (1 : 𝒮) = 0 then ext; simp [eq_zero_of_zero_eq_one h10.symm] else
  have : ∀ n, (p₁.iter n).sem_G_theorem (F:=F) (N:=N) (𝒮:=𝒮) := by
    intro n
    induction n with
    | zero =>
      simp [G, sem]
      ext h h'
      simp
      rw [ωSum_eq_single ⟨⟨h.1, [], h.1⟩, by simp [G, h10, GS.mk]⟩]
      · split_ifs with hα hβ
        · subst_eqs
          simp [GS.sem_eq, GS.H, GS.mk]
        · subst_eqs
          simp at hβ
        · simp_all [GS.sem_eq, GS.mk, GS.H]
        · simp_all [GS.sem_eq, GS.H]
      · simp [GS.mk, GS.sem_eq, GS.H, G]
        rintro α h10 h' β ⟨_⟩
        rw [Prod.eq_iff_fst_eq_snd_eq] at h'
        simp at h'
        simp_all
    | succ n ih' =>
      have := RPol.sem_G.Seq (p₁:=p₁) (p₂:=p₁.iter n) ih ih'
      simp_all
  simp only [sem_G_theorem] at this; simp only [this]; clear this
  simp [G, Countsupp.instHMul]
  ext α
  simp [← ωSum_mul_right]
  rw [ωSum_comm]
  congr with n
  apply ωSum_eq_ωSum_of_ne_one_bij
  rotate_right
  · exact fun ⟨x, hx⟩ ↦ ⟨x, by simp_all; contrapose! hx; simp [hx]⟩
  · intro; grind
  · simp_all [G]; grind
  · simp

variable [OmegaContinuousNonUnitalSemiring 𝒮] in
theorem RPol.sem_G (p : RPol[F,N,𝒮]) :
    p.sem = fun h ↦ ω∑ x : (G p).support, G p x * x.val.sem (𝒮:=𝒮) h := by
  induction p with
  | Drop => exact RPol.sem_G.Drop
  | Skip => exact RPol.sem_G.Skip
  | Test π₀ => exact RPol.sem_G.Test
  | Mod γ => exact RPol.sem_G.Mod
  | Dup => exact RPol.sem_G.Dup
  | Seq p₁ p₂ ih₁ ih₂ => exact RPol.sem_G.Seq ih₁ ih₂
  | Add p₁ p₂ ih₁ ih₂ => exact RPol.sem_G.Add ih₁ ih₂
  | Weight w p₁ ih => exact RPol.sem_G.Weight ih
  | Iter p₁ ih => exact RPol.sem_G.Iter ih

end WeightedNetKAT
