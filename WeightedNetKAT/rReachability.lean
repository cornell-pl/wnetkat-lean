module

public import WeightedNetKAT.WNKA
public import WeightedNetKAT.WNKA.Explicit

@[expose] public section

open OmegaCompletePartialOrder
open scoped RightActions

theorem List.max?_getD_lt {α : Type} [LinearOrder α] [Inhabited α] {xs : List α} {f : α} {e : α}
    (hf : xs ≠ [] ∨ f < e) (h : ∀ x ∈ xs, x < e) : xs.max?.getD f < e := by
  induction xs generalizing f with
  | nil => simp_all
  | cons x xs ih =>
    simp_all; clear ih
    induction xs generalizing x f with
    | nil => simp_all
    | cons y xs ih =>
      simp_all
      -- apply ih _ hf h.right.left

namespace WeightedNetKAT

variable {F : Type} [Fintype F] [Listed F] [DecidableEq F]
variable {N : Type} [Listed N] [DecidableEq N]

namespace rReachability

variable {Q 𝒮 : Type}
variable [Listed Q] [Fintype Q] [DecidableEq Q]
variable [Semiring 𝒮] [DecidableEq 𝒮]
variable (𝒜 : WNKA F N 𝒮 Q)
variable (ℰ : EWNKA F N 𝒮 Q)
variable [KStar 𝒮]

abbrev Run := List (Q × (Pk[F,N] × Pk[F,N]) × Q) × ((Pk[F,N] × Pk[F,N]) × Q)
notation "Run["f","n","q"]" => Run (F:=f) (N:=n) (Q:=q)

/--
error: failed to synthesize instance of type class
  DecidableEq (List (Q × (Pk[F,N] × Pk[F,N]) × Q))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : DecidableEq (List (Q × (Pk[F,N] × Pk[F,N]) × Q)) := inferInstance
#guard_msgs in
example : DecidableEq (List (Q × Pk[F,N] × Pk[F,N] × Q)) := inferInstance

instance : DecidableEq (List (Q × (Pk[F,N] × Pk[F,N]) × Q) × ((Pk[F,N] × Pk[F,N]) × Q)) :=
  letI : DecidableEq (Q × (Pk[F,N] × Pk[F,N]) × Q) := inferInstance
  inferInstance
instance [Repr F] [Repr N] [Repr Q] : Repr (List (Q × (Pk[F,N] × Pk[F,N]) × Q) × ((Pk[F,N] × Pk[F,N]) × Q)) :=
  letI : Repr Pk[F,N] := inferInstance
  letI : Repr (Pk[F,N] × Pk[F,N]) := inferInstance
  letI : Repr (Q × (Pk[F,N] × Pk[F,N]) × Q) := inferInstance
  inferInstance

def runsOf (q q' : Q) (gs : GS[F,N]) : Array Run[F,N,Q] := match gs with
  | ⟨α, [], β⟩ => if q = q' then #[([], (α, β), q)] else #[]
  | ⟨α, β::γ, χ⟩ =>
    Listed.array.filter (fun q'' ↦ 𝒜.δ α β q q'' ≠ 0) |>.flatMap fun q'' ↦
      runsOf q'' q' ⟨β, γ, χ⟩ |>.map fun ⟨r, e⟩ ↦ ⟨⟨q, (α, β), q''⟩ :: r, e⟩
termination_by gs.2.1.length

def Run.isCycleFree (run : Run[F,N,Q]) : Bool :=
  -- NOTE: we only take the first state in pairs of states since the repeat
  --       (q₀ α β q₁) · (q₁ α β q₂) · (q₂ α β q₃) ⋯ (α β qₙ)
  let qs := run.2.2::run.1.map (fun (q, _, _) ↦ q)
  qs.Nodup

def Run.length (run : Run[F,N,Q]) : ℕ := run.1.length
def Run.countQ (run : Run[F,N,Q]) : ℕ := run.2.2::run.1.map (fun (q, _, _) ↦ q) |>.dedup.length

def extendCycleFree' (cur : Run[F,N,Q]) (h : cur.isCycleFree) : Array Run[F,N,Q] :=
  match cur with
  | ⟨[], (α, β), q⟩ =>
    -- Listed.arrayOf (Q × (Pk[F,N] × Pk[F,N]) × Q) |>.filterMap fun (q₀, (α', β'), q₁) ↦
    --   if 𝒜.δ α' β' q₀ q₁ ≠ 0 ∧ 𝒜.δ α β q₁ q ≠ 0 then
    --     let r' : Run[F,N,Q] := ⟨[(q₀, (α', β'), q₁)], (α, β), q⟩
    --     if r'.isCycleFree then some r' else none
    --   else
    --     none
    Listed.arrayOf (Q × Pk[F,N]) |>.filterMap fun (q₀, α') ↦
      if 𝒜.δ α' α q₀ q ≠ 0 then
        let r' : Run[F,N,Q] := ⟨[(q₀, (α', α), q)], (α, β), q⟩
        if r'.isCycleFree then some r' else none
      else
        none
  | ⟨(q₁, (α, β), q')::ρ, t⟩ =>
    Listed.arrayOf (Q × (Pk[F,N] × Pk[F,N])) |>.filterMap fun (q₀, (α', β')) ↦
      if 𝒜.δ α' β' q₀ q₁ ≠ 0 then
        let r' : Run[F,N,Q] := ⟨(q₀, (α', β'), q₁)::(q₁, (α, β), q')::ρ, t⟩
        if r'.isCycleFree then some r' else none
      else
        none

omit [Fintype F] [Fintype Q] [KStar 𝒮] in
@[simp, grind]
theorem extendCycleFree'_isCycleFree {ρ} {h} : ∀ ρ' ∈ extendCycleFree' 𝒜 ρ h, ρ'.isCycleFree := by
  intro ρ'; simp [extendCycleFree']; grind

def extendCycleFree (cur : Array Run[F,N,Q]) (h : ∀ ρ ∈ cur, ρ.isCycleFree) : Array Run[F,N,Q] :=
  let next := cur.attach.flatMap (fun ⟨ρ, hρ⟩ ↦ extendCycleFree' 𝒜 ρ (h ρ hρ))
  if next = #[] then
    cur
  else
    cur ++ next ++ extendCycleFree next (by grind)
termination_by (Listed.size Q + 1) - (cur.toList.map (·.countQ) |>.max?.getD 0)
decreasing_by
  simp only [Array.toList_flatMap, Array.toList_attach, gt_iff_lt]
  refine Nat.sub_lt_sub_left ?_ ?_
  · apply List.max?_getD_lt
    · simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
    · simp
      rintro x ρ α β q h' ⟨_⟩
      specialize h _ h'
      sorry
  · apply List.max?_getD_lt
    · simp
      sorry
    · simp
      sorry

def cycleFreeRunsOf (q : Q) : Array Run[F,N,Q] :=
  extendCycleFree 𝒜 (Listed.array.map (⟨[], ·, q⟩)) (by simp [Run.isCycleFree]; grind)
-- partial def cycleFreeRunsOf (seen : Array Q) (q q' : Q) : Array Run[F,N,Q] :=
--   if q = q' then Listed.array.map ([], ·, q) else
--   -- | ⟨α, β::γ, χ⟩ =>
--     (Listed.arrayOf Q).filter (· ∉ seen) |>.filter (fun q'' ↦ 𝒜.δ α β q q'' ≠ 0) |>.flatMap fun q'' ↦
--       runsOf q'' q' ⟨β, γ, χ⟩ |>.map fun ⟨r, e⟩ ↦ ⟨⟨q, (α, β), q''⟩ :: r, e⟩

def Run.weight : Run[F,N,Q] → 𝒮
  | ⟨[], ((_, _), _)⟩ => 1
  | ⟨(q, (α, β), q')::ρ, ρ'⟩ => 𝒜.δ α β q q' * weight ⟨ρ, ρ'⟩

def δ_star (q q' : Q) (gs : GS[F,N]) : 𝒮 :=
  runsOf 𝒜 q q' gs |>.map (·.weight 𝒜) |>.sum

def all : Array (Run[F,N,Q] × 𝒮) := Listed.array.flatMap (cycleFreeRunsOf 𝒜) |>.map (fun x ↦ (x, x.weight 𝒜))

def potential : Array (Q × Q × Run[F,N,Q] × 𝒮) := sorry

end rReachability

end WeightedNetKAT
