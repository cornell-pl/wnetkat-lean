import WeightedNetKAT.Syntax

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuous 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]

instance : WeightedSemiring (𝒲 𝒮 X) := sorry
instance : WeightedOmegaContinuous (𝒲 𝒮 X) := sorry

noncomputable instance : DecidableEq (𝒲 𝒮 H[F]) := Classical.typeDecidableEq (𝒲 𝒮 H)

noncomputable def Predicate.sem (p : Predicate[F]) : H[F] → 𝒲 𝒮 H[F] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => if π f = n then η (π::h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- ⟦if t then skip else u⟧
    fun h ↦ (t.sem h ≫= fun h ↦ η h ⨁ ((if t.sem h = 𝟘 then η h else 𝟘) ≫= u.sem))
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦
    t.sem h ≫= u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 𝟘 then η h else 𝟘

instance : Subst Pk[F] F ℕ where
  subst pk f n := fun f' ↦ if f = f' then n else pk f'

@[simp]
def Policy.iter (p : Policy[F,𝒮]) : ℕ → Policy[F,𝒮]
  | 0 => wnk_policy { skip }
  | n+1 => wnk_policy {~p ; ~(p.iter n)}

@[simp, reducible] instance : HPow Policy[F,𝒮] ℕ Policy[F,𝒮] where hPow p n := p.iter n

@[simp]
def Policy.iterDepth : Policy[F,𝒮] → ℕ
| .Filter _ | wnk_policy {~_ ← ~_} | wnk_policy {dup} => 0
| wnk_policy {~p ⨁ ~q} | wnk_policy {~p ; ~q} => p.iterDepth ⊔ q.iterDepth
| wnk_policy {~_ ⨀ ~q} => q.iterDepth
| wnk_policy {~p *} => p.iterDepth + 1

omit [WeightedOmegaContinuous 𝒮] [Fintype F] [DecidableEq F] in
@[simp]
theorem Policy.iterDepth_iter {p : Policy[F,𝒮]} {n : ℕ} :
    (p.iter n).iterDepth = if n = 0 then 0 else p.iterDepth := by
  rcases n with _ | n <;> simp_all
  induction n with simp_all

noncomputable def Policy.sem (p : Policy[F,𝒮]) : H[F] → 𝒲 𝒮 H[F] := match p with
  | .Filter t => t.sem
  | wnk_policy {~f ← ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π[f ↦ n]::h)
  | wnk_policy {dup} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => η (π::π::h)
  -- TODO: this should use the syntax
  | .Seq p q =>
    fun h ↦ (p.sem h ≫= q.sem)
  -- TODO: this should use the syntax
  | .Weight w p => fun h ↦ w ⨀ p.sem h
  -- TODO: this should use the syntax
  | .Add p q => fun h ↦ p.sem h ⨁ q.sem h
  -- TODO: this should use the syntax
  | .Iter p => fun h ↦ ⨁' n : ℕ, (p ^ n).sem h
termination_by (p.iterDepth, sizeOf p)
decreasing_by all_goals simp_all; (try split_ifs) <;> omega

example {t u : Predicate[F]} :
    wnk_policy { ~t ∨ ~u }.sem (𝒮:=𝒮) = wnk_policy { if ~t then skip else @filter ~u }.sem := by
  simp [Policy.sem, Predicate.sem]
