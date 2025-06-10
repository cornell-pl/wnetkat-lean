import WeightedNetKAT.Syntax

variable {X : Type} {𝒮 : Type} [WeightedSemiring 𝒮] [WeightedOmegaContinuous 𝒮]

variable {F : Type} [Fintype F] [DecidableEq F]

instance : WeightedSemiring (𝒲 𝒮 X) := sorry
instance : WeightedOmegaContinuous (𝒲 𝒮 X) := sorry

instance : DecidableEq (𝒲 𝒮 H[F]) := sorry

noncomputable def Predicate.sem (p : Predicate[F]) : H[F] → 𝒲 𝒮 H[F] := match p with
  | wnk_pred {false} => fun _ ↦ 𝟘
  | wnk_pred {true} => η
  | wnk_pred {~f = ~n} => fun h ↦ match h with
    | [] => 𝟘
    | π::h => if π f = n then η (π::h) else 𝟘
  | wnk_pred {~t ∨ ~u} =>
    -- ⟦if t then skip else u⟧
    sorry
  -- TODO: update this once we fix the syntax for ;
  | .Con t u => fun h ↦
    t.sem h ≫= u.sem
  | wnk_pred {¬~t} => fun h ↦ if t.sem h = 𝟘 then η h else 𝟘

instance : Subst Pk[F] F ℕ where
  subst pk f n := fun f' ↦ if f = f' then n else pk f'

def Policy.iter (p : Policy[F,𝒮]) (n : ℕ) : Policy[F,𝒮] := sorry

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
  | .Iter p => fun h ↦ ⨁' n : ℕ, (p.iter n).sem h
decreasing_by
  all_goals try (simp; try omega)
  sorry
