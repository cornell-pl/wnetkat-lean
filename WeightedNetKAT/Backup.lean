
@[grind]
inductive Policy.Global (P : Policy[F,N,𝒮] → Prop) : Policy[F,N,𝒮] → Prop where
  | Filter (t : Predicate[F,N]) : P (.Filter t) → Global P (.Filter t)
  | Mod (f : F) (n : ℕ) : P (.Mod f n) → Global P (.Mod f n)
  | Dup : P .Dup → Global P .Dup
  | Seq (p q : Policy 𝒮) : Global P p → Global P q → P (.Seq p q) → Global P (.Seq p q)
  | Weight (w : 𝒮) (p : Policy 𝒮) : Global P p → P (.Weight w p) → Global P (.Weight w p)
  | Add (p q : Policy 𝒮) : Global P p → Global P q → P (.Add p q) → Global P (.Add p q)
  | Iter (p : Policy 𝒮) : Global P p → P (.Iter p) → Global P (.Iter p)

theorem Policy.Global_refl {P} {p : Policy[F,N,𝒮]} (h : Global P p) : P p := by
  grind

def Policy.nats (p : Policy[F,N,𝒮]) : Finset ℕ :=
  match p with
  | wnk_policy {skip} => ∅
  | wnk_policy {drop} => ∅
  -- TODO
  | .Filter _ => ∅
  | .Mod _ n => {n}
  | wnk_policy {dup} => {}
  | .Seq p q => p.nats ∪ q.nats
  | wnk_policy {~_ ⨀ ~p} => p.nats
  | wnk_policy {~p ⨁ ~q} => p.nats ∪ q.nats
  | wnk_policy {~p*} => p.nats

theorem Policy.nats_global (p : Policy[F,N,𝒮]) :
    p.Global (fun p' ↦ match p' with
      -- TODO
      | .Filter _ => True
      | .Mod _ n => n ∈ p'.nats
      | wnk_policy {dup} => True
      | .Seq p q => True
      | wnk_policy {~w ⨀ ~p} => True
      | wnk_policy {~p ⨁ ~q} => True
      | wnk_policy {~p*} => True
      ) := by
  induction p with constructor <;> (try simp [nats]) <;> grind [nats]

def Policy.RPol (p : Policy[F,N,𝒮]) (N : Finset ℕ) : RPol[F,N,𝒮] :=
  match p with
  | wnk_policy {skip} => .Skip
  | wnk_policy {drop} => .Drop
  | .Filter _ => sorry
  | .Mod _ _ => sorry
  | wnk_policy {dup} => .Dup
  | .Seq p q => .Seq (p.RPol N) (q.RPol N)
  | wnk_policy {~w ⨀ ~p} => .Weight w (p.RPol N)
  | wnk_policy {~p ⨁ ~q} => .Add (p.RPol N) (q.RPol N)
  | wnk_policy {~p*} => .Iter (p.RPol N)
