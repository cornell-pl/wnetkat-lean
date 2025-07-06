
@[grind]
inductive Pol.Global (P : Pol[F,N,𝒮] → Prop) : Pol[F,N,𝒮] → Prop where
  | Filter (t : Pred[F,N]) : P (.Filter t) → Global P (.Filter t)
  | Mod (f : F) (n : ℕ) : P (.Mod f n) → Global P (.Mod f n)
  | Dup : P .Dup → Global P .Dup
  | Seq (p q : Pol 𝒮) : Global P p → Global P q → P (.Seq p q) → Global P (.Seq p q)
  | Weight (w : 𝒮) (p : Pol 𝒮) : Global P p → P (.Weight w p) → Global P (.Weight w p)
  | Add (p q : Pol 𝒮) : Global P p → Global P q → P (.Add p q) → Global P (.Add p q)
  | Iter (p : Pol 𝒮) : Global P p → P (.Iter p) → Global P (.Iter p)

theorem Pol.Global_refl {P} {p : Pol[F,N,𝒮]} (h : Global P p) : P p := by
  grind

def Pol.nats (p : Pol[F,N,𝒮]) : Finset ℕ :=
  match p with
  | wnk_pol {skip} => ∅
  | wnk_pol {drop} => ∅
  -- TODO
  | .Filter _ => ∅
  | .Mod _ n => {n}
  | wnk_pol {dup} => {}
  | wnk_pol {~p; ~q} => p.nats ∪ q.nats
  | wnk_pol {~_ ⨀ ~p} => p.nats
  | wnk_pol {~p ⨁ ~q} => p.nats ∪ q.nats
  | wnk_pol {~p*} => p.nats

theorem Pol.nats_global (p : Pol[F,N,𝒮]) :
    p.Global (fun p' ↦ match p' with
      -- TODO
      | .Filter _ => True
      | .Mod _ n => n ∈ p'.nats
      | wnk_pol {dup} => True
      | wnk_pol {~p; ~q} => True
      | wnk_pol {~w ⨀ ~p} => True
      | wnk_pol {~p ⨁ ~q} => True
      | wnk_pol {~p*} => True
      ) := by
  induction p with constructor <;> (try simp [nats]) <;> grind [nats]

def Pol.RPol (p : Pol[F,N,𝒮]) (N : Finset ℕ) : RPol[F,N,𝒮] :=
  match p with
  | wnk_pol {skip} => .Skip
  | wnk_pol {drop} => .Drop
  | .Filter _ => sorry
  | .Mod _ _ => sorry
  | wnk_pol {dup} => .Dup
  | wnk_pol {~p; ~q} => .Seq (p.RPol N) (q.RPol N)
  | wnk_pol {~w ⨀ ~p} => .Weight w (p.RPol N)
  | wnk_pol {~p ⨁ ~q} => .Add (p.RPol N) (q.RPol N)
  | wnk_pol {~p*} => .Iter (p.RPol N)
