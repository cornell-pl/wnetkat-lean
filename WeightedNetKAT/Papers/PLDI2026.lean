module

public import WeightedNetKAT.Papers.Syntax

@[expose] public section

/-!

# Definitions, lemmas and theorems listed in order

This file contains links to all definitions, lemmas and theorems from the paper.

They are listed roughly in the order they appear in the paper. This file should serve as a jumping
off point to navigate and explore the formalization, and not as a reference to _how_ things are
defined. We invite the reader to click on the names in each definition to jump to their original
definition. In Visual Studio Code one can Ctrl/CMD+Click on symbols to jump to their definition.

-/

open scoped Paper

namespace WeightedNetKAT.Paper.PLDI2026

set_option linter.unusedSectionVars false

variable {F N : Type} {𝒮 : Type}
variable [DecidableEq F] [Listed F] [Inhabited F] [DecidableEq N] [Listed N] [Inhabited N]
variable [Semiring 𝒮] [OmegaCompletePartialOrder 𝒮] [OrderBot 𝒮] [IsPositiveOrderedAddMonoid 𝒮]
variable [Star 𝒮] [LawfulStar 𝒮] [MulLeftMono 𝒮] [MulRightMono 𝒮] [OmegaContinuousNonUnitalSemiring 𝒮]
variable {p : Pol[F,N,𝒮]} {p' : RPol[F,N,𝒮]} {t : Pred[F,N]}

/-! ## Section 3 – wNetKAT: Syntax and Semantics -/

Section 3, Definition 1: Countsupp
Section 3, Figure 6: (Pol[F,N,𝒮], p.sem, t.test)
Section 3, Figure 7: RPol[F,N,𝒮]

/-! ## Section 4 – Language Model -/

Section 4, Inline 1: GS
Section 4, Definition 2: G p'
Section 4, Lemma 1: p'.sem_G

/-! ## Section 5 – wNetKAT Automata -/

Section 5, Definition 3: WNKA[F,N,𝒮,S p']
Section 5, Inline 1: 𝒜⟦~p'⟧
/-- We use `𝒪` in stead of `λ` due it it being reserved for lambda functions in lean -/
Section 5, Table 1: (S p', p'.wnka.ι, p'.wnka.δ, p'.wnka.𝒪)
Section 5, Lemma 2: p'.𝒜_eq_G
Section 5, Corollary 1: p.sem_eq_toRPol_𝒜
variable {n : Type} [Fintype n] [DecidableEq n] in
Section 5, Definition 4: Matrix.Star.instStar (α := 𝒮) (n := n)

end WeightedNetKAT.Paper.PLDI2026
