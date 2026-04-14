import WeightedNetKAT.Papers.Syntax

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

/-! ## Section 3 – wNetKAT: Syntax and Semantics -/

Section 3, Definition 1: Countsupp
Section 3, Figure 6: (Pol, @Pol.sem, @Pred.test)
Section 3, Figure 7: @RPol

/-! ## Section 4 – Language Model -/

-- TODO
Section 4, Inline 1: GS
Section 4, Definition 2: @G
Section 4, Lemma 1: @RPol.sem_G_theorem

/-! ## Section 5 – wNetKAT Automata -/

Section 5, Definition 3: @WNKA
-- TODO: update def
Section 5, Inline 1: @WNKA.sem
/-- Use use `𝒪` in stead of `λ` due it it being reserved for lambda functions in lean -/
Section 5, Table 1: (@S, @WNKA.ι, @WNKA.δ, @WNKA.𝒪)
Section 5, Lemma 2: @RPol.wnka_sem
-- TODO: update name
Section 5, Corollary 1: @the_complete_theorem
Section 5, Definition 4: @Matrix.Star.instStar

def marker : ℕ := 12

end WeightedNetKAT.Paper.PLDI2026
