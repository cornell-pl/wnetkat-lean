import WeightedNetKAT.WNKA
import Batteries.Data.String.Matcher
import WeightedNetKAT.Instances.ENat

def List.dropLastN {α : Type*} (l : List α) : ℕ → List α
  | 0 => l
  | n+1 => l.dropLast |>.dropLastN n

namespace WeightedNetKAT.Paper

def parseAux (x : String) : List (String × String) :=
  x.splitOn "\n"
    |>.filter (fun s ↦ s.containsSubstr "\\newlabel{" ∧ ¬s.containsSubstr "@cref")
    |>.map (·.splitOn "{" |>.flatMap (·.splitOn "}") |>.tail |>.dropLastN 4 |> fun l ↦ (l.headD "", l.getLastD ""))
    |>.filter (fun s ↦ s.1 ≠ "" ∧ ¬s.1.contains '@' ∧ s.1.contains ':')
    |>.mergeSort (fun a b ↦ a.1 ≤ b.1)

def aux : List (String × String) := parseAux (include_str "../../../Papers/weighted-netkat/paper/paper.aux")

set_option pp.deepTerms true in
/--
info: [("appendix:approximation", "appendix.C"), ("appendix:decidability", "appendix.G"),
  ("appendix:monoids-semirings", "appendix.A"), ("appendix:runs-wnka", "subsection.G.3"),
  ("appendix:subsumption", "appendix.D"), ("appendix:unf-sem", "subsection.G.1"), ("cor:deno-aut", "corollary.1"),
  ("def:computable_semiring", "definition.13"), ("def:dec-problems", "definition.5"),
  ("def:equiv-fn-markov", "definition.20"), ("def:lang", "definition.2"),
  ("def:lexicographic-semiring", "definition.14"), ("def:monoids", "definition.9"),
  ("def:omega-comp-monoids", "lemma.1"), ("def:omega-comp-monoids1", "Item.20"), ("def:omega-comp-monoids2", "Item.21"),
  ("def:omega-comp-monoids3", "Item.22"), ("def:omega-comp-semirings", "lemma.2"),
  ("def:omega-monoids", "definition.10"), ("def:omega-monoids1", "Item.17"), ("def:omega-monoids2", "Item.18"),
  ("def:omega-monoids3", "Item.19"), ("def:omega-semirings", "definition.12"), ("def:omega-semirings1", "Item.27"),
  ("def:omega-semirings2", "Item.28"), ("def:omega-semirings3", "Item.29"), ("def:r-reachability", "AMS.30"),
  ("def:r-safety", "AMS.29"), ("def:semirings", "definition.11"), ("def:semirings1", "Item.23"),
  ("def:semirings2", "Item.24"), ("def:semirings3", "Item.25"), ("def:semirings4", "Item.26"),
  ("def:subsingleton-support", "definition.18"), ("def:weightings-measures-equiv", "definition.17"),
  ("def:wnka-runs", "definition.22"), ("eq:1_starproof", "equation.3"), ("eq:2_starproof", "equation.4"),
  ("eq:automata1", "equation.2"), ("eq:enc1", "equation.1"), ("eqn:thm_cantor_approx", "AMS.37"),
  ("ex:automata1", "example.4"), ("ex:automata2", "example.5"), ("ex:automata2-a", "figure.caption.23"),
  ("ex:automata2-b", "figure.caption.23"), ("ex:automata4", "example.6"), ("ex:automata4-a", "figure.caption.26"),
  ("ex:automata4-b", "figure.caption.26"), ("ex:language1", "example.2"), ("ex:language2", "example.3"),
  ("ex:r-reachable", "example.8"), ("ex:r-safe", "example.7"), ("fig:automaton1", "figure.caption.22"),
  ("fig:language", "figure.caption.17"), ("fig:reduced", "figure.caption.16"),
  ("fig:reduced-syntax", "figure.caption.16"), ("fig:semiring", "figure.caption.5"),
  ("fig:syntax-semantics", "figure.caption.13"), ("fig:topo", "figure.caption.7"),
  ("fig:weighted-topo", "figure.caption.12"), ("lmm:addition-equiv-wnetkat-gprobnetkat", "lemma.22"),
  ("lmm:alt-approx-equiv", "lemma.8"), ("lmm:alt-defn-guarded-iteration-equiv", "lemma.11"),
  ("lmm:alt-defn-guarded-iteration-equiv-probnetkat", "lemma.13"), ("lmm:approx-chain", "lemma.7"),
  ("lmm:approx-equiv-wnketkat-probnetkat", "lemma.12"), ("lmm:bind-dist-1", "lemma.32"),
  ("lmm:bind-dist-2", "lemma.33"), ("lmm:bind-equiv-wnetkat-gprobnetkat", "lemma.20"), ("lmm:bind-mono-l", "Item.44"),
  ("lmm:bind-mono-r", "Item.44"), ("lmm:bind-omega-continuous-l", "Item.45"),
  ("lmm:bind-omega-continuous-r", "Item.45"), ("lmm:bind-preserves-subsingleton", "lemma.15"),
  ("lmm:bot-right-annihilate-bind", "Item.43"), ("lmm:equiv-eta-dirac", "lemma.19"),
  ("lmm:guarded-iteration-equiv-wnetkat-gprobnetkat", "lemma.25"),
  ("lmm:if-then-else-equiv-wnetkat-gprobnetkat", "lemma.24"), ("lmm:lexi-compute", "lemma.5"),
  ("lmm:lexicographic-semiring-omega-cont", "lemma.4"), ("lmm:lexicographic-semiring-omega-cpo", "lemma.3"),
  ("lmm:nth-fold-mono", "lemma.9"), ("lmm:nth-fold-sup", "lemma.10"), ("lmm:phi-value-n", "lemma.6"),
  ("lmm:predicate-equiv-wnetkat-gprobnetkat", "lemma.23"), ("lmm:probnetkat-alt-approx-pol-equiv", "lemma.14"),
  ("lmm:red-props", "lemma.26"), ("lmm:red-props1", "Item.61"), ("lmm:red-props2", "Item.62"),
  ("lmm:red-props3", "Item.63"), ("lmm:red-props4", "Item.64"), ("lmm:red-props5", "Item.65"),
  ("lmm:reduced-pred", "lemma.27"), ("lmm:scalar-mul-equiv-wnetkat-gprobnetkat", "lemma.21"),
  ("lmm:singleton-support-approx", "lemma.18"), ("lmm:subsingleton-conditional-choice", "lemma.16"),
  ("lmm:subsingleton-guarded-iteration", "lemma.17"), ("lmm:supp-seq", "lemma.35"), ("lmm:supp-seq-sub", "lemma.34"),
  ("lmm:supp-sum", "lemma.30"), ("lmm:supp-union", "lemma.31"), ("lmm:supp-weigh", "lemma.29"),
  ("lmm:unf-gs-pk", "lemma.37"), ("lmm:unf-sem", "lemma.36"), ("lmm:zero-left-annihilate-bind", "Item.42"),
  ("pf:deno-lang", "subsection.E.3"), ("pf:guarded_pnetkat", "subsection.D.1"),
  ("pf:r-reachable-dec", "subsection.G.4"), ("pf:r-safe-dec", "subsection.G.2"),
  ("pf:thompson-soundness", "subsection.F.1"), ("pf:verif-reach", "subsection.G.6"),
  ("pf:verif-safety", "subsection.G.5"), ("prop:complete-assignment", "proposition.16"),
  ("prop:complete-test", "proposition.15"), ("q:w-reachability", "question.2"), ("q:w-safety", "question.1"),
  ("sec:bounding-weights", "subsection.2.5"), ("sec:decidability", "section.7"),
  ("sec:decision-problems", "subsection.7.1"), ("sec:encode-network", "subsection.2.2"),
  ("sec:introduction", "section.1"), ("sec:iter-lfp", "subsection.B.2"), ("sec:lang-model", "section.5"),
  ("sec:lexicographic-semirings", "subsection.A.4"), ("sec:model-quant-prop", "section.2"),
  ("sec:quant-prop", "subsection.2.3"), ("sec:safety-reachability", "subsection.7.2"),
  ("sec:semantics", "subsection.3.2"), ("sec:syntax", "subsection.3.1"), ("sec:syntax-semantics", "section.3"),
  ("sec:weightings-props", "subsection.B.1"), ("sec:wnetkat-automata", "section.6"),
  ("sec:wnetkat-probnetkat", "section.4"), ("tab:approx", "figure.caption.35"), ("tab:thompson", "table.caption.24"),
  ("tab:weighted-netkat-instances", "figure.caption.6"), ("thm:deno-lang", "theorem.4"),
  ("thm:guarded_pnetkat", "theorem.2"), ("thm:iter-lfp", "theorem.12"), ("thm:r-reachable-dec", "theorem.8"),
  ("thm:r-safe-dec", "theorem.7"), ("thm:reduced", "theorem.3"), ("thm:sem-comp", "theorem.6"),
  ("thm:sup-approx-equiv", "theorem.13"), ("thm:thompson-soundness", "theorem.5"), ("thm:verif-reach", "theorem.10"),
  ("thm:verif-safety", "theorem.9"), ("thm:weightings-props", "theorem.11"), ("thm:weightings-props1", "Item.37"),
  ("thm:weightings-props2", "Item.38"), ("thm:weightings-props3", "Item.39"), ("thm:weightings-props4", "Item.40"),
  ("thm:weightings-props5", "Item.41")]
-/
#guard_msgs in
#eval aux

declare_syntax_cat link_name

local syntax ident : link_name

local syntax (name:=link_macro) "link " link_name " := " term : command

open Lean Elab Command Term Meta in
def getAux : TermElabM (List (String × String)) := do
  let ty ← elabTermAndSynthesize (← `(term|List (String × String))) none
  let exp ← elabTermAndSynthesize (← `(term|aux)) none
  unsafe evalExpr (List (String × String)) ty exp

open Lean Elab Command Term Meta in
@[command_elab link_macro]
def linkMacro : CommandElab := fun stx ↦ do
  let `(link $name:ident := $ref) := stx | throwUnsupportedSyntax
  let name : Ident := name
  let aux ← liftTermElabM getAux
  let name := name.getId.toString.stripPrefix "«" |>.stripSuffix "»"
  match aux.find? (·.1 = name) with
  | some (_, id) =>
    dbg_trace f!"{id}"

    pure ()
  | none =>
    throwError ""
    pure ()

-- macro_rules
-- | `(link $_ := $_) => do
  -- let aux ← Lean.Meta.whnf (.const `aux [])
  -- `(#check RPol.wnka_sem)

namespace Links

link «fig:semiring» := RPol.wnka_sem

link «thm:thompson-soundness» := RPol.wnka_sem

end Links

syntax "paper " "section" ident num : command

end WeightedNetKAT.Paper
