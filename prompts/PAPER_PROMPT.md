Write a short note (about one page of body text, plus references) reporting the result
of the Lean project at https://github.com/michaelClucas/WightmanToAlgebra. Output a
LaTeX source file `paper/note.tex` (amsart, no custom macros beyond `\mathcal`,
`\mathfrak`) and a compiled PDF if a TeX install is available. If not, give the `.tex`
only and say so.

## Sources you must read first

- `REPORT.md`: exact theorem statements, axioms printed, decisions, blockers.
- `README.md`, `DECISIONS.md`, `BLOCKERS.md`, `TIMESLICE.md`, `AUDIT.md`, and `REVIEW.md`
  if it exists (an independent review; if it lists blocking findings, stop and report
  instead of writing the note).
- Fewster–Rejzner, arXiv:1904.04051, Sec. 4.1 and 5.1, for the axioms being formalized.
- The upstream repo https://github.com/yang-mills-group/OpenAI-YM-20261028 (README and
  `ChallengeSpec.lean`) for what the Yang–Mills construction claims.

## Content

1. Setting: the upstream project states a construction of 4d Yang–Mills satisfying
   Wightman-type axioms W0–W3 in Lean. This note formalizes the passage from those
   axioms to a Haag–Kastler net in the Fewster–Rejzner formulation (unital *-algebras,
   not C*-algebras).
2. Results, stated in ordinary mathematical notation, each with its Lean name:
   - Wightman W0–W3 ⇒ the polynomial field net satisfies isotony, Einstein causality,
     Poincaré covariance.
   - Conditional on the upstream `JointExistence`, the Yang–Mills hierarchies carry such
     nets.
   - The Wightman vacuum is a Poincaré-invariant vacuum state satisfying the spectrum
     condition, and GNS recovers the fields on `A(M)Ω` (with the B2 gap).
   - Haag–Kastler for a von Neumann net under explicit strong-locality hypotheses.
3. What is not proved: timeslice (false for polynomial nets of general Wightman theories;
   generalized free field), the equality `closure(A(M)Ω) = H`, and the upstream
   `JointExistence` itself, which this project takes as a hypothesis and does not check.
4. Method: say plainly this was an experiment in LLM-driven formalization. An LLM
   orchestrator split the obligations among LLM subagents, with separate LLM fidelity
   reviewers checking statements against the paper. Report the failure modes that showed
   up: a main statement that was trivially satisfiable as first written, and a hypothesis
   that could hold vacuously. Both were caught by reviewers and fixed. The Lean kernel
   checks proofs, not the faithfulness of statements, so statement review is where the
   human and model effort matters.
5. Availability: repo link, commit hash, toolchain version.

## Claims to avoid

- Do not call this a "new framework" for AQFT. The axioms are Fewster–Rejzner's. What is
  new is a machine-checked formalization of the Wightman-to-Haag–Kastler passage, and
  even "first" needs a literature check (search for prior Lean, Isabelle or Coq work on
  AQFT or Wightman axioms) before you write it. If you cannot confirm it, write "to our
  knowledge" or leave it out.
- Do not claim a rigorous construction of Yang–Mills. The note is conditional on the
  upstream hypothesis, which this project did not verify.
- The mathematics of the Wightman-to-polynomial-net passage is standard and elementary.
  Say so. The contribution is the checked formalization and the experiment.
- Every theorem statement in the note must match the Lean statement in `REPORT.md`. Do
  not strengthen anything in prose.

## Style

Plain, short sentences. No marketing language. Author placeholder `[Author]`.
Acknowledge the LLM's role explicitly in the text, not only in a footnote.
