VERDICT: SOUND AND FAITHFUL

Second independent review of `michaelClucas/WightmanToAlgebra`, now at `113066d`. The first round (at `0932618`, verdict "SOUND, FIDELITY ISSUES", findings F1–F7) is in git history. Commits `ab86eb9` and `113066d` respond to it. This round re-ran every soundness check on a fresh checkout, verified each response, and re-read the code paths the fixes touch.

## Soundness checks (re-run at `113066d`)

- `lake build`: `Build completed successfully (8671 jobs)`, exit 0. Zero `sorry` in the log. The only warning is `BoundedNet.lean:157:53: Variable name hT is not explicitly referenced` (see N3).
- `#print axioms` on every theorem in `REPORT.md` (now including `gnsRepresentation_equivalent_wightmanGNS` and `boundedAlgebra_weakCommute_field`), plus `polynomialNet`, `polynomialCovariance` and `Net.GNSRepresentation.equivalent`: each gives `[propext, Classical.choice, Quot.sound]`.
- Grep for `axiom|opaque|implemented_by|extern|native_decide|unsafe|skipKernelTC|maxHeartbeats|macro|syntax|elab|sorry|admit` in `WightmanToAlgebra/`: no hits apart from the docstring word "axiom".
- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged since `0932618`. `ym_core` is at `3456e5e75cf8d4cd558955a5c7638fba2d68f464` with a clean tree.
- CI: run 43270785975 succeeded on `ab86eb9` and the next run succeeded on `113066d` (`gh run list`), so the CI claim in `REPORT.md` is accurate.

## Code changes since round 1

`git diff 0932618 HEAD -- WightmanToAlgebra` touches two files:

1. `WightmanVacuum.lean`: `gns_recovers_wightman` is renamed to `gnsRepresentation_equivalent_wightmanGNS`. The statement is unchanged and the docstring now names the B2 gap. Recorded as D9.
2. `BoundedNet.lean`: new theorem `boundedAlgebra_weakCommute_field`. For `O` causally disjoint from `O₂`, every `A ∈ M(O₂)` satisfies `⟨φ(l†, f̄)v, Au⟩ = ⟨v, Aφ(l,f)u⟩` on `D`, that is, `A φ ⊆ (φ†)* A`. I checked the proof. `commute` and `adjoint_mem` give `S(O) ⊆ S(O₂)'`, hence `S(O₂)'' ⊆ S(O)'`, and `affiliated O` then applies to `A`. The statement is correct and non-vacuous, and it is the first result that uses `affiliated`. Recorded as D9.

No other definition or statement changed. Every change since `f82a298` now has a DECISIONS entry: D2, D3, D5, D7 (retroactive, covering `polynomialCovariance`, `wightmanVacuum`, `wightmanGNS` and `boundedCovariance`), and D9.

## Round-1 findings: status

| | Finding | Status | Evidence |
|---|---|---|---|
| F1 | YM theorem adds nothing beyond `JointExistence` | Resolved (disclosure) | `REPORT.md:10-15`, `README.md` checklist |
| F2 | `bounded_haagKastler` restates hypotheses; `affiliated` unused; no instance | Resolved as far as possible without new mathematics. The theorem is unchanged, and the docs now call it "the generic double-commutant fact". There is a new theorem that uses `affiliated`, and B3 records the missing instance. | `REPORT.md` Stretch 3, `BLOCKERS.md` B3 |
| F3 | GNS naming overstates | Resolved | rename, `README.md:24`, `REPORT.md` B2 paragraph |
| F4 | `Timeslice` differs from FR A5 | Resolved (disclosure, D8) | see N1 |
| F5 | Wrong grep claim in `TIMESLICE.md` | Resolved | `TIMESLICE.md:42` |
| F6 | `polynomialCovariance` had no DECISIONS entry | Resolved (retroactive D7) | `DECISIONS.md` D7 |
| F7 | Stale final-commit pointer | Resolved | `REPORT.md:16-17` |

I checked the D8 argument that the GFF counterexample refutes both timeslice formulations. The slab `O₁ = D(B) ∩ {|t|<ε}` contains `B = O₂ ∩ {t=0}`, and `B` is a Cauchy surface of the double cone `O₂ = D(B)`. So FR A5's hypothesis holds as well, and the argument is correct.

## Remaining findings

**N1. `AUDIT.md:140` still rates the timeslice deviation HARMLESS.** Severity: note.
Table row 7 reads "HARMLESS | Close variant of FR A5". The addendum at `AUDIT.md:221` withdraws that ("not proved harmless"), but the table itself was not edited, so a reader who stops at the table gets the old verdict. This does not affect any theorem.

**N2. `boundedAlgebra_weakCommute_field` follows from the hypotheses, not from the Wightman axioms.** `BoundedNet.lean:209`, severity: note.
It is a three-line corollary of `commute`, `adjoint_mem` and `affiliated`. It makes the link between `M(O)` and the fields explicit, but it does not make the bounded-net results any less conditional. `BoundedLocalData` is still uninhabited for every nontrivial theory in this repo (B3). `REPORT.md` and `README.md` now say this.

**N3. Unused `hT` in `boundedCovariance` and `bounded_haagKastler`.** `BoundedNet.lean:157,171`, severity: note. The linter flags it, and D9 records the choice to keep it. It is harmless, but it makes the signature suggest the Wightman axioms are used when they are not.

**N4. The committed round-1 `REVIEW.md` used stale names.** Severity: note. It referred to `gns_recovers_wightman` and to `REPORT.md` text that has since been rewritten. This file replaces it, and `REPORT.md`'s response table keeps the F1–F7 mapping.

No new soundness or fidelity defect was found. The round-1 fidelity checks still hold, since the definitions they cover are unchanged: Regions vs FR A1, net and isotony vs A1/A2, causality vs A3, covariance vs A4, the star as the formal adjoint, `P(O)` generated by fields with `tsupport f ⊆ O`, covariance by conjugation with `U(g) = onStates (coordinates.symm g)`, GNS vs FR Thm 10, spectrum condition and vacuum vs Defs 24/25, and the GFF counterexample.

## What this establishes, for a mathematical physicist

For any Wightman theory satisfying the upstream W0–W3, the code checks the following. The algebras `P(O)` of polynomials in smeared fields with test functions compactly supported in bounded, open, causally convex `O` form a net of unital *-algebras satisfying Fewster–Rejzner A1–A4. The involution is the formal adjoint on the Wightman domain, and covariance is implemented by `X ↦ U(g)XU(g)⁻¹`. The mathematics is elementary (inclusion of generators, W3, W2). The value is in definitions that match the AQFT axioms, and they do. Timeslice (A5) is not proved, and for this net it is false in general: a generalized free field with continuous Källén–Lehmann measure is a counterexample, under either form of the axiom. The vacuum vector state is a Poincaré-invariant state satisfying the spectrum condition, with unique invariant vector, and is unique up to unitary equivalence on the GNS space `closure(P(M)Ω)`. Whether that space is all of `H` is open. The Yang–Mills theorem holds only if the upstream `JointExistence` holds, which this repo does not check, and even then it is the general result applied to that theory. The von Neumann net results are conditional on hypotheses that no nontrivial theory in the repo is shown to satisfy. Nothing here bears on dynamics, a mass gap, or anything that distinguishes Yang–Mills from a free or generalized free field. The repository documents all of these limits accurately.
