# Progress

Single source of truth for the overseer run. Updated after every merge.

| Obligation | File | Owner | Status | Attempts | Last error |
| --- | --- | --- | --- | --- | --- |
| Phase 0: toolchain + scaffold build | all | overseer | done | 1 | scaffold elaboration errors in PolynomialNet (fixed, D2) |
| `properLorentz_mul_mem`, `properLorentz_one_mem` | Regions.lean | geometry agent | done (e7d827a) | 1 | |
| `poincareAct_isOpen`, `poincareAct_bounded`, `poincareAct_causallyConvex` | Regions.lean | geometry agent | done (e7d827a) | 1 | |
| `Region.map_one`, `Region.map_mul` | Regions.lean | geometry agent | done (e7d827a) | 1 | |
| `formalAdjoint_unique`, `exists_formalAdjoint` | PolynomialNet.lean | star agent | done (8221e31) | 1 | |
| `polyStarRing`, `polyStarModule`, `map_star'` | PolynomialNet.lean | star agent | done (8221e31) | 1 | inline `map_star'` proof hung Lean >15 min; fixed by separate lemma `polyStar_inclusion` |
| `polynomialCovariance` + covariance laws | PolynomialNet.lean, Conjugation.lean | covariance agent | done (merged e5358e0) | 1 | |
| isotony, Einstein causality | Main.lean, Locality.lean | main agent + overseer | done | 2 | agent proofs hit kernel deterministic timeout once real star was merged (`Subtype.ext rfl` unfolds `choose`); overseer rewrote via `polyVal_incl` |
| `wightman_to_haagKastler` | Main.lean | overseer | done | 1 | |
| Phase 5 audit | AUDIT.md | audit agents | done: FIDELITY PASS, SOUNDNESS PASS | 1 | |
| Phase 6.1 vacuum | Vacuum.lean, WightmanVacuum.lean | 2 agents | done (gap B2) | 1 | |
| Phase 6.2 timeslice | TIMESLICE.md | research agent | blocked (B1, false in general) | 1 | |
| Phase 6.3 bounded nets | BoundedNet.lean | agent | done | 1 | statement fix D5/D6 |

Issues: #1 Phase 0 (closed), #2-#4 geometry, #5-#6 star, #7 covariance, #8-#10 main, #11-#12 audit, #13-#16 stretch.


Axioms of both main theorems: propext, Classical.choice, Quot.sound.

## Final

All phases complete or blocked with reasons (B1, B2). Final code commit 45b6d23, CI run 43159539441 green.

PI review addressed 2026-11-12: code commit ab86eb9, CI run 43270785975 green.
