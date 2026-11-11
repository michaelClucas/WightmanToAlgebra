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
| `polynomialCovariance` + covariance laws | PolynomialNet.lean, Conjugation.lean | covariance agent | paused, WIP on branch `worktree-agent-a1f564dd18f04273a` (170c89a) | 1 | not yet verified |
| isotony, Einstein causality | Main.lean, Locality.lean | main agent | paused, WIP on branch `worktree-agent-ab42c67cd8c395d3d` (b3d8b8c) | 1 | not yet verified |
| `wightman_to_haagKastler` | Main.lean | overseer | todo | 0 | |
| Phase 5 audit | AUDIT.md | audit agents | todo | 0 | |
| Phase 6.1 vacuum | | | todo | 0 | |
| Phase 6.2 timeslice | | | todo | 0 | |
| Phase 6.3 bounded nets | | | todo | 0 | |

Issues: #1 Phase 0 (closed), #2-#4 geometry, #5-#6 star, #7 covariance, #8-#10 main, #11-#12 audit, #13-#16 stretch.

## Paused 2026-11-11 (user request)

Phases 0-2 merged on main. Phase 3 and Phase 4 (isotony/causality) work is committed as WIP on the two
branches above (local and pushed to origin). To resume: check out each branch, `lake build`, finish the
remaining `sorry`s, verify, merge. Phase 2 note: prove star facts as separate lemmas, inline proofs in
structure literals hung Lean.
