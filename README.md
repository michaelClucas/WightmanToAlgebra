# Wightman to Algebraic QFT

Lean 4 project mapping the Yang–Mills construction in
[yang-mills-group/OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028),
stated with Wightman axioms W0–W3 (`PublicTheory.lean`), to a net of local
*-algebras satisfying the Haag–Kastler axioms as formulated in Fewster–Rejzner,
[Algebraic Quantum Field Theory – an introduction](https://arxiv.org/abs/1904.04051).

The upstream repo is a Lake dependency pinned to commit `3456e5e`, so both
axiom systems are stated over the same `Spacetime`, `forwardCone`,
`spacelike` and `PoincareCoordinates`.

## Layout

| File | Contents |
| --- | --- |
| `WightmanToAlgebra/Regions.lean` | Causal order, causal convexity, domain of dependence, regions, Poincaré action on regions |
| `WightmanToAlgebra/HaagKastler.lean` | `Net` and the axioms: isotony, Einstein causality, timeslice, covariance |
| `WightmanToAlgebra/PolynomialNet.lean` | `O ↦ P(O)`, the unital algebra of smeared fields supported in `O`, with the formal adjoint as *-operation |
| `WightmanToAlgebra/Main.lean` | `wightman_to_haagKastler` and `yangMills_haagKastler` |
| `WightmanToAlgebra/Conjugation.lean`, `Locality.lean` | helpers: Poincaré inverses, conjugation, W3 on generated algebras |
| `WightmanToAlgebra/DoubleCone.lean` | double cone regions, directedness of regions |
| `WightmanToAlgebra/Vacuum.lean` | states, GNS representations and their uniqueness, spectrum condition, vacuum |
| `WightmanToAlgebra/WightmanVacuum.lean` (+`Aux`) | the Wightman vacuum is a vacuum state; its GNS representation is the fields acting on `A(M)Ω` inside `closure(A(M)Ω)` (equality with `H` open, B2) |
| `WightmanToAlgebra/BoundedNet.lean` | von Neumann net `S(O)''` under explicit hypotheses |

## Approach

Fewster–Rejzner allow arbitrary unital *-algebras, so the local algebras are
taken to be polynomial algebras of smeared Wightman fields acting on the common
domain. Then:

- isotony comes from `Algebra.adjoin_mono`;
- Einstein causality comes from W3 (`LocalCommutativity`), applied to generators;
- covariance comes from W2: `X ↦ U(g) X U(g)⁻¹` on the invariant domain;
- the *-operation needs W1's adjoint axiom plus density of the domain.

`yangMills_haagKastler` takes `JointExistence` as a hypothesis. The upstream proof
of it lives in `Solution.lean`; importing that discharges the hypothesis but
builds the full construction.

## Open points

- **Timeslice is not claimed.** It is not a consequence of W0–W3 for polynomial
  field algebras. Getting it needs either a dynamical input from the Yang–Mills
  construction or a passage to von Neumann algebras plus a timelike-tube
  argument.
- **TBD: equation of motion from the upstream construction.** The upstream public
  statement exports a Wightman theory whose fields are gauge-invariant composite
  operators graded by scaling dimension (`Hierarchy.Field d`, e.g. `centeredTrace :
  Field 4`), not the gauge potential `A_μ`. The Yang–Mills equation `D_μ F^{μν} = 0` is
  a statement about `A_μ`, so it has no direct meaning for these fields, and nothing in
  the exported statement is dynamical. Open question: can the construction (lattice
  Wilson action, continuum limit) be made to export a quantum equation of motion, e.g.
  Schwinger–Dyson identities for renormalized composite operators, in a form strong
  enough to give timeslice? Even then, timeslice for an interacting theory is known only
  perturbatively (Chilian–Fredenhagen 2009). See `TIMESLICE.md`.
- **Bounded (von Neumann) nets** are proved under explicit hypotheses
  (`BoundedLocalData`: adjoint-closed, monotone, spacelike-commuting, covariant generating
  sets, with the fields weakly affiliated, `B φ ⊆ (φ†)* B` for `B ∈ S(O)'`; this is weaker
  than affiliation of the closures when `φ` is not essentially self-adjoint). The
  Haag–Kastler part is the generic fact about double commutants and does not use the
  fields; the link to the fields is `boundedAlgebra_weakCommute_field`. No instance of
  `BoundedLocalData` is constructed for any nontrivial theory: deriving the hypotheses
  needs unbounded spectral theory not in Mathlib.
- **Vacuum / spectrum condition**: proved (`WightmanVacuum.lean`). Open: the GNS space
  `closure(A(M)Ω)` equals `H` (BLOCKERS.md B2).

## Status

No `sorry` in `WightmanToAlgebra/`. Every headline theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`.

- [x] Geometry: Lorentz closure, Poincaré action on regions (`Regions.lean`)
- [x] *-structure: formal adjoint, `StarRing`, `StarModule`, star-preserving inclusions
- [x] Covariance: conjugation by `U(g)` on the domain, covariance laws
- [x] `wightman_to_haagKastler`: isotony, Einstein causality, covariance
- [x] `yangMills_haagKastler`, strengthened to the hierarchy's own net (DECISIONS.md D3); conditional on the upstream
      `JointExistence`, which this repo does not check, and adds nothing beyond the general
      Wightman result for that theory
- [x] Phase 5 audit (`AUDIT.md`): fidelity PASS, soundness PASS
- [x] Stretch 1 (`Vacuum.lean`, `WightmanVacuum.lean`): states, GNS uniqueness, spectrum
      condition, vacuum state; the Wightman vacuum is a Poincaré-invariant vacuum and every
      GNS representation is unitarily equivalent to the fields on `A(M)Ω`
      (gap: `closure(A(M)Ω) = H` not proved, BLOCKERS.md B2)
- [x] Stretch 3 (`BoundedNet.lean`): Haag–Kastler for `M(O) = S(O)''` under explicit
      hypotheses `BoundedLocalData` (generic double-commutant fact; link to the fields in
      `boundedAlgebra_weakCommute_field`; no nontrivial instance constructed, B3)
- [ ] Stretch 2, timeslice: false for polynomial nets of general Wightman theories, and the
      upstream construction gives no field equation (`TIMESLICE.md`, BLOCKERS.md B1)

Final summary: `REPORT.md`. Independent PI reviews: `REVIEW_ROUND1.md`, `REVIEW.md` (round 2: sound and faithful); responses in `REPORT.md`.

## Build

```bash
lake exe cache get
lake build
```
