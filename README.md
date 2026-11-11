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
- **Bounded (C*/von Neumann) nets.** Passing to bounded operators needs extra
  hypotheses on the Wightman fields (e.g. strong commutativity of
  spectral projections at spacelike separation). Not attempted yet.
- **Vacuum state / spectrum condition** on the net side (vacuum as a state on the
  quasi-local algebra, GNS recovering the Wightman Hilbert space) is not yet stated.

## Status

Statements are in place; proofs are `sorry`. Remaining obligations:

- [ ] `properLorentz_mul_mem`, `properLorentz_one_mem`
- [ ] `poincareAct_isOpen`, `poincareAct_bounded`, `poincareAct_causallyConvex`
- [ ] `Region.map_one`, `Region.map_mul`
- [ ] `formalAdjoint_unique`, `exists_formalAdjoint`
- [ ] `polyStarRing`, `polyStarModule`, `map_star'` of inclusions
- [ ] `polynomialCovariance` (construction)
- [ ] `wightman_to_haagKastler`

## Build

```bash
lake exe cache get
lake build
```
