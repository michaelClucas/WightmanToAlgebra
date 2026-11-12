# Time-slice (FR A5) for the polynomial net

Target: `Net.Timeslice` (`WightmanToAlgebra/HaagKastler.lean:57`). For `polynomialNet`, `A(O) = Algebra.adjoin ℂ {φ_l(f) : tsupport f ⊆ O}` inside `End(D)` and `incl` is subalgebra inclusion, so time-slice for `O₁ ⊆ O₂ ⊆ dependenceDomain O₁` means exactly `P(O₂) ≤ P(O₁)`, i.e. every generator `φ_l(f)` with `tsupport f ⊆ O₂` lies in `P(O₁)`.

## 1. Verdicts

| | Verdict |
|---|---|
| (a) general W0–W3 | **False in general**, so not provable. A generalized free field is a counterexample (section 2). |
| (b) Yang–Mills hierarchy | **Not provable from what upstream exports.** Nothing in it is a dynamical relation among fields (section 3). Whether it holds is open. |
| (c) modified nets | **Not provable here.** The Borchers route proves a different statement. The field-equation route needs a hypothesis the YM hierarchy lacks, plus causal Green's functions that Mathlib does not have (section 4). |

## 2. (a) Counterexample: generalized free field

**Standard facts.** A generalized free field (GFF) is a scalar field whose two-point function is `W(x−y) = ∫ dρ(m) Δ₊(x−y; m²)` and whose n-point functions are given by Wick's theorem. Here ρ is a positive, polynomially bounded measure on `[0,∞)`. Every GFF satisfies the Wightman axioms (Greenberg, Ann. Phys. 16 (1961); Jost, *General Theory of Quantized Fields*). It lives on Fock space over the one-particle space `K = ⊕∫ dρ(m) L²(H_m⁺, dμ_m)`, and `‖P₁φ(f)Ω‖² = ∫ dρ(m) ∫_{H_m⁺} |f̂(p)|² dμ_m(p)`. Choose `ρ = Lebesgue measure on [1,2]`.

**Literature (standard, cite with care).** Haag–Schroer (1962) and Landau (CMP 39, 1974) pointed out that GFFs violate primitive causality / time-slice-type properties when ρ is not concentrated on a single mass. Garber (CMP 42, 1975) analysed duality and the causal properties of GFF nets of von Neumann algebras. Haag's *Local Quantum Physics* (§III.3 and the discussion of primitive causality) treats the GFF as the standard example of a Wightman theory without time-slice. I have not rechecked the exact hypotheses on ρ in Landau's and Garber's statements. Cite them for the von Neumann-algebra version, and use the self-contained argument below for the polynomial version, which is the one we need.

**Sketch (mine, elementary, polynomial level).** Fix a ball `B` at `t = 0`, let `O₂ = D(B)` be the double cone, and let `O₁ = O₂ ∩ {|t| < ε}`. Both are bounded, open and causally convex, and `O₂ ⊆ dependenceDomain O₁`. Take a nonzero `f ∈ C_c^∞(O₂ \ closure O₁)`, and suppose `φ(f) = X ∈ P(O₁)` as an element of `End(D)`.

1. `X` is a finite sum of monomials `φ(g₁)…φ(g_k)` with `tsupport gᵢ ⊆ O₁`. By Wick's theorem, `P₁ φ(g₁)…φ(g_k)Ω` is a finite linear combination of the one-particle vectors `[gᵢ] := P₁φ(gᵢ)Ω`, because all other contractions give scalars. So `P₁XΩ = [h]` for some `h ∈ C_c^∞`, with `tsupport h ⊆ O₁` (a finite union of compact subsets of `O₁`).
2. `P₁φ(f)Ω = [f]`. So `[f − h] = 0`, which means `∫₁² dm ∫_{H_m⁺} |(f−h)^|² dμ_m = 0`.
3. The shells `H_m⁺` for `m ∈ (1,2)` sweep out the open set `U = {p : 1 < p² < 4, p⁰ > 0}`, and `dm dμ_m` is equivalent to Lebesgue measure on `U`. So `(f−h)^ = 0` a.e. on `U`, and by continuity everywhere on `U`.
4. `f − h` has compact support, so `(f−h)^` is entire (Paley–Wiener). It vanishes on a nonempty open set, so `f = h`. Then `tsupport f ⊆ O₁`, which contradicts `f ≠ 0` with support outside `closure O₁`.

So `φ(f) ∉ P(O₁)` and `Timeslice` fails for `polynomialNet` of the GFF. The argument uses only the vacuum vector, so it does not depend on which invariant domain `D` is chosen.

**Contrast with the free field.** If ρ = δ_{m₀}, step 3 only gives `(f−h)^ = 0` on the single shell `p² = m₀²`. That is consistent with `f − h = (□+m₀²)g`, and indeed time-slice holds at the polynomial level because `φ((□+m₀²)g) = 0` on `D` (standard: Dimock CMP 77 (1980); Fewster–Rejzner §3). The mechanism in the free case is exactly the field equation, and nothing in W0–W3 supplies one.

## 3. (b) What upstream provides (`.lake/packages/ym_core`)

What I checked:

- `PublicTheory.lean`. W0 gives the spectral measure, positive energy and a unique vacuum. W1 gives the dense domain, cyclicity, temperedness and the adjoint identity. W2 gives Poincaré covariance. W3 gives spacelike commutativity. Nothing here relates fields at timelike separation.
- `ChallengeSpec.lean`, `Hierarchy`. This is data: labels, `correlation`, `continuation`, OPE `coefficient`/`actor`, and `centeredTrace`.
- `Reconstructed`. Gives the Wightman axioms, faithfulness, label coverage, permutation symmetry and smoothness of Euclidean correlations, and the phase mixture. `analytic` is holomorphy in complex times on `orderedTube`, and `boundary` says the boundary values are the Wightman functions. That analytic continuation is the standard consequence of the spectrum condition and holds in every Wightman theory, the GFF included, so it adds nothing beyond (a).
- `OperatorProductExpansion`. Short-distance (Euclidean-norm) asymptotics of `grouped` correlations, with remainder bounds. It relates products at coincident points to single fields at one point. It says nothing about propagation from a time slice.
- `TraceTest`. A vanishing one-point function, `r⁸ log²` short-distance behaviour, and exclusion of finite Wick (mass-shell) profiles. This rules out the free-field mechanism and does not replace it with another.
- `ContactSpec.Contacts`. An extension of correlations to a distribution across diagonals. Kinematic only.
- `Construction.lean`, `Solution.lean`, `HierarchyBridge.lean`, `PublicWilson.lean`, `PublicView.lean`, `WilsonBridge.lean`. These cover the Wilson lattice family, the regularity of insertions, the convergence of smeared moments, and the bridging of internal `YM.*` objects to the public structures. `constructed` also exports internal clauses (`Headline.*`, `Contacts.*`, `Pert.*`).

A grep of the package for field-equation, Schwinger, Klein, Laplacian and time-slice terms hits about 30 files (corrected after the PI review, finding F5; the earlier version of this file wrongly said there was a single hit). Examples: `YM/Maxwell/PotentialKernel.lean` ("Laplacian vanishes on the open patch"), `YM/Next/MAXWELL/Source.lean`, `YM/Extra/FREE_DETECTOR_ALGEBRA/Solutions.lean`, `YM/Trace/ConeValues.lean` ("strict-time slice estimates"). These are lattice kernels, free-field comparison objects and Euclidean Schwinger functions used inside the construction. None is exported through `ChallengeSpec.Hierarchy` / `Properties`, and `YM/Pert/Lattice/Lifts.lean` states that no field equations on interacting dynamics are imposed. The conclusion is unchanged: the public statement exports no equation of motion for the hierarchy's fields.

**Missing.** Any operator identity of the form `Σ_l φ_l(D_l g) ∈ (lower-order composite terms)` (a field equation or Schwinger–Dyson relation for the gauge-invariant labels), or any statement mentioning `dependenceDomain` or a Cauchy-surface relation. Even granting such an identity, time-slice for interacting theories is known only perturbatively (Chilian–Fredenhagen, CMP 287 (2009), for formal power series algebras), and it uses the field equation essentially.

## 4. (c) Modified nets

**(c1) Von Neumann closures plus Borchers.** Borchers' timelike tube theorem (Nuovo Cimento 19 (1961); generalised by Araki 1963 and Strohmaier–Witten 2023) says that the weak closure of fields smeared in a thin timelike tube around a segment equals the closure of the fields in the double cone of that segment. The thin direction there is spacelike. Time-slice needs the thin direction to be timelike, and edge-of-the-wedge / analytic continuation does not give that: the vN version of time-slice fails for the GFF (Landau; Garber). So the theorem is the wrong tool. Even setting up the vN net would need:

- closures of the `φ(f)` with self-adjoint closures (Wightman fields need not be essentially self-adjoint on `D`);
- the spectral theorem for unbounded self-adjoint operators;
- passage from commutativity on `D` to commuting spectral projections, which fails in general (Nelson's example). It needs extra hypotheses such as Borchers–Zimmermann analytic vectors or Driessler–Summers–Wichmann (CMP 105, 1986) energy bounds, just to keep Einstein causality.

As far as I know, Mathlib has `LinearPMap` closures but no spectral theorem for unbounded operators, no affiliated-operator theory, and no edge-of-the-wedge or several-complex-variables tube theory. Out of reach.

**(c2) Fields with time-slice tests plus a field equation.** Statement level: add the hypothesis `∀ g, φ((□+m²)g) = 0` on `D` (or a family of hyperbolic equations). Then show that for `tsupport f ⊆ O₂ ⊆ D(O₁)` there is `g ∈ C_c^∞` with `tsupport (f − (□+m²)g) ⊆ O₁`, via `g = χ·E^adv f + (1−χ)·E^ret f`-type cutoffs. This needs retarded and advanced fundamental solutions of the Klein–Gordon operator with support in `J^±`, plus their smoothness on test functions. None of that is in Mathlib. More importantly, the YM hierarchy provides no such equation for its labels (section 3), so (c2) would only cover free or free-like theories, and the GFF shows (c2) cannot be stated without the extra hypothesis.

**Recommendation.** Keep `Timeslice` unclaimed, as `Main.lean` already does, and record the GFF counterexample as the reason it is not a theorem about polynomial nets of Wightman theories.
