# Decisions

Each entry: date, decision, reason. Statement changes also quote Fewster–Rejzner
(arXiv:1904.04051), give old and new Lean text, and record fidelity sign-off.

## D1 (2026-11-11): toolchain and caches live inside the repo directory

The run is restricted to this directory, so `ELAN_HOME=.elan`, `XDG_CACHE_HOME=.cache`,
`MATHLIB_CACHE_DIR=.cache/mathlib`, scratch files in `.scratch/`. All are gitignored.

## D2 (2026-11-11): Phase 0 compile fixes in `PolynomialNet.lean` (no change of meaning)

- `localGenerators`: `∃ l f, tsupport (f : Spacetime → ℂ) ⊆ A ∧ X = F.field l f` failed to
  elaborate because the ascription made `f : Spacetime → ℂ`. Now binder types are explicit:
  `∃ (l : Labels.carrier) (f : TestFunction), ...`. Same set.
- `polynomialNet.incl`: the `StarAlgHom` type needs the `Star` instances on `P(O₁)`, `P(O₂)`;
  they are now provided with `letI := polyStarRing ...`, which is the same instance the net's
  `starRing` field uses.
- `polyStar`, `polyStarRing` marked `@[reducible]` (Lean 4.32 requires it for defs of class
  type); `polyStarModule` is a `Prop`, so `def` became `theorem`.
None of `HaagKastler.lean`, `Regions.lean` or `Main.lean` changed in Phase 0 (later phases only fill proofs there, plus D3).

## D3 (2026-11-11): strengthen `yangMills_haagKastler` (issue #10)

Fewster–Rejzner, Sec. 4.1, A1: "There is a unital *-algebra A(M) and, to each open causally
convex bounded region O ⊂ M, a subalgebra A(O) containing the unit of A(M) ...". The claim is
that *the Yang–Mills Wightman theory* yields such a net.

Reason: the scaffold statement was satisfiable without the hypothesis. Its conclusion
`∃ T : Hierarchy C, ∃ N : Net, ∃ α : N.Covariance, N.Isotony ∧ N.EinsteinCausality ∧ N.Covariant α`
does not relate `N` to `T`, so the constant net `Alg O := ℂ` proves it.

Old:
```lean
theorem yangMills_haagKastler (hYM : JointExistence) :
    ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, ∃ N : Net, ∃ α : N.Covariance,
          N.Isotony ∧ N.EinsteinCausality ∧ N.Covariant α
```
New:
```lean
theorem yangMills_haagKastler (hYM : JointExistence) :
    ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧
          ∃ hax : T.theory.Axioms,
            (polynomialNet T.theory hax).Isotony ∧
            (polynomialNet T.theory hax).EinsteinCausality ∧
            (polynomialNet T.theory hax).Covariant (polynomialCovariance T.theory hax)
```
The new statement implies the old one.

Fidelity sign-off: independent agent (saw only FR text, upstream spec, net definitions and the
diff): **APPROVE**. Its caveat: the `Covariant` clause is meaningful only if
`polynomialCovariance` is implemented as conjugation by `U(g) = onStates (coordinates.symm g)`.
This is checked when the covariance branch is merged and again in the Phase 5 audit.

## D4 (2026-11-11): Phase 6 statement design (new files only; existing statements untouched)

- `Vacuum.lean`: a state on the quasi-local algebra is a compatible family of normalized
  positive functionals (`Net.State`); FR's `A(M)` is the colimit over the directed set of
  regions, so this is equivalent. GNS representation follows FR Thm 10 (`D = π(A)Ω` dense,
  `ω(a) = ⟨Ω, π(a)Ω⟩`, `π(a*)` formal adjoint of `π(a)` on `D`). Spectrum condition (FR
  Def. 24) is stated through vector-state spectral measures: for every `ψ`,
  `x ↦ ⟨ψ, U(x)ψ⟩` is `charFun` of a finite measure vanishing off the closed forward cone.
  Fourier convention follows upstream W0 (Euclidean pairing); the two conventions differ by
  `p ↦ (p⁰, -p⃗)`, which preserves `V₊`, so the support condition is the same. Vacuum (FR
  Def. 25) adds uniqueness of invariant vectors; Poincaré (not only translation) invariance
  is required, as Phase 6 asks.
- `WightmanVacuum.lean`: `wightmanVacuum` pinned by `wightmanVacuum_apply`
  (`ω(X) = ⟨Ω, XΩ⟩`), `wightmanGNS` pinned by `wightmanGNS_spec` (isometric embedding of
  its domain into the Wightman domain intertwining with the field polynomials).
- `BoundedNet.lean`: `M(O) = S(O)''` with explicit hypotheses `BoundedLocalData`
  (adjoint-closed, monotone, spacelike commuting, covariant under `U(g)`, and fields
  localised in `O` affiliated with `S(O)''` on the domain, which excludes `S = ∅`).
- Work happens on branch `phase6`; `main` stays sorry-free until each piece is proved.

## D5 (2026-11-11): Phase 6 fidelity review; `BoundedLocalData.affiliated` strengthened

Independent fidelity agent (saw FR, upstream spec and the new statement files only):
`Vacuum.lean` and `WightmanVacuum.lean` faithful. `BoundedNet.lean`: REJECT on one item. The
original `affiliated` field only constrained commutant elements `B` preserving the Wightman
domain `D`; elements of `S(O)'` typically do not preserve `D`, so the field could hold
vacuously and `S(O)` would not be tied to the fields.

Old:
```lean
  affiliated (O) (l) (f) (hf : tsupport f ⊆ O.carrier) (B : H.Operator)
      (hB : ∀ A ∈ S O, Commute A B)
      (hD : Set.MapsTo B (T.fields.domain : Set H.carrier) T.fields.domain)
      (u : T.fields.domain) :
    B (T.fields.field l f u).1 = (T.fields.field l f ⟨B u.1, hD u.2⟩).1
```
New (reviewer's proposal, `B φ ⊆ (φ†)* B`, no domain invariance needed):
```lean
  affiliated (O) (l) (f) (hf : tsupport f ⊆ O.carrier) (B : H.Operator)
      (hB : ∀ A ∈ S O, Commute A B) (u v : T.fields.domain) :
    inner ℂ (T.fields.field (T.adjointLabel l) (conjugateTest f) v).1 (B u.1) =
      inner ℂ v.1 (B (T.fields.field l f u).1)
```
Re-review of the fix requested (see D6).

## D6 (2026-11-11): fidelity re-review of D5: APPROVE

Second independent agent: the new `affiliated` is the weak form of `B φ ⊆ (φ†)* B` with slot
order matching W1's `AdjointAxiom`; non-vacuous (with `S(O)` empty or scalar, rank-one `B`
would force every field localised in `O` to act as a scalar); satisfiable in the intended
example under strong locality; consistent.

## D7 (2026-11-12, retroactive, PI review F6): definitions supplied as data

These were `sorry` in the statement files and their bodies determine what the theorems mean.
They should have had entries when they were filled in.

- `polynomialCovariance` (`PolynomialNet.lean`, filled in `93bf718`, merged `e5358e0`):
  `act g O X := domainConj g X`, i.e. `X ↦ V X V⁻¹` with
  `V = onStates (coordinates.symm g)` restricted to the Wightman domain (W2
  `domainInvariant`), inverse `onStates (coordinates.symm (poincareInv g))`. This is the
  construction the scaffold docstring specified and the D3 approval was conditioned on;
  checked independently in `AUDIT.md` and the PI review.
- `wightmanVacuum`, `wightmanGNS` (`WightmanVacuum.lean`): pinned by `wightmanVacuum_apply`
  (`ω(X) = ⟨Ω, XΩ⟩`) and `wightmanGNS_spec` (isometric embedding of the GNS domain into
  `D`, `Ω ↦ Ω`, intertwining the field polynomials).
- `boundedCovariance` (`BoundedNet.lean`): pinned by `boundedCovariance_apply`
  (`A ↦ U(g) A U(g)*`).

## D8 (2026-11-12, PI review F4): `Net.Timeslice` differs from FR A5; left unchanged

FR A5: "If O₁ ⊂ O₂ and O₁ contains a Cauchy surface of O₂ then A(O₂) = A(O₁)", where a
Cauchy surface of `O₂` is met exactly once by every inextendible timelike curve in `O₂`.
`HaagKastler.lean` states it with `O₂ ⊆ dependenceDomain O₁` (inextendible causal curves in
all of Minkowski space). The two hypotheses are not shown equivalent, and the earlier audit
called the difference harmless without proof. Decision: leave the definition as is, because
timeslice is not claimed by any theorem, and changing `HaagKastler.lean` needs a faithful
formalization of Cauchy surfaces of a region plus fidelity sign-off, which buys nothing while
timeslice stays unproved. The GFF counterexample in `TIMESLICE.md` uses a double cone `O₂`
and a slab `O₁ = O₂ ∩ {|t| < ε}`; `O₁` contains the Cauchy surface `O₂ ∩ {t = 0}` of `O₂`,
so the counterexample refutes both formulations.

## D9 (2026-11-12, PI review F2, F3): rename and new theorem in Phase 6 files

- `gns_recovers_wightman` renamed to `gnsRepresentation_equivalent_wightmanGNS`
  (statement unchanged). The old name suggested the full Wightman representation on `H` is
  recovered; only `closure(A(M)Ω)` is (BLOCKERS.md B2).
- New theorem `boundedAlgebra_weakCommute_field` (`BoundedNet.lean`): every element of
  `M(O₂)` satisfies `A φ ⊆ (φ†)* A` on `D` for fields localised in a region causally
  disjoint from `O₂`. It is the first result that uses `BoundedLocalData.affiliated`, and
  it is the statement that ties the von Neumann net to the Wightman fields.
  `bounded_haagKastler` itself is the generic double-commutant fact and does not use the
  fields (the PI review's F2); docs now say so. `hT` in `boundedCovariance` and
  `bounded_haagKastler` is unused; first left in place, then removed in D10.
- No instance of `BoundedLocalData` for a nontrivial theory is constructed (would need
  self-adjoint closures and spectral projections of unbounded operators). Recorded in
  `BLOCKERS.md` B3.

## D10 (2026-11-12, PI review round 2, N3): drop unused `hT` from the bounded net

Old: `boundedCovariance (T) (hT : T.Axioms) (B)`, and `boundedCovariance_apply`,
`bounded_haagKastler` with `(hT : T.Axioms)`. New: the binder is removed. The proofs never
used it (the linter flagged it), and its presence suggested the Wightman axioms enter the
bounded-net result when they do not. Removing an unused hypothesis only strengthens the
statements. Covariance is still `Ad U(g)` with `U(g) = onStates (coordinates.symm g)`.
