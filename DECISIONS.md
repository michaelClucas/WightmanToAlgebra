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
