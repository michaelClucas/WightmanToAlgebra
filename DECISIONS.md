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
None of `HaagKastler.lean`, `Regions.lean` or `Main.lean` changed.
