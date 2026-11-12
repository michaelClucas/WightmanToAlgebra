# Blockers

## B1: Timeslice (FR A5) is not provable for the polynomial net (Phase 6.2)

It is false for polynomial nets of general W0–W3 theories: generalized free fields with a
continuous Källén–Lehmann measure are Wightman theories for which a smeared field supported
outside a time slice is not in the polynomial algebra of the slice. The upstream Yang–Mills
hierarchy exports no field equation or other dynamical relation that would supply it, and the
von Neumann routes need unbounded spectral theory not in Mathlib. Full analysis and
counterexample sketch: `TIMESLICE.md`. `Timeslice` stays unclaimed in `Main.lean`.

## B2: the Wightman GNS space is `closure(A(M)Ω)`; equality with `H` not proved (Phase 6.1)

`wightmanGNS` lives on `K = closure(A(M)Ω) ⊆ H`, where `A(M)` is the union of the local
polynomial algebras (tests with compact support in some region). `gnsRepresentation_equivalent_wightmanGNS`
shows every GNS representation of the vacuum state is unitarily equivalent to the Wightman
fields acting on `A(M)Ω ⊆ D`. Showing `K = H` needs density of compactly supported word
vectors in `H`. Upstream W1 gives cyclicity for words with arbitrary Schwartz tests and
continuity of `f ↦ φ(f)ψ` for each fixed `ψ` (separate continuity only). Approximating all
tests of a word at once needs joint continuity of the Wightman functions (Banach–Steinhaus
for separately continuous multilinear maps on the Fréchet space of Schwartz functions,
with Schwartz-space completeness and the barrelled-space machinery in Mathlib wired to
`SchwartzMap`). Not attempted further in this run.

## B3: no nontrivial instance of `BoundedLocalData` (Phase 6.3, PI review F2)

`bounded_haagKastler` and `boundedAlgebra_weakCommute_field` are conditional on
`BoundedLocalData`. The repo never constructs one for a nontrivial theory (not even the free
field). The intended instance takes `S(O)` = spectral projections of the self-adjoint
closures of hermitian smeared fields; building it needs closures of unbounded operators, the
spectral theorem for unbounded self-adjoint operators, and a strong-locality hypothesis
(commutation on `D` does not imply commuting spectral projections; Nelson's example). None
of this is in Mathlib.
